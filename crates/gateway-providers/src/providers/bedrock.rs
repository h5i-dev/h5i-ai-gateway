//! Amazon Bedrock: the Converse API for chat (`POST /model/{id}/converse`,
//! `/converse-stream` with AWS event-stream framing) and InvokeModel for
//! Amazon Titan and Cohere embeddings (`POST /model/{id}/invoke`).
//!
//! Configuration follows LiteLLM (`bedrock/...` model strings):
//!
//! * the model id may carry routing prefixes (`bedrock/converse/...`,
//!   `bedrock/invoke/...` — both use Converse here), a region path segment
//!   (`bedrock/us-west-2/<id>`), a cross-region inference profile prefix
//!   (`us.`, `eu.`, `apac.`, `global.`, ...) or be an ARN; `model_id`
//!   overrides the id sent in the URL;
//! * region: `aws_region_name`, the region path, the ARN's region,
//!   `AWS_REGION_NAME`, `AWS_REGION`, `AWS_DEFAULT_REGION`, else `us-west-2`;
//! * endpoint: `api_base`, `aws_bedrock_runtime_endpoint`,
//!   `AWS_BEDROCK_RUNTIME_ENDPOINT`, else
//!   `https://bedrock-runtime.{region}.amazonaws.com`;
//! * auth: a Bedrock API key (`api_key` / `AWS_BEARER_TOKEN_BEDROCK`, sent as
//!   `Authorization: Bearer`) or SigV4 with `aws_access_key_id` /
//!   `aws_secret_access_key` / `aws_session_token` (else the standard
//!   `AWS_*` variables). Explicit `litellm_params` win over the environment.
//!
//! Translation follows LiteLLM's `AmazonConverseConfig` and
//! `_bedrock_converse_messages_pt`: leading system messages become `system`
//! blocks (later ones become user text); consecutive same-role turns merge;
//! `tool_calls` <-> `toolUse`, `role: tool` -> `toolResult`; base64 images
//! and documents -> `bytes` sources, `s3://` URLs -> `s3Location` (the
//! gateway does not download `http(s)` URLs); `cache_control` -> `cachePoint`
//! blocks; `max_tokens`/`temperature`/`top_p`/`stop` -> `inferenceConfig`;
//! `top_k`, `thinking` and `reasoning_effort` -> `additionalModelRequestFields`
//! (Anthropic / Nova shapes); `response_format: json_schema` -> a forced
//! `json_tool_call` tool whose input is returned as content.

use std::collections::HashMap;
use std::time::SystemTime;

use serde_json::{Map, Value, json};

use super::{HttpRequest, StreamTranslator, gen_id, map_finish_reason, now_unix, parse_arguments, parse_data_url, parse_json};
use crate::auth::sigv4::{self, SignableRequest, SigningParams};
use crate::deployment::{Deployment, Secret, take_string};
use crate::error::ProviderError;
use crate::pricing::{self, Pricing};
use crate::sse::SseEvent;
use crate::tokens::text_tokens;
use crate::types::{
    ChatChunk, ChatMessage, ChatRequest, ChatResponse, Choice, ContentPart, Delta, Embedding, EmbeddingRequest, EmbeddingResponse, EmbeddingVector,
    FunctionCallDelta, JsonObject, MessageContent, PromptTokensDetails, ResponseFormat, Role, Tool, ToolCall, ToolCallDelta, ToolChoice, Usage,
    finish_reason, part_type,
};

const PROVIDER: &str = "bedrock";
/// SigV4 service name for the Bedrock runtime.
const SERVICE: &str = "bedrock";
const DEFAULT_REGION: &str = "us-west-2";
/// Cross-region inference profile prefixes (LiteLLM's list).
const CROSS_REGION_PREFIXES: &[&str] = &["global", "us", "eu", "apac", "jp", "au", "us-gov"];
/// LiteLLM routing prefixes that are not part of the Bedrock model id.
const ROUTE_PREFIXES: &[&str] = &["bedrock/", "converse/", "invoke/"];
/// Same as the Anthropic adapter (LiteLLM's `RESPONSE_FORMAT_TOOL_NAME`).
const JSON_TOOL_NAME: &str = "json_tool_call";
const PLACEHOLDER: &str = ".";
/// LiteLLM's `DEFAULT_MAX_TOKENS` used when thinking needs room.
const DEFAULT_MAX_TOKENS: u64 = 4096;
const THINKING_BUDGETS: &[(&str, u64)] = &[("low", 1024), ("medium", 2048), ("high", 4096)];
/// Bedrock `toolUseId` limit.
const TOOL_USE_ID_MAX: usize = 64;
/// Native Converse request fields forwarded from the request's extra fields.
const PASSTHROUGH_FIELDS: &[&str] =
    &["guardrailConfig", "performanceConfig", "requestMetadata", "promptVariables", "additionalModelResponseFieldPaths"];

/// Static AWS credentials for SigV4.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AwsCredentials {
    pub access_key_id: String,
    pub secret_access_key: Secret,
    pub session_token: Option<Secret>,
}

/// How Bedrock requests are authenticated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AwsAuth {
    /// A Bedrock API key, sent as `Authorization: Bearer`.
    Bearer(Secret),
    /// SigV4 request signing.
    SigV4(AwsCredentials),
}

/// Bedrock-specific deployment settings (the endpoint is
/// the deployment's `api_base`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BedrockConfig {
    pub region: String,
    pub auth: AwsAuth,
    /// The model id or ARN used in request URLs (unencoded).
    pub model_id: String,
}

fn is_region(s: &str) -> bool {
    // e.g. us-east-1, us-gov-west-1, eu-central-2, ap-southeast-3
    let parts: Vec<&str> = s.split('-').collect();
    parts.len() >= 3
        && parts.iter().all(|p| !p.is_empty())
        && parts[0].len() == 2
        && parts[0].bytes().all(|b| b.is_ascii_lowercase())
        && parts.last().is_some_and(|p| p.bytes().all(|b| b.is_ascii_digit()))
}

fn valid_region_name(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
}

/// Strip routing prefixes and a region path: `(region from path, model id)`.
pub(crate) fn normalize_model(model: &str) -> (Option<String>, String) {
    let mut m = model;
    for prefix in ROUTE_PREFIXES {
        if let Some(rest) = m.strip_prefix(prefix) {
            m = rest;
        }
    }
    if !m.starts_with("arn:")
        && let Some((first, rest)) = m.split_once('/')
        && is_region(first)
        && !rest.is_empty()
    {
        return (Some(first.to_owned()), rest.to_owned());
    }
    (None, m.to_owned())
}

/// The region field of an ARN (`arn:aws:bedrock:<region>:...`).
fn arn_region(model: &str) -> Option<String> {
    let region = model.strip_prefix("arn:")?.split(':').nth(2)?;
    valid_region_name(region).then(|| region.to_owned())
}

/// The model without ARN path, throughput suffix or cross-region prefix:
/// `us.anthropic.claude-3-5-sonnet-20241022-v2:0` ->
/// `anthropic.claude-3-5-sonnet-20241022-v2:0`.
pub(crate) fn base_model(model: &str) -> String {
    let m = if model.starts_with("arn:") { model.rsplit('/').next().unwrap_or(model) } else { model };
    // `anthropic.claude-...-v2:0:51k` (provisioned throughput) -> `...:0`.
    let m = match m.rsplit_once(':') {
        Some((head, tail)) if head.contains(':') && tail.ends_with('k') => head,
        _ => m,
    };
    match m.split_once('.') {
        Some((prefix, rest)) if CROSS_REGION_PREFIXES.contains(&prefix) => rest.to_owned(),
        _ => m.to_owned(),
    }
}

fn dns_suffix(region: &str) -> &'static str {
    if region.starts_with("cn-") { "amazonaws.com.cn" } else { "amazonaws.com" }
}

/// Parse the Bedrock-specific `litellm_params`. Returns `(model, api_base,
/// config)`; consumes the `aws_*` keys from `obj`.
pub(crate) fn parse_config(
    model: &str,
    obj: &mut JsonObject,
    env: &dyn Fn(&str) -> Option<String>,
    explicit_api_key: Option<String>,
    configured_base: Option<String>,
) -> Result<(String, String, BedrockConfig), ProviderError> {
    let cfg_err = |msg: String| ProviderError::config(PROVIDER, msg);
    let from_env = |names: &[&str]| names.iter().find_map(|n| env(n).filter(|v| !v.is_empty()));
    let (path_region, model) = normalize_model(model);
    if model.is_empty() {
        return Err(cfg_err("model name missing".into()));
    }

    for unsupported in ["aws_role_name", "aws_profile_name", "aws_web_identity_token", "aws_session_name", "aws_external_id"] {
        if obj.get(unsupported).is_some_and(|v| !v.is_null()) {
            return Err(cfg_err(format!(
                "{unsupported} is not supported; configure aws_access_key_id/aws_secret_access_key \
                 (optionally aws_session_token) or a Bedrock API key"
            )));
        }
    }
    obj.remove("aws_sts_endpoint");

    let model_id = take_string(obj, "model_id")?.unwrap_or_else(|| model.clone());
    let region = take_string(obj, "aws_region_name")?
        .or(path_region)
        .or_else(|| arn_region(&model_id))
        .or_else(|| from_env(&["AWS_REGION_NAME", "AWS_REGION", "AWS_DEFAULT_REGION"]))
        .unwrap_or_else(|| DEFAULT_REGION.to_owned());
    if !valid_region_name(&region) {
        return Err(cfg_err(format!("invalid AWS region '{region}'")));
    }
    let endpoint = configured_base
        .or(take_string(obj, "aws_bedrock_runtime_endpoint")?)
        .or_else(|| from_env(&["AWS_BEDROCK_RUNTIME_ENDPOINT"]))
        .unwrap_or_else(|| format!("https://bedrock-runtime.{region}.{}", dns_suffix(&region)));
    let endpoint = endpoint.trim_end_matches('/').to_owned();

    let access_key = take_string(obj, "aws_access_key_id")?;
    let secret_key = take_string(obj, "aws_secret_access_key")?;
    let session_token = take_string(obj, "aws_session_token")?;
    let keys = |id: String, secret: String, token: Option<String>| {
        AwsAuth::SigV4(AwsCredentials {
            access_key_id: id,
            secret_access_key: Secret::new(secret),
            session_token: token.filter(|t| !t.is_empty()).map(Secret::new),
        })
    };
    let auth = if let Some(key) = explicit_api_key.filter(|k| !k.is_empty()) {
        AwsAuth::Bearer(Secret::new(key))
    } else if let (Some(id), Some(secret)) = (access_key.clone(), secret_key.clone()) {
        keys(id, secret, session_token)
    } else if access_key.is_some() || secret_key.is_some() {
        return Err(cfg_err("aws_access_key_id and aws_secret_access_key must be set together".into()));
    } else if let Some(token) = from_env(&["AWS_BEARER_TOKEN_BEDROCK"]) {
        AwsAuth::Bearer(Secret::new(token))
    } else if let (Some(id), Some(secret)) = (from_env(&["AWS_ACCESS_KEY_ID"]), from_env(&["AWS_SECRET_ACCESS_KEY"])) {
        keys(id, secret, session_token.or_else(|| from_env(&["AWS_SESSION_TOKEN"])))
    } else {
        return Err(cfg_err(
            "no AWS credentials: set api_key / AWS_BEARER_TOKEN_BEDROCK, or \
             aws_access_key_id + aws_secret_access_key / AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY"
                .into(),
        ));
    };
    Ok((model, endpoint, BedrockConfig { region, auth, model_id }))
}

/// Pricing: `bedrock/<region>/<id>`, the id, then the base model.
pub(crate) fn pricing(dep: &Deployment) -> Option<Pricing> {
    let region = config(dep).map(|c| c.region.as_str()).unwrap_or_default();
    pricing::lookup_with_provider(PROVIDER, &format!("{region}/{}", dep.model))
        .filter(|_| !region.is_empty())
        .or_else(|| pricing::lookup_with_provider(PROVIDER, &dep.model))
        .or_else(|| pricing::lookup_with_provider(PROVIDER, &base_model(&dep.model)))
}

pub(crate) fn config(dep: &Deployment) -> Option<&BedrockConfig> {
    match &dep.cloud {
        Some(crate::deployment::CloudConfig::Bedrock(c)) => Some(c),
        _ => None,
    }
}

fn require_config(dep: &Deployment) -> Result<&BedrockConfig, ProviderError> {
    config(dep).ok_or_else(|| ProviderError::config(PROVIDER, "deployment has no Bedrock settings"))
}

/// Percent-encode a model id or ARN as one path segment.
fn encode_model_id(id: &str) -> String {
    super::encode_path_segment(id)
}

fn model_url(dep: &Deployment, cfg: &BedrockConfig, action: &str) -> String {
    format!("{}/model/{}/{action}", dep.api_base().trim_end_matches('/'), encode_model_id(&cfg.model_id))
}

fn with_auth(mut http: HttpRequest, cfg: &BedrockConfig) -> HttpRequest {
    if let AwsAuth::Bearer(token) = &cfg.auth {
        http = http.header("authorization", format!("Bearer {}", token.expose()));
    }
    http
}

/// SigV4 headers for a request about to be sent (no-op for API keys).
/// `headers` are the request's headers; `x-amz*` ones are signed along with
/// `content-type` and `host`, like botocore.
pub(crate) fn sign_headers(
    dep: &Deployment,
    url: &str,
    headers: &[(String, String)],
    body: &[u8],
    time: SystemTime,
) -> Result<Vec<(String, String)>, ProviderError> {
    let Some(cfg) = config(dep) else {
        return Ok(Vec::new());
    };
    let AwsAuth::SigV4(creds) = &cfg.auth else {
        return Ok(Vec::new());
    };
    let mut signed: Vec<(String, String)> = vec![("content-type".into(), "application/json".into())];
    signed.extend(
        headers
            .iter()
            .filter(|(n, _)| {
                let n = n.to_ascii_lowercase();
                n.starts_with("x-amz") && n != "x-amz-date" && n != "x-amz-security-token"
            })
            .cloned(),
    );
    let sig = sigv4::sign(
        SignableRequest { method: "POST", url, headers: &signed, body },
        SigningParams {
            access_key_id: &creds.access_key_id,
            secret_access_key: creds.secret_access_key.expose(),
            session_token: creds.session_token.as_ref().map(Secret::expose),
            region: &cfg.region,
            service: SERVICE,
            time,
            content_sha256_header: false,
        },
    )
    .map_err(|e| ProviderError::config(PROVIDER, e))?;
    Ok(sig.headers)
}

// ---------------------------------------------------------------------------
// Chat: OpenAI -> Converse
// ---------------------------------------------------------------------------

fn json_schema_of(format: Option<&ResponseFormat>) -> Option<Value> {
    let f = format?;
    if f.kind != "json_schema" {
        return None;
    }
    f.json_schema.as_ref()?.schema.clone()
}

/// Bedrock tool names must match `[a-zA-Z][a-zA-Z0-9_-]*` (LiteLLM's
/// `make_valid_bedrock_tool_name`).
pub(crate) fn valid_tool_name(name: &str) -> String {
    if name.is_empty() {
        return String::new();
    }
    let mut s = String::with_capacity(name.len() + 1);
    if !name.chars().next().is_some_and(|c| c.is_ascii_alphabetic()) {
        s.push('a');
    }
    s.extend(name.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' || c == '-' { c } else { '_' }));
    s
}

/// Rewritten tool name -> original, for the names [`valid_tool_name`]
/// changed.
fn tool_name_map(req: &ChatRequest) -> HashMap<String, String> {
    req.tools
        .iter()
        .flatten()
        .filter_map(|t| t.function.as_ref())
        .filter_map(|f| {
            let valid = valid_tool_name(&f.name);
            (valid != f.name).then(|| (valid, f.name.clone()))
        })
        .collect()
}

/// `toolUseId` must match `[a-zA-Z0-9_.:-]+` and be at most 64 characters;
/// rewritten ids get a hash suffix so distinct ids stay distinct.
pub(crate) fn sanitize_tool_use_id(id: &str) -> String {
    let s: String = id.chars().map(|c| if c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | ':' | '-') { c } else { '_' }).collect();
    if s == id && !s.is_empty() && s.len() <= TOOL_USE_ID_MAX {
        return s;
    }
    let hash = &sigv4::sha256_hex(id.as_bytes())[..8];
    let keep = TOOL_USE_ID_MAX - hash.len() - 1;
    format!("{}_{hash}", &s[..s.len().min(keep)])
}

fn cache_point() -> Value {
    json!({"cachePoint": {"type": "default"}})
}

fn has_cache_control(v: Option<&Value>) -> bool {
    v.is_some_and(|c| !c.is_null())
}

fn image_format(mime: &str) -> Option<&'static str> {
    Some(match mime {
        "image/png" => "png",
        "image/jpeg" | "image/jpg" => "jpeg",
        "image/gif" => "gif",
        "image/webp" => "webp",
        _ => return None,
    })
}

fn document_format(mime: &str) -> Option<&'static str> {
    Some(match mime {
        "application/pdf" => "pdf",
        "text/csv" => "csv",
        "application/msword" => "doc",
        "application/vnd.openxmlformats-officedocument.wordprocessingml.document" => "docx",
        "application/vnd.ms-excel" => "xls",
        "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet" => "xlsx",
        "text/html" => "html",
        "text/plain" => "txt",
        "text/markdown" => "md",
        _ => return None,
    })
}

fn video_format(mime: &str) -> Option<&'static str> {
    Some(match mime {
        "video/mp4" => "mp4",
        "video/quicktime" => "mov",
        "video/x-matroska" => "mkv",
        "video/webm" => "webm",
        "video/x-flv" => "flv",
        "video/mpeg" => "mpeg",
        "video/x-ms-wmv" => "wmv",
        "video/3gpp" => "three_gp",
        _ => return None,
    })
}

fn media_error(msg: impl Into<String>) -> ProviderError {
    ProviderError::bad_request(PROVIDER, msg)
}

/// An image / document / video block from a base64 source or an S3 URI.
fn media_block(url: &str, mime_override: Option<&str>) -> Result<Value, ProviderError> {
    let (mime, source) = if let Some((mime, data)) = parse_data_url(url) {
        (mime_override.unwrap_or(mime).to_owned(), json!({"bytes": data}))
    } else if url.starts_with("s3://") {
        let mime = mime_override.map_or_else(|| super::mime_from_url(url).to_owned(), str::to_owned);
        (mime, json!({"s3Location": {"uri": url}}))
    } else if url.starts_with("http://") || url.starts_with("https://") {
        return Err(media_error(
            "Bedrock needs inline media: send images/files as base64 data URLs or s3:// URIs \
             (the gateway does not download http(s) URLs)",
        ));
    } else {
        return Err(media_error("media must be a base64 data URL or an s3:// URI"));
    };
    if let Some(f) = image_format(&mime) {
        return Ok(json!({"image": {"format": f, "source": source}}));
    }
    if let Some(f) = video_format(&mime) {
        return Ok(json!({"video": {"format": f, "source": source}}));
    }
    if let Some(f) = document_format(&mime) {
        // Converse requires a document name; LiteLLM derives a stable one
        // from the content.
        let basis = source.to_string();
        let hash = &sigv4::sha256_hex(basis.as_bytes())[..16];
        return Ok(json!({"document": {
            "format": f, "name": format!("DocumentPDFmessages_{hash}_{f}"), "source": source
        }}));
    }
    Err(media_error(format!("unsupported media type '{mime}' for Bedrock")))
}

/// Translate one user/assistant content part; `None` for empty text.
fn content_block(p: &ContentPart, assistant: bool) -> Result<Option<Value>, ProviderError> {
    Ok(match p.kind.as_str() {
        part_type::TEXT => p.text.as_deref().filter(|t| if assistant { !t.trim().is_empty() } else { !t.is_empty() }).map(|t| json!({"text": t})),
        part_type::IMAGE_URL => {
            let img = p.image_url.as_ref().ok_or_else(|| media_error("image_url part without image_url"))?;
            Some(media_block(&img.url, img.format.as_deref())?)
        }
        part_type::FILE => {
            let f = p.file.as_ref().ok_or_else(|| media_error("file part without file"))?;
            let src = f.file_data.as_deref().or(f.file_id.as_deref()).ok_or_else(|| media_error("file part needs file_data or file_id"))?;
            let fmt = f.extra.get("format").and_then(Value::as_str);
            Some(media_block(src, fmt)?)
        }
        part_type::INPUT_AUDIO => {
            return Err(media_error("Bedrock Converse does not accept audio input"));
        }
        // Native Converse blocks (`{"type": "guardContent", ...}` etc.)
        // pass through without their `type`.
        other => {
            let mut raw = p.extra.clone();
            raw.remove("cache_control");
            if raw.is_empty() {
                return Err(media_error(format!("content part type '{other}' is not supported by Bedrock")));
            }
            Some(Value::Object(raw))
        }
    })
}

fn parts_to_blocks(content: &MessageContent, message_cache: Option<&Value>, assistant: bool) -> Result<Vec<Value>, ProviderError> {
    let mut out = Vec::new();
    match content {
        MessageContent::Text(s) => {
            if (assistant && !s.trim().is_empty()) || (!assistant && !s.is_empty()) {
                out.push(json!({"text": s}));
            }
            if has_cache_control(message_cache) {
                out.push(cache_point());
            }
        }
        MessageContent::Parts(parts) => {
            for p in parts {
                if let Some(b) = content_block(p, assistant)? {
                    out.push(b);
                }
                if has_cache_control(p.extra.get("cache_control")) {
                    out.push(cache_point());
                }
            }
        }
    }
    Ok(out)
}

fn legacy_function_id(name: &str) -> String {
    sanitize_tool_use_id(&format!("function_call_{name}"))
}

fn tool_result(m: &ChatMessage) -> Result<Vec<Value>, ProviderError> {
    let id = match (&m.tool_call_id, &m.name) {
        (Some(id), _) => sanitize_tool_use_id(id),
        (None, Some(name)) if m.role == Role::Function => legacy_function_id(name),
        _ => {
            return Err(ProviderError::bad_request(PROVIDER, "tool message without tool_call_id"));
        }
    };
    let content: Vec<Value> = match &m.content {
        None => Vec::new(),
        Some(MessageContent::Text(s)) => vec![json!({"text": s})],
        Some(MessageContent::Parts(parts)) => {
            let mut blocks = Vec::new();
            for p in parts {
                match p.kind.as_str() {
                    part_type::TEXT => {
                        blocks.push(json!({"text": p.text.as_deref().unwrap_or_default()}));
                    }
                    part_type::IMAGE_URL | part_type::FILE => {
                        if let Some(b) = content_block(p, false)? {
                            blocks.push(b);
                        }
                    }
                    _ => {}
                }
            }
            blocks
        }
    };
    let mut out = vec![json!({"toolResult": {"toolUseId": id, "content": content}})];
    let part_cache = match &m.content {
        Some(MessageContent::Parts(parts)) => parts.iter().any(|p| has_cache_control(p.extra.get("cache_control"))),
        _ => false,
    };
    if has_cache_control(m.extra.get("cache_control")) || part_cache {
        out.push(cache_point());
    }
    Ok(out)
}

/// Replay `thinking_blocks` as `reasoningContent`.
fn reasoning_blocks(m: &ChatMessage) -> Vec<Value> {
    let Some(Value::Array(blocks)) = m.extra.get("thinking_blocks") else {
        return Vec::new();
    };
    blocks
        .iter()
        .filter_map(|b| match b["type"].as_str() {
            Some("thinking") => {
                let mut text = json!({"text": b["thinking"].as_str().unwrap_or_default()});
                if let Some(sig) = b["signature"].as_str() {
                    text["signature"] = json!(sig);
                }
                Some(json!({"reasoningContent": {"reasoningText": text}}))
            }
            Some("redacted_thinking") => b["data"].as_str().map(|d| json!({"reasoningContent": {"redactedContent": d}})),
            _ => None,
        })
        .collect()
}

fn assistant_blocks(m: &ChatMessage) -> Result<Vec<Value>, ProviderError> {
    let mut out = reasoning_blocks(m);
    if let Some(c) = &m.content {
        out.extend(parts_to_blocks(c, m.extra.get("cache_control"), true)?);
    }
    let tool_use = |id: String, name: &str, args: &str| -> Result<Value, ProviderError> {
        let input = match parse_arguments(PROVIDER, args)? {
            obj @ Value::Object(_) => obj,
            // Bedrock requires an object.
            _ => json!({}),
        };
        Ok(json!({"toolUse": {"toolUseId": id, "name": valid_tool_name(name), "input": input}}))
    };
    for call in m.tool_calls.iter().flatten() {
        out.push(tool_use(sanitize_tool_use_id(&call.id), &call.function.name, &call.function.arguments)?);
        if has_cache_control(call.extra.get("cache_control")) {
            out.push(cache_point());
        }
    }
    if let Some(call) = &m.function_call {
        out.push(tool_use(legacy_function_id(&call.name), &call.name, &call.arguments)?);
    }
    Ok(out)
}

/// Returns `(system blocks, messages)`.
fn translate_messages(msgs: &[ChatMessage]) -> Result<(Vec<Value>, Vec<Value>), ProviderError> {
    let is_system = |m: &ChatMessage| matches!(m.role, Role::System | Role::Developer);
    let leading = msgs.iter().take_while(|m| is_system(m)).count();
    let mut system = Vec::new();
    for m in &msgs[..leading] {
        if let Some(c) = &m.content {
            for block in parts_to_blocks(c, m.extra.get("cache_control"), false)? {
                // Only text and cache points are valid system blocks.
                if block.get("text").is_some() || block.get("cachePoint").is_some() {
                    system.push(block);
                }
            }
        }
    }

    let mut turns: Vec<(&'static str, Vec<Value>)> = Vec::new();
    let mut push = |role: &'static str, blocks: Vec<Value>| {
        if blocks.is_empty() {
            return;
        }
        match turns.last_mut() {
            Some((r, existing)) if *r == role => existing.extend(blocks),
            _ => turns.push((role, blocks)),
        }
    };
    for m in &msgs[leading..] {
        match m.role {
            // Later system messages become user text (LiteLLM).
            Role::System | Role::Developer | Role::User => {
                if let Some(c) = &m.content {
                    push("user", parts_to_blocks(c, m.extra.get("cache_control"), false)?);
                }
            }
            Role::Tool | Role::Function => push("user", tool_result(m)?),
            Role::Assistant => push("assistant", assistant_blocks(m)?),
        }
    }

    if turns.first().is_none_or(|(role, _)| *role != "user") {
        turns.insert(0, ("user", vec![json!({"text": PLACEHOLDER})]));
    }
    // The final assistant turn (a prefill) cannot end with whitespace.
    if let Some((role, blocks)) = turns.last_mut()
        && *role == "assistant"
    {
        if let Some(Value::Object(last)) = blocks.last_mut()
            && let Some(Value::String(text)) = last.get_mut("text")
        {
            text.truncate(text.trim_end().len());
            if text.is_empty() {
                blocks.pop();
            }
        }
        if blocks.is_empty() {
            turns.pop();
        }
    }
    let messages = turns
        .into_iter()
        .map(|(role, mut content)| {
            if role == "user" {
                // Tool results first, keeping each one's cache point after it.
                let mut results = Vec::new();
                let mut rest = Vec::new();
                let mut last_was_result = false;
                for b in content.drain(..) {
                    let is_result = b.get("toolResult").is_some();
                    let is_cache = b.get("cachePoint").is_some();
                    if is_result || (is_cache && last_was_result) {
                        results.push(b);
                    } else {
                        rest.push(b);
                    }
                    last_was_result = is_result || (is_cache && last_was_result);
                }
                results.extend(rest);
                content = results;
            }
            json!({"role": role, "content": content})
        })
        .collect();
    Ok((system, messages))
}

fn translate_tool(tool: &Tool) -> Vec<Value> {
    let Some(f) = &tool.function else {
        // Pre-formatted Bedrock tool blocks pass through; other built-in
        // tool types have no Converse equivalent and are dropped.
        return ["toolSpec", "systemTool", "cachePoint"]
            .iter()
            .find(|k| tool.extra.contains_key(**k))
            .map(|_| vec![Value::Object(tool.extra.clone())])
            .unwrap_or_default();
    };
    let mut schema = f.parameters.clone().unwrap_or_else(|| json!({"type": "object", "properties": {}}));
    if let Value::Object(s) = &mut schema {
        const ROOT_TYPES: &[&str] = &["array", "boolean", "integer", "null", "number", "object", "string"];
        let ok = s.get("type").and_then(Value::as_str).is_some_and(|t| ROOT_TYPES.contains(&t));
        if !ok {
            s.insert("type".into(), json!("object"));
        }
    }
    let name = valid_tool_name(&f.name);
    let description = f.description.clone().filter(|d| !d.is_empty()).unwrap_or_else(|| name.clone());
    let mut out = vec![json!({"toolSpec": {
        "name": name, "description": description, "inputSchema": {"json": schema}
    }})];
    if has_cache_control(tool.extra.get("cache_control")) {
        out.push(cache_point());
    }
    out
}

fn translate_tool_choice(choice: &ToolChoice) -> Result<Option<Value>, ProviderError> {
    let mode = |m: &str| -> Result<Option<Value>, ProviderError> {
        match m {
            "auto" => Ok(Some(json!({"auto": {}}))),
            "required" | "any" => Ok(Some(json!({"any": {}}))),
            "none" => Err(ProviderError::bad_request(PROVIDER, "Bedrock doesn't support tool_choice=none; omit the tools instead")),
            other => Err(ProviderError::bad_request(PROVIDER, format!("unsupported tool_choice '{other}'"))),
        }
    };
    match choice {
        ToolChoice::Mode(m) => mode(m),
        ToolChoice::Named(n) => match &n.function {
            Some(f) => Ok(Some(json!({"tool": {"name": valid_tool_name(&f.name)}}))),
            None => mode(&n.kind),
        },
    }
}

/// Build the Converse request body.
pub(crate) fn converse_body(dep: &Deployment, req: &ChatRequest) -> Result<Value, ProviderError> {
    let base = base_model(&dep.model);
    let is_anthropic = base.starts_with("anthropic.");
    let is_nova = base.starts_with("amazon.nova");
    let (system, messages) = translate_messages(&req.messages)?;

    let mut body = Map::new();
    body.insert("messages".into(), Value::Array(messages));
    if !system.is_empty() {
        body.insert("system".into(), Value::Array(system));
    }

    let mut additional = match req.extra.get("additionalModelRequestFields") {
        Some(Value::Object(o)) => o.clone(),
        _ => Map::new(),
    };
    let mut inference = Map::new();
    let explicit_max = req.max_output_tokens();
    if let Some(n) = explicit_max {
        inference.insert("maxTokens".into(), json!(n));
    }
    if let Some(t) = req.temperature {
        inference.insert("temperature".into(), json!(t));
    }
    if let Some(p) = req.top_p {
        inference.insert("topP".into(), json!(p));
    }
    if let Some(stop) = &req.stop {
        let stops: Vec<String> = stop.to_vec().into_iter().filter(|s| !s.is_empty()).collect();
        if !stops.is_empty() {
            inference.insert("stopSequences".into(), json!(stops));
        }
    }
    if let Some(k) = req.extra.get("top_k").or_else(|| req.extra.get("topK")) {
        if is_anthropic {
            additional.insert("top_k".into(), k.clone());
        } else if is_nova {
            additional.insert("inferenceConfig".into(), json!({"topK": k}));
        }
    }

    // Extended thinking (Anthropic): explicit `thinking` or `reasoning_effort`.
    if let Some(t) = req.extra.get("thinking").filter(|t| !t.is_null()) {
        additional.insert("thinking".into(), t.clone());
    } else if let Some(effort) = req.reasoning_effort.as_deref() {
        if is_anthropic {
            if let Some(&(_, budget)) = THINKING_BUDGETS.iter().find(|(e, _)| *e == effort) {
                additional.insert("thinking".into(), json!({"type": "enabled", "budget_tokens": budget}));
            }
        } else {
            additional.insert("reasoning_effort".into(), json!(effort));
        }
    }
    let thinking = additional.get("thinking").and_then(|t| t.get("type")).is_some_and(|t| t != "disabled");
    if thinking && explicit_max.is_none() {
        let budget = additional["thinking"]["budget_tokens"].as_u64().unwrap_or(0);
        inference.insert("maxTokens".into(), json!(budget + DEFAULT_MAX_TOKENS));
    }
    if !inference.is_empty() {
        body.insert("inferenceConfig".into(), Value::Object(inference));
    }

    let mut tools: Vec<Value> = req.tools.iter().flatten().flat_map(translate_tool).collect();
    let mut tool_choice = match (&req.tool_choice, tools.is_empty()) {
        (Some(c), false) => translate_tool_choice(c)?,
        _ => None,
    };
    if let Some(schema) = json_schema_of(req.response_format.as_ref()) {
        let mut input_schema = json!({"type": "object"});
        if let (Value::Object(target), Value::Object(src)) = (&mut input_schema, schema) {
            target.extend(src);
        }
        tools.push(json!({"toolSpec": {
            "name": JSON_TOOL_NAME,
            "description": "Respond with a JSON object.",
            "inputSchema": {"json": input_schema}
        }}));
        tool_choice = Some(json!({"tool": {"name": JSON_TOOL_NAME}}));
    }
    // Forced tool use is incompatible with extended thinking.
    if thinking && tool_choice.as_ref().is_some_and(|c| c.get("any").is_some() || c.get("tool").is_some()) {
        tool_choice = Some(json!({"auto": {}}));
    }
    if !tools.is_empty() {
        let mut config = json!({"tools": tools});
        if let Some(tc) = &tool_choice {
            config["toolChoice"] = tc.clone();
        }
        body.insert("toolConfig".into(), config);
        if is_anthropic && let Some(parallel) = req.parallel_tool_calls {
            let mut tc = json!({"disable_parallel_tool_use": !parallel});
            if tool_choice.is_none() {
                tc["type"] = json!("auto");
            }
            additional.insert("tool_choice".into(), tc);
        }
    }
    if !additional.is_empty() {
        body.insert("additionalModelRequestFields".into(), Value::Object(additional));
    }
    for key in PASSTHROUGH_FIELDS {
        if let Some(v) = req.extra.get(*key) {
            body.insert((*key).to_owned(), v.clone());
        }
    }
    if let Some(Value::String(tier)) = req.extra.get("service_tier") {
        body.insert("serviceTier".into(), json!({"type": tier}));
    }
    for (k, v) in &dep.extra_body {
        body.insert(k.clone(), v.clone());
    }
    Ok(Value::Object(body))
}

pub(crate) fn chat_request(dep: &Deployment, req: &ChatRequest, stream: bool) -> Result<HttpRequest, ProviderError> {
    let cfg = require_config(dep)?;
    let action = if stream { "converse-stream" } else { "converse" };
    let http = HttpRequest::new(model_url(dep, cfg, action), converse_body(dep, req)?);
    Ok(with_auth(http, cfg))
}

// ---------------------------------------------------------------------------
// Chat: Converse -> OpenAI
// ---------------------------------------------------------------------------

/// Converse usage (`inputTokens` excludes cache reads/writes; prompt tokens
/// include them, like LiteLLM).
pub(crate) fn usage_from(u: &Value) -> Usage {
    let get = |keys: &[&str]| keys.iter().find_map(|k| u.get(*k).and_then(Value::as_u64)).unwrap_or(0);
    let input = get(&["inputTokens"]);
    let output = get(&["outputTokens"]);
    let cache_read = get(&["cacheReadInputTokens", "cacheReadInputTokenCount"]);
    let cache_write = get(&["cacheWriteInputTokens", "cacheWriteInputTokenCount"]);
    let prompt = input + cache_read + cache_write;
    Usage {
        total_tokens: get(&["totalTokens"]).max(prompt + output),
        prompt_tokens_details: Some(PromptTokensDetails {
            cached_tokens: Some(cache_read),
            cache_creation_tokens: Some(cache_write),
            ..PromptTokensDetails::default()
        }),
        cache_creation_input_tokens: Some(cache_write),
        cache_read_input_tokens: Some(cache_read),
        ..Usage::new(prompt, output)
    }
}

fn finish_reason_for(stop_reason: Option<&str>, json_mode: bool) -> Option<String> {
    let reason = match stop_reason? {
        "guardrail_intervened" | "content_filtered" => finish_reason::CONTENT_FILTER,
        other => map_finish_reason(other),
    };
    Some(if json_mode && reason == finish_reason::TOOL_CALLS { finish_reason::STOP } else { reason }.to_owned())
}

pub(crate) fn parse_chat(dep: &Deployment, req: &ChatRequest, body: &str) -> Result<ChatResponse, ProviderError> {
    let json_mode = json_schema_of(req.response_format.as_ref()).is_some();
    let names = tool_name_map(req);
    let v: Value = parse_json(PROVIDER, body)?;
    let blocks = v["output"]["message"]["content"]
        .as_array()
        .ok_or_else(|| ProviderError::invalid_response(PROVIDER, "Converse response without output.message.content"))?;

    let mut text = String::new();
    let mut reasoning = String::new();
    let mut thinking_blocks = Vec::new();
    let mut tool_calls = Vec::new();
    let mut json_tool_used = false;
    for b in blocks {
        if let Some(t) = b.get("text").and_then(Value::as_str) {
            text.push_str(t);
        } else if let Some(tu) = b.get("toolUse") {
            let raw_name = tu["name"].as_str().unwrap_or_default();
            let input = serde_json::to_string(&tu["input"]).unwrap_or_else(|_| "{}".into());
            if json_mode && raw_name == JSON_TOOL_NAME {
                text.push_str(&input);
                json_tool_used = true;
                continue;
            }
            let name = names.get(raw_name).map_or(raw_name, String::as_str);
            tool_calls.push(ToolCall::function(tu["toolUseId"].as_str().unwrap_or_default(), name, input));
        } else if let Some(rc) = b.get("reasoningContent") {
            if let Some(rt) = rc.get("reasoningText") {
                let t = rt["text"].as_str().unwrap_or_default();
                reasoning.push_str(t);
                let mut tb = json!({"type": "thinking", "thinking": t});
                if let Some(sig) = rt["signature"].as_str() {
                    tb["signature"] = json!(sig);
                }
                thinking_blocks.push(tb);
            } else if let Some(data) = rc.get("redactedContent") {
                thinking_blocks.push(json!({"type": "redacted_thinking", "data": data}));
            }
        }
    }

    let mut message = ChatMessage::assistant(text);
    if !tool_calls.is_empty() {
        if message.text().is_empty() {
            message.content = None;
        }
        message.tool_calls = Some(tool_calls);
    }
    if !reasoning.is_empty() {
        message.reasoning_content = Some(reasoning);
    }
    if !thinking_blocks.is_empty() {
        message.extra.insert("thinking_blocks".into(), Value::Array(thinking_blocks));
    }
    let mut finish = finish_reason_for(v["stopReason"].as_str(), json_mode);
    if json_tool_used && message.tool_calls.is_none() {
        finish = Some(finish_reason::STOP.into());
    }
    let mut extra = JsonObject::new();
    if let Some(trace) = v.get("trace") {
        extra.insert("trace".into(), trace.clone());
    }
    if let Some(tier) = v["serviceTier"]["type"].as_str() {
        extra.insert("service_tier".into(), json!(tier));
    }
    Ok(ChatResponse {
        id: gen_id("chatcmpl-"),
        object: "chat.completion".into(),
        created: now_unix(),
        model: dep.model.clone(),
        choices: vec![Choice { index: 0, message, finish_reason: finish, logprobs: None, extra: JsonObject::new() }],
        usage: v.get("usage").map(usage_from),
        system_fingerprint: None,
        extra,
    })
}

enum Block {
    Tool { index: u32, has_args: bool },
    JsonTool,
}

/// ConverseStream events (`:event-type` + JSON payload) -> OpenAI chunks.
pub(crate) struct BedrockStream {
    json_mode: bool,
    names: HashMap<String, String>,
    id: String,
    model: String,
    created: u64,
    blocks: HashMap<u64, Block>,
    next_tool: u32,
    stopped: bool,
    done: bool,
}

impl BedrockStream {
    pub fn new(dep: &Deployment, req: &ChatRequest) -> Self {
        Self {
            json_mode: json_schema_of(req.response_format.as_ref()).is_some(),
            names: tool_name_map(req),
            id: gen_id("chatcmpl-"),
            model: dep.model.clone(),
            created: now_unix(),
            blocks: HashMap::new(),
            next_tool: 0,
            stopped: false,
            done: false,
        }
    }

    fn chunk(&self, delta: Delta, finish: Option<String>) -> ChatChunk {
        ChatChunk::new(self.id.clone(), self.model.clone(), self.created).with_delta(delta, finish)
    }

    fn content(&self, text: &str) -> Vec<ChatChunk> {
        if text.is_empty() {
            return Vec::new();
        }
        vec![self.chunk(Delta { content: Some(text.to_owned()), ..Delta::default() }, None)]
    }

    fn tool_delta(&self, delta: ToolCallDelta) -> ChatChunk {
        self.chunk(Delta { tool_calls: Some(vec![delta]), ..Delta::default() }, None)
    }

    fn args_delta(&self, index: u32, args: &str) -> ChatChunk {
        self.tool_delta(ToolCallDelta {
            index,
            function: Some(FunctionCallDelta { name: None, arguments: Some(args.to_owned()) }),
            ..ToolCallDelta::default()
        })
    }
}

impl StreamTranslator for BedrockStream {
    fn on_event(&mut self, event: SseEvent) -> Result<Vec<ChatChunk>, ProviderError> {
        let v: Value = if event.data.trim().is_empty() { Value::Null } else { parse_json(PROVIDER, &event.data)? };
        let index = v["contentBlockIndex"].as_u64().unwrap_or(0);
        Ok(match event.event.as_deref().unwrap_or_default() {
            "messageStart" => vec![self.chunk(Delta { role: Some(Role::Assistant), content: Some(String::new()), ..Delta::default() }, None)],
            "contentBlockStart" => {
                let Some(tu) = v["start"].get("toolUse") else {
                    return Ok(Vec::new());
                };
                let raw_name = tu["name"].as_str().unwrap_or_default();
                if self.json_mode && raw_name == JSON_TOOL_NAME {
                    self.blocks.insert(index, Block::JsonTool);
                    return Ok(Vec::new());
                }
                let name = self.names.get(raw_name).map_or(raw_name, String::as_str).to_owned();
                let tool_index = self.next_tool;
                self.next_tool += 1;
                self.blocks.insert(index, Block::Tool { index: tool_index, has_args: false });
                vec![self.tool_delta(ToolCallDelta {
                    index: tool_index,
                    id: tu["toolUseId"].as_str().map(str::to_owned),
                    kind: Some("function".into()),
                    function: Some(FunctionCallDelta { name: Some(name), arguments: Some(String::new()) }),
                })]
            }
            "contentBlockDelta" => {
                let delta = &v["delta"];
                if let Some(t) = delta.get("text").and_then(Value::as_str) {
                    return Ok(self.content(t));
                }
                if let Some(input) = delta["toolUse"]["input"].as_str() {
                    return Ok(match self.blocks.get_mut(&index) {
                        Some(Block::JsonTool) => self.content(input),
                        Some(Block::Tool { index, has_args }) => {
                            if input.is_empty() {
                                return Ok(Vec::new());
                            }
                            *has_args = true;
                            let i = *index;
                            vec![self.args_delta(i, input)]
                        }
                        None => Vec::new(),
                    });
                }
                if let Some(t) = delta["reasoningContent"]["text"].as_str()
                    && !t.is_empty()
                {
                    return Ok(vec![self.chunk(Delta { reasoning_content: Some(t.to_owned()), ..Delta::default() }, None)]);
                }
                // signatures, redacted reasoning, citations
                Vec::new()
            }
            "contentBlockStop" => match self.blocks.remove(&index) {
                Some(Block::Tool { index, has_args: false }) => vec![self.args_delta(index, "{}")],
                _ => Vec::new(),
            },
            "messageStop" => {
                self.stopped = true;
                match finish_reason_for(v["stopReason"].as_str(), self.json_mode) {
                    Some(f) => vec![self.chunk(Delta::default(), Some(f))],
                    None => Vec::new(),
                }
            }
            "metadata" => {
                self.done = true;
                match v.get("usage") {
                    Some(u) => vec![ChatChunk::new(self.id.clone(), self.model.clone(), self.created).with_usage(usage_from(u))],
                    None => Vec::new(),
                }
            }
            _ => Vec::new(),
        })
    }

    fn is_done(&self) -> bool {
        self.done
    }

    fn finish(&mut self) -> Result<Vec<ChatChunk>, ProviderError> {
        if self.stopped { Ok(Vec::new()) } else { Err(ProviderError::new(crate::ErrorKind::Connection, PROVIDER, "stream ended before messageStop")) }
    }
}

// ---------------------------------------------------------------------------
// Embeddings (InvokeModel)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EmbeddingFamily {
    /// Amazon Titan text embeddings: one input per call.
    Titan { v2: bool },
    /// Cohere Embed: a batch per call.
    Cohere,
}

fn embedding_family(model: &str) -> Option<EmbeddingFamily> {
    let base = base_model(model);
    if base.starts_with("amazon.titan-embed") {
        Some(EmbeddingFamily::Titan { v2: base.contains("-v2") })
    } else if base.starts_with("cohere.embed") {
        Some(EmbeddingFamily::Cohere)
    } else {
        None
    }
}

/// One InvokeModel request per Titan input, one for a Cohere batch.
pub(crate) fn embeddings_requests(dep: &Deployment, req: &EmbeddingRequest) -> Result<Vec<HttpRequest>, ProviderError> {
    let cfg = require_config(dep)?;
    let texts = req.input.texts().ok_or_else(|| ProviderError::bad_request(PROVIDER, "Bedrock embeddings require text input"))?;
    let family = embedding_family(&dep.model).ok_or_else(|| {
        ProviderError::bad_request(
            PROVIDER,
            format!(
                "embeddings are supported for Amazon Titan (amazon.titan-embed-*) and Cohere \
                 (cohere.embed-*) models, not '{}'",
                dep.model
            ),
        )
    })?;
    let url = model_url(dep, cfg, "invoke");
    let bodies: Vec<Value> = match family {
        EmbeddingFamily::Titan { v2 } => texts
            .iter()
            .map(|t| {
                let mut b = json!({"inputText": t});
                if v2 {
                    if let Some(d) = req.dimensions {
                        b["dimensions"] = json!(d);
                    }
                    if let Some(n) = req.extra.get("normalize") {
                        b["normalize"] = n.clone();
                    }
                }
                b
            })
            .collect(),
        EmbeddingFamily::Cohere => {
            let mut b = json!({
                "texts": texts,
                "input_type": req.extra.get("input_type").cloned().unwrap_or_else(|| json!("search_document")),
            });
            for key in ["truncate", "embedding_types"] {
                if let Some(v) = req.extra.get(key) {
                    b[key] = v.clone();
                }
            }
            if let Some(d) = req.dimensions {
                b["output_dimension"] = json!(d);
            }
            vec![b]
        }
    };
    Ok(bodies
        .into_iter()
        .map(|mut b| {
            for (k, v) in &dep.extra_body {
                b[k] = v.clone();
            }
            with_auth(HttpRequest::new(url.clone(), b), cfg)
        })
        .collect())
}

/// Parse the InvokeModel responses (in request order). `header_tokens` is
/// `X-Amzn-Bedrock-Input-Token-Count` of each response, if present.
pub(crate) fn parse_embeddings(
    dep: &Deployment,
    req: &EmbeddingRequest,
    responses: &[(String, Option<u64>)],
) -> Result<EmbeddingResponse, ProviderError> {
    let family = embedding_family(&dep.model);
    let floats = |v: &Value| -> Vec<f64> { v.as_array().map(|a| a.iter().filter_map(Value::as_f64).collect()).unwrap_or_default() };
    let mut data = Vec::new();
    let mut prompt_tokens = 0u64;
    let mut counted = true;
    for (body, header_tokens) in responses {
        let v: Value = parse_json(PROVIDER, body)?;
        match family {
            Some(EmbeddingFamily::Titan { .. }) => {
                let values = v["embeddingsByType"]
                    .get("float")
                    .or_else(|| v.get("embedding"))
                    .ok_or_else(|| ProviderError::invalid_response(PROVIDER, "Titan response without embedding"))?;
                data.push(floats(values));
                match v["inputTextTokenCount"].as_u64().or(*header_tokens) {
                    Some(n) => prompt_tokens += n,
                    None => counted = false,
                }
            }
            _ => {
                let list = match &v["embeddings"] {
                    Value::Object(by_type) => by_type.get("float").cloned().unwrap_or(Value::Null),
                    other => other.clone(),
                };
                let list = list.as_array().ok_or_else(|| ProviderError::invalid_response(PROVIDER, "Cohere response without embeddings"))?;
                data.extend(list.iter().map(floats));
                match header_tokens {
                    Some(n) => prompt_tokens += n,
                    None => counted = false,
                }
            }
        }
    }
    if !counted {
        prompt_tokens = req.input.texts().unwrap_or_default().iter().map(|t| text_tokens(t)).sum();
    }
    Ok(EmbeddingResponse {
        object: "list".into(),
        data: data
            .into_iter()
            .enumerate()
            .map(|(i, values)| Embedding { object: "embedding".into(), index: i as u32, embedding: EmbeddingVector::Float(values) })
            .collect(),
        model: dep.model.clone(),
        usage: Usage::new(prompt_tokens, 0),
        extra: JsonObject::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::deployment::CloudConfig;
    use crate::providers::translate_all;
    use std::time::{Duration, UNIX_EPOCH};

    fn env(name: &str) -> Option<String> {
        match name {
            "AWS_ACCESS_KEY_ID" => Some("AKIDENV".into()),
            "AWS_SECRET_ACCESS_KEY" => Some("envsecret".into()),
            "MY_SECRET" => Some("from-os-environ".into()),
            _ => None,
        }
    }

    fn parse(v: Value) -> Result<Deployment, ProviderError> {
        Deployment::from_litellm_params_with_env(&v, env)
    }

    fn dep() -> Deployment {
        parse(json!({
            "model": "bedrock/anthropic.claude-3-5-sonnet-20241022-v2:0",
            "aws_access_key_id": "AKID", "aws_secret_access_key": "secret",
            "aws_region_name": "us-east-1"
        }))
        .unwrap()
    }

    fn req(v: Value) -> ChatRequest {
        serde_json::from_value(v).unwrap()
    }

    fn body(v: Value) -> Value {
        converse_body(&dep(), &req(v)).unwrap()
    }

    #[test]
    fn model_strings() {
        for (raw, region, model) in [
            ("anthropic.claude-v2", None, "anthropic.claude-v2"),
            ("converse/us.anthropic.claude-3-haiku-20240307-v1:0", None, "us.anthropic.claude-3-haiku-20240307-v1:0"),
            ("invoke/anthropic.claude-v2", None, "anthropic.claude-v2"),
            ("us-west-2/meta.llama3-70b-instruct-v1:0", Some("us-west-2"), "meta.llama3-70b-instruct-v1:0"),
            ("us-gov-west-1/anthropic.claude-v2", Some("us-gov-west-1"), "anthropic.claude-v2"),
            (
                "arn:aws:bedrock:eu-west-1:123456789012:inference-profile/eu.anthropic.claude-3-haiku",
                None,
                "arn:aws:bedrock:eu-west-1:123456789012:inference-profile/eu.anthropic.claude-3-haiku",
            ),
        ] {
            let (r, m) = normalize_model(raw);
            assert_eq!((r.as_deref(), m.as_str()), (region, model), "{raw}");
        }
        assert_eq!(base_model("us.anthropic.claude-3-5-sonnet-20241022-v2:0"), "anthropic.claude-3-5-sonnet-20241022-v2:0");
        assert_eq!(base_model("global.anthropic.claude-sonnet-4-5-20250929-v1:0"), "anthropic.claude-sonnet-4-5-20250929-v1:0");
        assert_eq!(base_model("anthropic.claude-3-5-sonnet-20241022-v2:0:51k"), "anthropic.claude-3-5-sonnet-20241022-v2:0");
        assert_eq!(base_model("arn:aws:bedrock:us-east-1:1:inference-profile/us.amazon.nova-pro-v1:0"), "amazon.nova-pro-v1:0");
        assert_eq!(arn_region("arn:aws:bedrock:eu-west-1:1:x/y").as_deref(), Some("eu-west-1"));
        assert_eq!(arn_region("anthropic.claude"), None);
    }

    #[test]
    fn config_resolution() {
        let d = dep();
        assert_eq!(d.provider, crate::Provider::Bedrock);
        assert_eq!(d.model, "anthropic.claude-3-5-sonnet-20241022-v2:0");
        assert_eq!(d.api_base.as_deref(), Some("https://bedrock-runtime.us-east-1.amazonaws.com"));
        let cfg = config(&d).unwrap();
        assert_eq!(cfg.region, "us-east-1");
        assert!(matches!(&cfg.auth, AwsAuth::SigV4(c) if c.access_key_id == "AKID" && c.session_token.is_none()));
        assert!(!format!("{d:?}").contains("\"secret\""), "secret must be redacted");
        assert!(d.extra.is_empty(), "aws_* keys are consumed: {:?}", d.extra);

        // Env credentials, ARN region, os.environ/ session token.
        let d = parse(json!({
            "model": "bedrock/converse/arn:aws:bedrock:eu-west-1:1:inference-profile/eu.anthropic.claude-3-haiku-20240307-v1:0",
            "aws_session_token": "os.environ/MY_SECRET"
        }))
        .unwrap();
        let cfg = config(&d).unwrap();
        assert_eq!(cfg.region, "eu-west-1");
        assert!(matches!(&cfg.auth, AwsAuth::SigV4(c)
            if c.access_key_id == "AKIDENV"
                && c.session_token.as_ref().map(Secret::expose) == Some("from-os-environ")));

        // Bearer API key wins; endpoint override; model_id override.
        let d = parse(json!({
            "model": "bedrock/us.amazon.nova-pro-v1:0", "api_key": "bedrock-key",
            "aws_bedrock_runtime_endpoint": "https://vpce.example.com/",
            "model_id": "arn:aws:bedrock:us-east-1:1:provisioned-model/abc"
        }))
        .unwrap();
        let cfg = config(&d).unwrap();
        assert_eq!(cfg.auth, AwsAuth::Bearer(Secret::new("bedrock-key")));
        assert_eq!(d.api_base.as_deref(), Some("https://vpce.example.com"));
        assert_eq!(cfg.region, "us-east-1", "region of the model_id ARN");
        assert_eq!(d.model, "us.amazon.nova-pro-v1:0", "pricing still uses the model");
        let r = chat_request(&d, &req(json!({"model": "m", "messages": [{"role": "user", "content": "hi"}]})), true).unwrap();
        assert_eq!(r.url, "https://vpce.example.com/model/arn%3Aaws%3Abedrock%3Aus-east-1%3A1%3Aprovisioned-model%2Fabc/converse-stream");
        assert!(r.headers.contains(&("authorization".into(), "Bearer bedrock-key".into())));

        // Env bearer token and region from the region path / env.
        let d = Deployment::from_litellm_params_with_env(&json!({"model": "bedrock/ap-northeast-1/anthropic.claude-v2"}), |n| match n {
            "AWS_BEARER_TOKEN_BEDROCK" => Some("env-bearer".into()),
            "AWS_REGION" => Some("us-east-2".into()),
            _ => None,
        })
        .unwrap();
        let cfg = config(&d).unwrap();
        assert_eq!((cfg.region.as_str(), d.model.as_str()), ("ap-northeast-1", "anthropic.claude-v2"));
        assert_eq!(cfg.auth, AwsAuth::Bearer(Secret::new("env-bearer")));

        // Errors.
        let no_env = |p: Value| Deployment::from_litellm_params_with_env(&p, |_| None);
        assert!(no_env(json!({"model": "bedrock/anthropic.claude-v2"})).unwrap_err().message().contains("no AWS credentials"));
        assert!(no_env(json!({"model": "bedrock/x", "aws_access_key_id": "a"})).is_err());
        assert!(no_env(json!({"model": "bedrock/x", "api_key": "k", "aws_role_name": "r"})).is_err());
        assert!(no_env(json!({"model": "bedrock/x", "api_key": "k", "aws_region_name": "US_EAST"})).is_err());
        assert!(matches!(d.cloud, Some(CloudConfig::Bedrock(_))));
    }

    #[test]
    fn sigv4_headers_for_requests() {
        let d = parse(json!({
            "model": "bedrock/anthropic.claude-v2",
            "aws_access_key_id": "AKIDEXAMPLE",
            "aws_secret_access_key": "wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY",
            "aws_session_token": "session-token",
            "aws_region_name": "us-east-1",
        }))
        .unwrap();
        let h = sign_headers(
            &d,
            "https://bedrock-runtime.us-east-1.amazonaws.com/model/amazon.titan-text-express-v1/invoke",
            &[("x-unrelated".into(), "v".into())],
            br#"{"input":"hello"}"#,
            UNIX_EPOCH + Duration::from_secs(1_704_164_645),
        )
        .unwrap();
        // Same inputs as botocore's golden vector.
        assert!(
            h.iter().any(|(n, v)| n == "authorization" && v.ends_with("Signature=55c027ef47527d3ad63f1735f9d099efdbc99f296ff914bd94e727e24ec0e464"))
        );
        let bearer = parse(json!({"model": "bedrock/x", "api_key": "k"})).unwrap();
        assert!(sign_headers(&bearer, "https://h/", &[], b"", SystemTime::now()).unwrap().is_empty());
    }

    #[test]
    fn system_messages_and_inference_config() {
        let b = body(json!({"model": "x",
            "messages": [
                {"role": "system", "content": "be brief", "cache_control": {"type": "ephemeral"}},
                {"role": "developer", "content": [{"type": "text", "text": "and kind"}]},
                {"role": "user", "content": "hi"},
                {"role": "system", "content": "late system"},
                {"role": "assistant", "content": "hello  "}
            ],
            "max_tokens": 100, "temperature": 0.2, "top_p": 0.9, "stop": ["END", ""], "top_k": 5
        }));
        assert_eq!(b["system"], json!([{"text": "be brief"}, {"cachePoint": {"type": "default"}}, {"text": "and kind"}]));
        assert_eq!(
            b["messages"],
            json!([
                {"role": "user", "content": [{"text": "hi"}, {"text": "late system"}]},
                {"role": "assistant", "content": [{"text": "hello"}]}
            ])
        );
        assert_eq!(b["inferenceConfig"], json!({"maxTokens": 100, "temperature": 0.2, "topP": 0.9, "stopSequences": ["END"]}));
        assert_eq!(b["additionalModelRequestFields"], json!({"top_k": 5}));
        assert!(b.get("toolConfig").is_none());

        // Conversation starting with an assistant turn gets a user turn.
        let b = body(json!({"model": "x", "messages": [{"role": "assistant", "content": "hi"}, {"role": "user", "content": "yo"}]}));
        assert_eq!(b["messages"][0], json!({"role": "user", "content": [{"text": "."}]}));
        // Nova top_k shape.
        let nova = parse(json!({"model": "bedrock/us.amazon.nova-pro-v1:0", "api_key": "k"})).unwrap();
        let b = converse_body(&nova, &req(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}], "top_k": 3}))).unwrap();
        assert_eq!(b["additionalModelRequestFields"], json!({"inferenceConfig": {"topK": 3}}));
    }

    #[test]
    fn images_documents_and_media_errors() {
        let b = body(json!({"model": "x", "messages": [{"role": "user", "content": [
            {"type": "text", "text": "look"},
            {"type": "image_url", "image_url": {"url": "data:image/png;base64,iVBORw0KGgo="}},
            {"type": "image_url", "image_url": "s3://bucket/cat.jpg", "cache_control": {"type": "ephemeral"}},
            {"type": "file", "file": {"file_data": "data:application/pdf;base64,JVBERi0x"}}
        ]}]}));
        let content = b["messages"][0]["content"].as_array().unwrap();
        assert_eq!(content[1], json!({"image": {"format": "png", "source": {"bytes": "iVBORw0KGgo="}}}));
        assert_eq!(content[2], json!({"image": {"format": "jpeg", "source": {"s3Location": {"uri": "s3://bucket/cat.jpg"}}}}));
        assert_eq!(content[3], json!({"cachePoint": {"type": "default"}}));
        let doc = &content[4]["document"];
        assert_eq!(doc["format"], "pdf");
        assert_eq!(doc["source"], json!({"bytes": "JVBERi0x"}));
        assert!(doc["name"].as_str().unwrap().starts_with("DocumentPDFmessages_"));

        let err = converse_body(
            &dep(),
            &req(json!({"model": "x", "messages": [{"role": "user", "content": [
                {"type": "image_url", "image_url": {"url": "https://example.com/cat.png"}}
            ]}]})),
        )
        .unwrap_err();
        assert_eq!(err.kind(), crate::ErrorKind::BadRequest);
        assert!(
            converse_body(
                &dep(),
                &req(json!({"model": "x", "messages": [{"role": "user", "content": [
                    {"type": "input_audio", "input_audio": {"data": "AAAA", "format": "wav"}}
                ]}]}))
            )
            .is_err()
        );
        assert!(
            converse_body(
                &dep(),
                &req(json!({"model": "x", "messages": [{"role": "user", "content": [
                    {"type": "image_url", "image_url": {"url": "data:image/tiff;base64,AAAA"}}
                ]}]}))
            )
            .is_err()
        );
    }

    #[test]
    fn tools_tool_calls_and_results() {
        let b = body(json!({"model": "x",
            "messages": [
                {"role": "user", "content": "weather?"},
                {"role": "assistant", "content": null, "tool_calls": [
                    {"id": "call_1", "type": "function", "function": {"name": "get.weather", "arguments": "{\"city\":\"Paris\"}"}},
                    {"id": "call 2!", "type": "function", "function": {"name": "noargs", "arguments": ""}}
                ]},
                {"role": "tool", "tool_call_id": "call_1", "content": "sunny"},
                {"role": "tool", "tool_call_id": "call 2!", "content": [{"type": "text", "text": "done"}], "cache_control": {"type": "ephemeral"}},
                {"role": "user", "content": "thanks"}
            ],
            "tools": [
                {"type": "function", "function": {"name": "get.weather", "description": "Weather", "parameters": {"type": "object", "properties": {"city": {"type": "string"}}}}},
                {"type": "function", "function": {"name": "noargs"}, "cache_control": {"type": "ephemeral"}},
                {"type": "web_search_preview"}
            ],
            "tool_choice": {"type": "function", "function": {"name": "get.weather"}},
            "parallel_tool_calls": false
        }));
        assert_eq!(
            b["toolConfig"],
            json!({
                "tools": [
                    {"toolSpec": {"name": "get_weather", "description": "Weather", "inputSchema": {"json": {"type": "object", "properties": {"city": {"type": "string"}}}}}},
                    {"toolSpec": {"name": "noargs", "description": "noargs", "inputSchema": {"json": {"type": "object", "properties": {}}}}},
                    {"cachePoint": {"type": "default"}}
                ],
                "toolChoice": {"tool": {"name": "get_weather"}}
            })
        );
        assert_eq!(b["additionalModelRequestFields"], json!({"tool_choice": {"disable_parallel_tool_use": true}}));
        let id2 = sanitize_tool_use_id("call 2!");
        assert!(id2.starts_with("call_2__") && id2.len() <= 64);
        assert_eq!(
            b["messages"][1],
            json!({"role": "assistant", "content": [
                {"toolUse": {"toolUseId": "call_1", "name": "get_weather", "input": {"city": "Paris"}}},
                {"toolUse": {"toolUseId": id2, "name": "noargs", "input": {}}}
            ]})
        );
        assert_eq!(
            b["messages"][2],
            json!({"role": "user", "content": [
                {"toolResult": {"toolUseId": "call_1", "content": [{"text": "sunny"}]}},
                {"toolResult": {"toolUseId": id2, "content": [{"text": "done"}]}},
                {"cachePoint": {"type": "default"}},
                {"text": "thanks"}
            ]})
        );

        for (choice, expected) in [(json!("auto"), json!({"auto": {}})), (json!("required"), json!({"any": {}}))] {
            let b = body(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}],
                "tools": [{"type": "function", "function": {"name": "f"}}], "tool_choice": choice}));
            assert_eq!(b["toolConfig"]["toolChoice"], expected);
        }
        let err = converse_body(
            &dep(),
            &req(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}],
            "tools": [{"type": "function", "function": {"name": "f"}}], "tool_choice": "none"})),
        )
        .unwrap_err();
        assert_eq!(err.kind(), crate::ErrorKind::BadRequest);
        assert_eq!(valid_tool_name("1st tool"), "a1st_tool");
        assert_eq!(sanitize_tool_use_id(&"x".repeat(80)).len(), 64);
        assert_eq!(sanitize_tool_use_id("tooluse_abc-1.2:3"), "tooluse_abc-1.2:3");
    }

    #[test]
    fn thinking_reasoning_and_json_mode() {
        let b = body(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}],
            "reasoning_effort": "low", "tools": [{"type": "function", "function": {"name": "f"}}], "tool_choice": "required"}));
        assert_eq!(b["additionalModelRequestFields"]["thinking"], json!({"type": "enabled", "budget_tokens": 1024}));
        assert_eq!(b["inferenceConfig"]["maxTokens"], 1024 + DEFAULT_MAX_TOKENS);
        assert_eq!(b["toolConfig"]["toolChoice"], json!({"auto": {}}), "forced tool use dropped under thinking");

        // Replayed thinking blocks become reasoningContent first.
        let b = body(json!({"model": "x", "messages": [
            {"role": "user", "content": "hi"},
            {"role": "assistant", "content": "answer", "thinking_blocks": [
                {"type": "thinking", "thinking": "hmm", "signature": "sig"},
                {"type": "redacted_thinking", "data": "opaque"}
            ]},
            {"role": "user", "content": "more"}
        ]}));
        assert_eq!(
            b["messages"][1]["content"],
            json!([
                {"reasoningContent": {"reasoningText": {"text": "hmm", "signature": "sig"}}},
                {"reasoningContent": {"redactedContent": "opaque"}},
                {"text": "answer"}
            ])
        );

        let b = body(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}],
            "response_format": {"type": "json_schema", "json_schema": {"name": "r", "schema": {"type": "object", "properties": {"a": {"type": "integer"}}}}}}));
        assert_eq!(b["toolConfig"]["toolChoice"], json!({"tool": {"name": JSON_TOOL_NAME}}));
        assert_eq!(b["toolConfig"]["tools"][0]["toolSpec"]["inputSchema"]["json"]["properties"]["a"]["type"], "integer");

        // Non-Anthropic models get reasoning_effort passed through.
        let oss = parse(json!({"model": "bedrock/openai.gpt-oss-120b-1:0", "api_key": "k"})).unwrap();
        let b =
            converse_body(&oss, &req(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}], "reasoning_effort": "high"}))).unwrap();
        assert_eq!(b["additionalModelRequestFields"], json!({"reasoning_effort": "high"}));

        // Passthrough fields and extra_body.
        let mut d = dep();
        d.extra_body.insert("performanceConfig".into(), json!({"latency": "optimized"}));
        let b = converse_body(
            &d,
            &req(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}],
            "guardrailConfig": {"guardrailIdentifier": "g", "guardrailVersion": "1"}, "service_tier": "priority"})),
        )
        .unwrap();
        assert_eq!(b["guardrailConfig"]["guardrailIdentifier"], "g");
        assert_eq!(b["performanceConfig"], json!({"latency": "optimized"}));
        assert_eq!(b["serviceTier"], json!({"type": "priority"}));
    }

    #[test]
    fn parses_converse_responses() {
        let r = req(json!({"model": "x", "messages": [], "tools": [{"type": "function", "function": {"name": "get.weather"}}]}));
        let resp = parse_chat(
            &dep(),
            &r,
            &json!({
                "output": {"message": {"role": "assistant", "content": [
                    {"reasoningContent": {"reasoningText": {"text": "thinking...", "signature": "s1"}}},
                    {"text": "Let me check."},
                    {"toolUse": {"toolUseId": "tooluse_1", "name": "get_weather", "input": {"city": "Paris"}}}
                ]}},
                "stopReason": "tool_use",
                "usage": {"inputTokens": 10, "outputTokens": 5, "totalTokens": 27, "cacheReadInputTokens": 8, "cacheWriteInputTokens": 4},
                "metrics": {"latencyMs": 100}
            })
            .to_string(),
        )
        .unwrap();
        let c = &resp.choices[0];
        assert_eq!(c.finish_reason.as_deref(), Some("tool_calls"));
        assert_eq!(c.message.text(), "Let me check.");
        assert_eq!(c.message.reasoning_content.as_deref(), Some("thinking..."));
        assert_eq!(c.message.extra["thinking_blocks"][0]["signature"], "s1");
        let call = &c.message.tool_calls.as_ref().unwrap()[0];
        assert_eq!((call.id.as_str(), call.function.name.as_str()), ("tooluse_1", "get.weather"), "name mapped back");
        assert_eq!(serde_json::from_str::<Value>(&call.function.arguments).unwrap(), json!({"city": "Paris"}));
        let u = resp.usage.unwrap();
        assert_eq!((u.prompt_tokens, u.completion_tokens, u.total_tokens), (22, 5, 27));
        assert_eq!((u.cache_read_input_tokens, u.cache_creation_input_tokens), (Some(8), Some(4)));
        assert_eq!(resp.model, "anthropic.claude-3-5-sonnet-20241022-v2:0");

        for (stop, finish) in [
            ("end_turn", "stop"),
            ("max_tokens", "length"),
            ("stop_sequence", "stop"),
            ("guardrail_intervened", "content_filter"),
            ("content_filtered", "content_filter"),
        ] {
            let resp = parse_chat(
                &dep(),
                &r,
                &json!({"output": {"message": {"content": [{"text": "x"}]}}, "stopReason": stop, "usage": {"inputTokens": 1, "outputTokens": 1}})
                    .to_string(),
            )
            .unwrap();
            assert_eq!(resp.choices[0].finish_reason.as_deref(), Some(finish), "{stop}");
        }

        // JSON mode: the tool input is the content.
        let jr = req(
            json!({"model": "x", "messages": [], "response_format": {"type": "json_schema", "json_schema": {"name": "r", "schema": {"type": "object"}}}}),
        );
        let resp = parse_chat(
            &dep(),
            &jr,
            &json!({
                "output": {"message": {"content": [{"toolUse": {"toolUseId": "t", "name": JSON_TOOL_NAME, "input": {"a": 1}}}]}},
                "stopReason": "tool_use", "usage": {"inputTokens": 1, "outputTokens": 1}
            })
            .to_string(),
        )
        .unwrap();
        assert_eq!(resp.choices[0].message.text(), "{\"a\":1}");
        assert_eq!(resp.choices[0].finish_reason.as_deref(), Some("stop"));
        assert!(resp.choices[0].message.tool_calls.is_none());

        assert_eq!(parse_chat(&dep(), &r, "{}").unwrap_err().kind(), crate::ErrorKind::InvalidResponse);
    }

    fn ev(event: &str, data: Value) -> (String, String) {
        (event.to_owned(), data.to_string())
    }

    fn run(r: &ChatRequest, events: &[(String, String)]) -> Result<Vec<ChatChunk>, ProviderError> {
        let evs: Vec<(&str, &str)> = events.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
        translate_all(BedrockStream::new(&dep(), r), &evs)
    }

    #[test]
    fn stream_translation() {
        let r = req(json!({"model": "x", "messages": [], "tools": [{"type": "function", "function": {"name": "get.weather"}}]}));
        let chunks = run(
            &r,
            &[
                ev("messageStart", json!({"role": "assistant"})),
                ev("contentBlockDelta", json!({"contentBlockIndex": 0, "delta": {"reasoningContent": {"text": "hmm"}}})),
                ev("contentBlockDelta", json!({"contentBlockIndex": 0, "delta": {"reasoningContent": {"signature": "sig"}}})),
                ev("contentBlockStop", json!({"contentBlockIndex": 0})),
                ev("contentBlockDelta", json!({"contentBlockIndex": 1, "delta": {"text": "Hel"}, "p": "abc"})),
                ev("contentBlockDelta", json!({"contentBlockIndex": 1, "delta": {"text": "lo"}})),
                ev("contentBlockStop", json!({"contentBlockIndex": 1})),
                ev("contentBlockStart", json!({"contentBlockIndex": 2, "start": {"toolUse": {"toolUseId": "tu_1", "name": "get_weather"}}})),
                ev("contentBlockDelta", json!({"contentBlockIndex": 2, "delta": {"toolUse": {"input": "{\"city\":"}}})),
                ev("contentBlockDelta", json!({"contentBlockIndex": 2, "delta": {"toolUse": {"input": "\"Paris\"}"}}})),
                ev("contentBlockStop", json!({"contentBlockIndex": 2})),
                ev("contentBlockStart", json!({"contentBlockIndex": 3, "start": {"toolUse": {"toolUseId": "tu_2", "name": "get_weather"}}})),
                ev("contentBlockStop", json!({"contentBlockIndex": 3})),
                ev("messageStop", json!({"stopReason": "tool_use"})),
                ev("metadata", json!({"usage": {"inputTokens": 7, "outputTokens": 3, "totalTokens": 10}, "metrics": {"latencyMs": 5}})),
                ev("ignored-after-done", json!({})),
            ],
        )
        .unwrap();
        assert_eq!(chunks[0].choices[0].delta.role, Some(Role::Assistant));
        assert_eq!(chunks[1].choices[0].delta.reasoning_content.as_deref(), Some("hmm"));
        let text: String = chunks.iter().filter_map(|c| c.choices.first()?.delta.content.clone()).collect();
        assert_eq!(text, "Hello");
        let calls: Vec<&ToolCallDelta> = chunks.iter().filter_map(|c| c.choices.first()?.delta.tool_calls.as_ref()).flatten().collect();
        assert_eq!(calls[0].id.as_deref(), Some("tu_1"));
        assert_eq!(calls[0].function.as_ref().unwrap().name.as_deref(), Some("get.weather"));
        let args0: String = calls.iter().filter(|c| c.index == 0).filter_map(|c| c.function.as_ref()?.arguments.clone()).collect();
        assert_eq!(args0, "{\"city\":\"Paris\"}");
        let args1: String = calls.iter().filter(|c| c.index == 1).filter_map(|c| c.function.as_ref()?.arguments.clone()).collect();
        assert_eq!(args1, "{}", "argument-less call gets {{}}");
        let finish = chunks.iter().find_map(|c| c.choices.first()?.finish_reason.clone());
        assert_eq!(finish.as_deref(), Some("tool_calls"));
        let last = chunks.last().unwrap();
        assert!(last.is_usage_only());
        assert_eq!(last.usage.as_ref().unwrap().total_tokens, 10);
        assert!(chunks.iter().all(|c| c.id == chunks[0].id));
    }

    #[test]
    fn stream_json_mode_and_truncation() {
        let jr = req(
            json!({"model": "x", "messages": [], "response_format": {"type": "json_schema", "json_schema": {"name": "r", "schema": {"type": "object"}}}}),
        );
        let chunks = run(
            &jr,
            &[
                ev("messageStart", json!({"role": "assistant"})),
                ev("contentBlockStart", json!({"contentBlockIndex": 0, "start": {"toolUse": {"toolUseId": "t", "name": JSON_TOOL_NAME}}})),
                ev("contentBlockDelta", json!({"contentBlockIndex": 0, "delta": {"toolUse": {"input": "{\"a\":1}"}}})),
                ev("contentBlockStop", json!({"contentBlockIndex": 0})),
                ev("messageStop", json!({"stopReason": "tool_use"})),
            ],
        )
        .unwrap();
        let text: String = chunks.iter().filter_map(|c| c.choices.first()?.delta.content.clone()).collect();
        assert_eq!(text, "{\"a\":1}");
        assert!(chunks.iter().all(|c| { c.choices.first().is_none_or(|ch| ch.delta.tool_calls.is_none()) }));
        assert_eq!(chunks.last().unwrap().choices[0].finish_reason.as_deref(), Some("stop"));

        let err = run(&jr, &[ev("messageStart", json!({"role": "assistant"}))]).unwrap_err();
        assert_eq!(err.kind(), crate::ErrorKind::Connection);
    }

    #[test]
    fn embeddings_titan_and_cohere() {
        let titan = parse(json!({"model": "bedrock/amazon.titan-embed-text-v2:0", "api_key": "k", "aws_region_name": "us-east-1"})).unwrap();
        let er: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": ["a", "b"], "dimensions": 256, "normalize": true})).unwrap();
        let reqs = embeddings_requests(&titan, &er).unwrap();
        assert_eq!(reqs.len(), 2);
        assert_eq!(reqs[0].url, "https://bedrock-runtime.us-east-1.amazonaws.com/model/amazon.titan-embed-text-v2%3A0/invoke");
        assert_eq!(reqs[1].body, json!({"inputText": "b", "dimensions": 256, "normalize": true}));
        let resp = parse_embeddings(
            &titan,
            &er,
            &[
                (json!({"embedding": [0.1, 0.2], "inputTextTokenCount": 3}).to_string(), None),
                (json!({"embeddingsByType": {"float": [0.3]}, "embedding": [9.0], "inputTextTokenCount": 2}).to_string(), None),
            ],
        )
        .unwrap();
        assert_eq!(resp.data.len(), 2);
        assert_eq!(resp.data[1].embedding, EmbeddingVector::Float(vec![0.3]));
        assert_eq!(resp.data[1].index, 1);
        assert_eq!(resp.usage.prompt_tokens, 5);

        let v1 = parse(json!({"model": "bedrock/amazon.titan-embed-text-v1", "api_key": "k"})).unwrap();
        assert_eq!(embeddings_requests(&v1, &er).unwrap()[0].body, json!({"inputText": "a"}));

        let cohere = parse(json!({"model": "bedrock/cohere.embed-english-v3", "api_key": "k"})).unwrap();
        let er: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": ["a", "b"], "input_type": "search_query"})).unwrap();
        let reqs = embeddings_requests(&cohere, &er).unwrap();
        assert_eq!(reqs.len(), 1);
        assert_eq!(reqs[0].body, json!({"texts": ["a", "b"], "input_type": "search_query"}));
        let resp = parse_embeddings(&cohere, &er, &[(json!({"embeddings": [[1.0], [2.0]], "id": "x"}).to_string(), Some(4))]).unwrap();
        assert_eq!(resp.data.len(), 2);
        assert_eq!(resp.usage.prompt_tokens, 4);
        let resp = parse_embeddings(&cohere, &er, &[(json!({"embeddings": {"float": [[1.0], [2.0]]}}).to_string(), None)]).unwrap();
        assert_eq!(resp.data[1].embedding, EmbeddingVector::Float(vec![2.0]));
        assert!(resp.usage.prompt_tokens > 0, "estimated");

        let nova = parse(json!({"model": "bedrock/amazon.nova-pro-v1:0", "api_key": "k"})).unwrap();
        assert_eq!(embeddings_requests(&nova, &er).unwrap_err().kind(), crate::ErrorKind::BadRequest);
        let tokens: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": [1, 2]})).unwrap();
        assert!(embeddings_requests(&titan, &tokens).is_err());
    }

    #[test]
    fn pricing_lookup() {
        for model in [
            "bedrock/anthropic.claude-3-5-sonnet-20241022-v2:0",
            "bedrock/us.anthropic.claude-3-5-sonnet-20241022-v2:0",
            "bedrock/converse/us.amazon.nova-pro-v1:0",
            "bedrock/global.anthropic.claude-sonnet-4-5-20250929-v1:0",
            "bedrock/apac.anthropic.claude-3-5-sonnet-20241022-v2:0:51k",
            "bedrock/amazon.titan-embed-text-v2:0",
            "bedrock/cohere.embed-english-v3",
            "bedrock/arn:aws:bedrock:us-east-1:1:inference-profile/us.anthropic.claude-3-5-sonnet-20241022-v2:0",
        ] {
            let d = parse(json!({"model": model, "api_key": "k"})).unwrap();
            let p = d.pricing().unwrap_or_else(|| panic!("no price for {model}"));
            assert!(p.input_cost_per_token > 0.0, "{model}");
        }
        // Regional price entries win.
        let d = parse(json!({"model": "bedrock/ap-northeast-1/anthropic.claude-instant-v1", "api_key": "k"})).unwrap();
        let regional = d.pricing().unwrap();
        let global = parse(json!({"model": "bedrock/anthropic.claude-instant-v1", "api_key": "k"})).unwrap().pricing().unwrap();
        assert!(regional.input_cost_per_token > 0.0 && global.input_cost_per_token > 0.0);
        // Bare Bedrock ids infer the provider from the price table.
        let d = Deployment::from_litellm_params_with_env(&json!({"model": "anthropic.claude-3-5-sonnet-20241022-v2:0"}), env).unwrap();
        assert_eq!(d.provider, crate::Provider::Bedrock);
    }
}
