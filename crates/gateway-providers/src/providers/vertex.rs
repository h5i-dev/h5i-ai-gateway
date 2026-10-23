//! Google Vertex AI (`vertex_ai/...`): Gemini models
//! (`publishers/google/models/{m}:generateContent` /
//! `:streamGenerateContent?alt=sse`) reusing the Gemini translation,
//! Anthropic Claude models (`publishers/anthropic/models/{m}:rawPredict` /
//! `:streamRawPredict`, body without `model` and with
//! `anthropic_version: "vertex-2023-10-16"`) reusing the Anthropic
//! translation, and text embeddings (`:predict`). Numeric model names are
//! tuned-model endpoints (`endpoints/{id}`).
//!
//! Configuration follows LiteLLM:
//!
//! * `vertex_project` (alias `vertex_ai_project`, env `VERTEXAI_PROJECT`,
//!   else the credentials' project, else `GOOGLE_CLOUD_PROJECT`; on GCE the
//!   metadata server's project);
//! * `vertex_location` (alias `vertex_ai_location`, env `VERTEXAI_LOCATION` /
//!   `VERTEX_LOCATION`, default `us-central1`); `global` uses
//!   `aiplatform.googleapis.com`, multi-regions (`us`, `eu`) use
//!   `aiplatform.{geo}.rep.googleapis.com`;
//! * credentials: `api_key` (an access token), `vertex_credentials` (path,
//!   JSON string or object), `VERTEXAI_CREDENTIALS`,
//!   `GOOGLE_APPLICATION_CREDENTIALS`, the gcloud ADC file, then the GCE
//!   metadata server (see [`crate::auth::gcp`]);
//! * `api_base`: an empty path or a bare `/v1` / `/v1beta1` gets the
//!   standard resource path grafted on; any other path is used as the
//!   endpoint and `:{method}` is appended.

use serde_json::{Map, Value, json};

use super::{HttpRequest, anthropic, gemini, parse_json};
use crate::auth::gcp::{DEFAULT_METADATA_HOST, GcpCredentials};
use crate::deployment::{CloudConfig, Deployment, Secret, take_string};
use crate::error::ProviderError;
use crate::types::{
    ChatRequest, Embedding, EmbeddingRequest, EmbeddingResponse, EmbeddingVector, JsonObject, Usage,
};

const PROVIDER: &str = "vertex_ai";
pub(crate) const DEFAULT_LOCATION: &str = "us-central1";
/// `anthropic_version` Claude on Vertex requires.
pub(crate) const VERTEX_ANTHROPIC_VERSION: &str = "vertex-2023-10-16";

/// Vertex-specific deployment settings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VertexConfig {
    pub project: Option<String>,
    pub location: String,
    pub credentials: GcpCredentials,
    /// `api_base` was configured rather than derived from the location.
    pub custom_api_base: bool,
}

/// Per-request auth context resolved by the client.
#[derive(Debug, Clone)]
pub(crate) struct Context {
    pub project: String,
    pub token: String,
}

/// Which publisher API a model uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Family {
    Gemini,
    Anthropic,
}

pub(crate) fn family(model: &str) -> Family {
    if model.to_ascii_lowercase().contains("claude") {
        Family::Anthropic
    } else {
        Family::Gemini
    }
}

/// LiteLLM's `get_vertex_base_url`.
pub(crate) fn base_url(location: &str) -> String {
    if location == "global" {
        "https://aiplatform.googleapis.com".to_owned()
    } else if !location.contains('-') {
        format!("https://aiplatform.{location}.rep.googleapis.com")
    } else {
        format!("https://{location}-aiplatform.googleapis.com")
    }
}

fn valid_location(s: &str) -> bool {
    !s.is_empty()
        && s.bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
}

/// Parse the Vertex-specific `litellm_params`; returns `(api_base, config)`
/// and consumes the `vertex_*` keys from `obj`.
pub(crate) fn parse_config(
    obj: &mut JsonObject,
    env: &dyn Fn(&str) -> Option<String>,
    explicit_api_key: Option<String>,
    configured_base: Option<String>,
) -> Result<(String, VertexConfig), ProviderError> {
    let cfg_err = |msg: String| ProviderError::config(PROVIDER, msg);
    let from_env = |names: &[&str]| names.iter().find_map(|n| env(n).filter(|v| !v.is_empty()));
    let take_either =
        |obj: &mut JsonObject, a: &str, b: &str| -> Result<Option<String>, ProviderError> {
            let first = take_string(obj, a)?;
            let second = take_string(obj, b)?;
            Ok(first.or(second))
        };

    let project = take_either(obj, "vertex_project", "vertex_ai_project")?
        .or_else(|| from_env(&["VERTEXAI_PROJECT"]));
    let location = take_either(obj, "vertex_location", "vertex_ai_location")?
        .or_else(|| from_env(&["VERTEXAI_LOCATION", "VERTEX_LOCATION"]))
        .unwrap_or_else(|| DEFAULT_LOCATION.to_owned());
    if !valid_location(&location) {
        return Err(cfg_err(format!("invalid vertex_location '{location}'")));
    }

    let raw_creds = match (
        obj.remove("vertex_credentials"),
        obj.remove("vertex_ai_credentials"),
    ) {
        (Some(v), _) | (None, Some(v)) if !v.is_null() => Some(v),
        _ => None,
    };
    let load = |src: &str| GcpCredentials::load(src).map_err(cfg_err);
    let credentials = if let Some(token) = explicit_api_key.filter(|k| !k.is_empty()) {
        GcpCredentials::AccessToken(Secret::new(token))
    } else if let Some(raw) = raw_creds {
        match &raw {
            Value::String(s) => load(s)?,
            Value::Object(_) => GcpCredentials::from_json(&raw).map_err(cfg_err)?,
            _ => {
                return Err(cfg_err(
                    "vertex_credentials must be a path, JSON string or object".into(),
                ));
            }
        }
    } else if let Some(src) = from_env(&["VERTEXAI_CREDENTIALS", "GOOGLE_APPLICATION_CREDENTIALS"])
    {
        load(&src)?
    } else if let Some(adc) = adc_file(env) {
        load(&adc)?
    } else {
        GcpCredentials::MetadataServer {
            host: from_env(&["GCE_METADATA_HOST", "GCE_METADATA_IP"])
                .unwrap_or_else(|| DEFAULT_METADATA_HOST.to_owned()),
        }
    };
    let project = project
        .or_else(|| credentials.project_id().map(str::to_owned))
        .or_else(|| from_env(&["GOOGLE_CLOUD_PROJECT", "GCLOUD_PROJECT"]));
    let custom_api_base = configured_base.is_some();
    if project.is_none()
        && !custom_api_base
        && !matches!(credentials, GcpCredentials::MetadataServer { .. })
    {
        return Err(cfg_err(
            "vertex_project is required (or VERTEXAI_PROJECT, or credentials with a project_id)"
                .into(),
        ));
    }
    let api_base = configured_base
        .map(|b| b.trim_end_matches('/').to_owned())
        .unwrap_or_else(|| base_url(&location));
    Ok((
        api_base,
        VertexConfig {
            project,
            location,
            credentials,
            custom_api_base,
        },
    ))
}

/// The gcloud application-default credentials file, if present.
fn adc_file(env: &dyn Fn(&str) -> Option<String>) -> Option<String> {
    let dir = env("CLOUDSDK_CONFIG")
        .or_else(|| env("HOME").map(|h| format!("{h}/.config/gcloud")))
        .or_else(|| env("APPDATA").map(|a| format!("{a}/gcloud")))?;
    let path = format!("{dir}/application_default_credentials.json");
    std::path::Path::new(&path).is_file().then_some(path)
}

pub(crate) fn config(dep: &Deployment) -> Result<&VertexConfig, ProviderError> {
    match &dep.cloud {
        Some(CloudConfig::Vertex(c)) => Ok(c),
        _ => Err(ProviderError::config(
            PROVIDER,
            "deployment has no Vertex AI settings",
        )),
    }
}

/// A path segment, keeping `@` (model versions such as
/// `claude-sonnet-4-5@20250929`) readable.
fn segment(s: &str) -> String {
    super::encode_path_segment(s).replace("%40", "@")
}

/// `publishers/{publisher}/models/{m}`, or `endpoints/{id}` for tuned
/// models.
fn resource(model: &str, publisher: &str) -> String {
    if !model.is_empty() && model.bytes().all(|b| b.is_ascii_digit()) {
        format!("endpoints/{model}")
    } else {
        format!("publishers/{publisher}/models/{}", segment(model))
    }
}

/// The full URL for `method` on `resource`.
pub(crate) fn url(
    dep: &Deployment,
    cfg: &VertexConfig,
    project: &str,
    resource: &str,
    method: &str,
    sse: bool,
) -> String {
    let api_base = dep.api_base().trim_end_matches('/');
    let path = format!(
        "projects/{project}/locations/{}/{resource}:{method}",
        cfg.location
    );
    let mut url = if !cfg.custom_api_base {
        format!("{api_base}/v1/{path}")
    } else {
        let base_path = reqwest::Url::parse(api_base)
            .map(|u| u.path().trim_end_matches('/').to_owned())
            .unwrap_or_default();
        match base_path.as_str() {
            "" => format!("{api_base}/v1/{path}"),
            "/v1" | "/v1beta1" => format!("{api_base}/{path}"),
            _ => format!("{api_base}:{method}"),
        }
    };
    if sse {
        url.push_str(if url.contains('?') {
            "&alt=sse"
        } else {
            "?alt=sse"
        });
    }
    url
}

fn authorize(mut http: HttpRequest, ctx: &Context) -> HttpRequest {
    http.headers.retain(|(n, _)| {
        !n.eq_ignore_ascii_case("x-api-key") && !n.eq_ignore_ascii_case("anthropic-version")
    });
    http.header("authorization", format!("Bearer {}", ctx.token))
}

pub(crate) fn chat_request(
    dep: &Deployment,
    ctx: &Context,
    req: &ChatRequest,
    stream: bool,
) -> Result<HttpRequest, ProviderError> {
    let cfg = config(dep)?;
    let mut http = match family(&dep.model) {
        Family::Anthropic => {
            let mut http = anthropic::chat_request(dep, req, stream)?;
            if let Value::Object(body) = &mut http.body {
                body.remove("model");
                body.insert(
                    "anthropic_version".into(),
                    Value::String(VERTEX_ANTHROPIC_VERSION.into()),
                );
            }
            let method = if stream {
                "streamRawPredict"
            } else {
                "rawPredict"
            };
            http.url = url(
                dep,
                cfg,
                &ctx.project,
                &resource(&dep.model, "anthropic"),
                method,
                false,
            );
            http
        }
        Family::Gemini => {
            let mut http = gemini::chat_request(dep, req, stream)?;
            let method = if stream {
                "streamGenerateContent"
            } else {
                "generateContent"
            };
            http.url = url(
                dep,
                cfg,
                &ctx.project,
                &resource(&dep.model, "google"),
                method,
                stream,
            );
            http
        }
    };
    http = authorize(http, ctx);
    Ok(http)
}

pub(crate) fn embeddings_request(
    dep: &Deployment,
    ctx: &Context,
    req: &EmbeddingRequest,
) -> Result<HttpRequest, ProviderError> {
    let cfg = config(dep)?;
    let texts = req.input.texts().ok_or_else(|| {
        ProviderError::bad_request(PROVIDER, "Vertex AI embeddings require text input")
    })?;
    let task_type = req
        .extra
        .get("task_type")
        .or_else(|| req.extra.get("input_type"));
    let title = req.extra.get("title");
    let instances: Vec<Value> = texts
        .iter()
        .map(|t| {
            let mut i = json!({"content": t});
            if let Some(tt) = task_type {
                i["task_type"] = tt.clone();
            }
            if let Some(title) = title {
                i["title"] = title.clone();
            }
            i
        })
        .collect();
    let mut parameters = Map::new();
    if let Some(d) = req.dimensions {
        parameters.insert("outputDimensionality".into(), json!(d));
    }
    if let Some(a) = req
        .extra
        .get("auto_truncate")
        .or_else(|| req.extra.get("autoTruncate"))
    {
        parameters.insert("autoTruncate".into(), a.clone());
    }
    let mut body = json!({"instances": instances});
    if !parameters.is_empty() {
        body["parameters"] = Value::Object(parameters);
    }
    for (k, v) in &dep.extra_body {
        body[k] = v.clone();
    }
    let http = HttpRequest::new(
        url(
            dep,
            cfg,
            &ctx.project,
            &resource(&dep.model, "google"),
            "predict",
            false,
        ),
        body,
    );
    Ok(authorize(http, ctx))
}

pub(crate) fn parse_embeddings(
    dep: &Deployment,
    body: &str,
) -> Result<EmbeddingResponse, ProviderError> {
    let v: Value = parse_json(PROVIDER, body)?;
    let predictions = v["predictions"].as_array().ok_or_else(|| {
        ProviderError::invalid_response(PROVIDER, "predict response without predictions")
    })?;
    let mut tokens = 0u64;
    let data = predictions
        .iter()
        .enumerate()
        .map(|(i, p)| {
            // Tuned models return the bare vector nested one level deeper.
            let values = p["embeddings"]["values"]
                .as_array()
                .or_else(|| p.as_array().and_then(|a| a.first()?.as_array()))
                .map(|a| a.iter().filter_map(Value::as_f64).collect())
                .unwrap_or_default();
            tokens += p["embeddings"]["statistics"]["token_count"]
                .as_f64()
                .unwrap_or(0.0) as u64;
            Embedding {
                object: "embedding".into(),
                index: i as u32,
                embedding: EmbeddingVector::Float(values),
            }
        })
        .collect();
    Ok(EmbeddingResponse {
        object: "list".into(),
        data,
        model: dep.model.clone(),
        usage: Usage::new(tokens, 0),
        extra: JsonObject::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::auth::gcp::tests::service_account_json;

    fn env(name: &str) -> Option<String> {
        match name {
            "SA_JSON" => Some(service_account_json("https://oauth2.example/token").to_string()),
            _ => None,
        }
    }

    fn parse(v: Value) -> Result<Deployment, ProviderError> {
        Deployment::from_litellm_params_with_env(&v, env)
    }

    fn ctx() -> Context {
        Context {
            project: "my-proj".into(),
            token: "ya29.token".into(),
        }
    }

    fn req(v: Value) -> ChatRequest {
        serde_json::from_value(v).unwrap()
    }

    fn hello() -> ChatRequest {
        req(json!({"model": "x", "messages": [
            {"role": "system", "content": "terse"}, {"role": "user", "content": "hi"}
        ], "max_tokens": 10}))
    }

    #[test]
    fn base_urls() {
        assert_eq!(
            base_url("us-central1"),
            "https://us-central1-aiplatform.googleapis.com"
        );
        assert_eq!(base_url("global"), "https://aiplatform.googleapis.com");
        assert_eq!(base_url("eu"), "https://aiplatform.eu.rep.googleapis.com");
    }

    #[test]
    fn credential_and_project_resolution() {
        // Service account from os.environ/ JSON: project from the key.
        let d = parse(json!({"model": "vertex_ai/gemini-2.0-flash", "vertex_credentials": "os.environ/SA_JSON"})).unwrap();
        let cfg = config(&d).unwrap();
        assert_eq!(cfg.project.as_deref(), Some("proj-from-key"));
        assert_eq!(cfg.location, DEFAULT_LOCATION);
        assert!(matches!(cfg.credentials, GcpCredentials::ServiceAccount(_)));
        assert_eq!(
            d.api_base.as_deref(),
            Some("https://us-central1-aiplatform.googleapis.com")
        );
        assert!(d.extra.is_empty(), "{:?}", d.extra);
        assert!(!format!("{d:?}").contains("PRIVATE KEY"));

        // Object form, explicit project and location win.
        let d = parse(json!({
            "model": "vertex_ai/claude-sonnet-4-5@20250929",
            "vertex_credentials": service_account_json("https://t"),
            "vertex_project": "explicit", "vertex_location": "global"
        }))
        .unwrap();
        let cfg = config(&d).unwrap();
        assert_eq!(
            (cfg.project.as_deref(), cfg.location.as_str()),
            (Some("explicit"), "global")
        );
        assert_eq!(
            d.api_base.as_deref(),
            Some("https://aiplatform.googleapis.com")
        );

        // Access token via api_key.
        let d = parse(json!({"model": "vertex_ai/gemini-2.0-flash", "api_key": "ya29.x", "vertex_ai_project": "p"})).unwrap();
        assert_eq!(
            config(&d).unwrap().credentials,
            GcpCredentials::AccessToken(Secret::new("ya29.x"))
        );

        // GOOGLE_APPLICATION_CREDENTIALS path.
        let path = std::env::temp_dir().join(format!("h5i-gw-vertex-{}.json", std::process::id()));
        std::fs::write(&path, service_account_json("https://t").to_string()).unwrap();
        let p = path.to_str().unwrap().to_owned();
        let d = Deployment::from_litellm_params_with_env(
            &json!({"model": "vertex_ai/gemini-2.0-flash"}),
            |n| (n == "GOOGLE_APPLICATION_CREDENTIALS").then(|| p.clone()),
        )
        .unwrap();
        std::fs::remove_file(&path).unwrap();
        assert_eq!(
            config(&d).unwrap().project.as_deref(),
            Some("proj-from-key")
        );

        // Nothing configured: metadata server, project resolved lazily.
        let d = Deployment::from_litellm_params_with_env(
            &json!({"model": "vertex_ai/gemini-2.0-flash"}),
            |n| (n == "GCE_METADATA_HOST").then(|| "127.0.0.1:1".to_owned()),
        )
        .unwrap();
        let cfg = config(&d).unwrap();
        assert_eq!(
            cfg.credentials,
            GcpCredentials::MetadataServer {
                host: "127.0.0.1:1".into()
            }
        );
        assert_eq!(cfg.project, None);

        // Errors.
        let no_env = |p: Value| Deployment::from_litellm_params_with_env(&p, |_| None);
        assert!(
            no_env(json!({"model": "vertex_ai/gemini-2.0-flash", "api_key": "t"}))
                .unwrap_err()
                .message()
                .contains("vertex_project")
        );
        assert!(
            no_env(
                json!({"model": "vertex_ai/gemini-2.0-flash", "vertex_credentials": "/nope.json"})
            )
            .is_err()
        );
        assert!(no_env(json!({"model": "vertex_ai/g", "api_key": "t", "vertex_project": "p", "vertex_location": "US CENTRAL"})).is_err());
    }

    #[test]
    fn gemini_on_vertex() {
        let d = parse(json!({"model": "vertex_ai/gemini-2.0-flash", "api_key": "ya29.x", "vertex_project": "p"})).unwrap();
        let r = chat_request(&d, &ctx(), &hello(), false).unwrap();
        assert_eq!(
            r.url,
            "https://us-central1-aiplatform.googleapis.com/v1/projects/my-proj/locations/us-central1/publishers/google/models/gemini-2.0-flash:generateContent"
        );
        assert_eq!(
            r.headers,
            vec![("authorization".to_owned(), "Bearer ya29.token".to_owned())]
        );
        assert_eq!(
            r.body["systemInstruction"],
            json!({"parts": [{"text": "terse"}]})
        );
        assert_eq!(r.body["generationConfig"]["maxOutputTokens"], 10);
        let r = chat_request(&d, &ctx(), &hello(), true).unwrap();
        assert!(
            r.url.ends_with(":streamGenerateContent?alt=sse"),
            "{}",
            r.url
        );
        // Tuned model endpoint.
        let d = parse(json!({"model": "vertex_ai/4965075652664360960", "api_key": "t", "vertex_project": "p"})).unwrap();
        let r = chat_request(&d, &ctx(), &hello(), false).unwrap();
        assert!(
            r.url
                .ends_with("/locations/us-central1/endpoints/4965075652664360960:generateContent")
        );
    }

    #[test]
    fn anthropic_on_vertex() {
        let d = parse(json!({"model": "vertex_ai/claude-sonnet-4-5@20250929", "api_key": "ya29.x", "vertex_project": "p", "vertex_location": "us-east5"})).unwrap();
        let r = chat_request(&d, &ctx(), &hello(), false).unwrap();
        assert_eq!(
            r.url,
            "https://us-east5-aiplatform.googleapis.com/v1/projects/my-proj/locations/us-east5/publishers/anthropic/models/claude-sonnet-4-5@20250929:rawPredict"
        );
        assert!(r.body.get("model").is_none());
        assert_eq!(r.body["anthropic_version"], VERTEX_ANTHROPIC_VERSION);
        assert_eq!(r.body["system"], json!([{"type": "text", "text": "terse"}]));
        assert_eq!(r.body["max_tokens"], 10);
        assert_eq!(
            r.headers,
            vec![("authorization".to_owned(), "Bearer ya29.token".to_owned())]
        );
        let r = chat_request(&d, &ctx(), &hello(), true).unwrap();
        assert!(r.url.ends_with(":streamRawPredict"));
        assert_eq!(r.body["stream"], true);
        // Default max_tokens comes from the vertex_ai price entry.
        let r = chat_request(
            &d,
            &ctx(),
            &req(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}]})),
            false,
        )
        .unwrap();
        assert!(r.body["max_tokens"].as_u64().unwrap() > 4096);
    }

    #[test]
    fn custom_api_bases() {
        let mk = |base: &str| {
            parse(json!({"model": "vertex_ai/gemini-2.0-flash", "api_key": "t", "vertex_project": "p", "api_base": base})).unwrap()
        };
        let path = "projects/my-proj/locations/us-central1/publishers/google/models/gemini-2.0-flash:generateContent";
        let d = mk("http://127.0.0.1:9/");
        assert_eq!(
            chat_request(&d, &ctx(), &hello(), false).unwrap().url,
            format!("http://127.0.0.1:9/v1/{path}")
        );
        let d = mk("https://proxy.example/v1beta1");
        assert_eq!(
            chat_request(&d, &ctx(), &hello(), false).unwrap().url,
            format!("https://proxy.example/v1beta1/{path}")
        );
        let d = mk("https://gw.example/vertex/my-endpoint");
        assert_eq!(
            chat_request(&d, &ctx(), &hello(), true).unwrap().url,
            "https://gw.example/vertex/my-endpoint:streamGenerateContent?alt=sse"
        );
        // A fully custom endpoint needs no project.
        assert!(Deployment::from_litellm_params_with_env(
            &json!({"model": "vertex_ai/gemini-2.0-flash", "api_key": "t", "api_base": "https://gw.example/x"}),
            |_| None
        )
        .is_ok());
    }

    #[test]
    fn embeddings() {
        let d = parse(
            json!({"model": "vertex_ai/text-embedding-004", "api_key": "t", "vertex_project": "p"}),
        )
        .unwrap();
        let er: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": ["a", "b"], "dimensions": 256, "task_type": "RETRIEVAL_QUERY"})).unwrap();
        let r = embeddings_request(&d, &ctx(), &er).unwrap();
        assert!(
            r.url
                .ends_with("/publishers/google/models/text-embedding-004:predict")
        );
        assert_eq!(
            r.body,
            json!({"instances": [{"content": "a", "task_type": "RETRIEVAL_QUERY"}, {"content": "b", "task_type": "RETRIEVAL_QUERY"}],
                   "parameters": {"outputDimensionality": 256}})
        );
        let resp = parse_embeddings(&d, &json!({"predictions": [
            {"embeddings": {"values": [0.1, 0.2], "statistics": {"token_count": 2, "truncated": false}}},
            {"embeddings": {"values": [0.3], "statistics": {"token_count": 3.0}}}
        ]}).to_string()).unwrap();
        assert_eq!(resp.data.len(), 2);
        assert_eq!(resp.data[1].embedding, EmbeddingVector::Float(vec![0.3]));
        assert_eq!(resp.usage.prompt_tokens, 5);
        assert!(parse_embeddings(&d, "{}").is_err());
        let p = d.pricing().unwrap();
        assert!(p.input_cost_per_token > 0.0);
    }

    #[test]
    fn pricing_lookup() {
        for model in [
            "vertex_ai/gemini-2.0-flash",
            "vertex_ai/claude-sonnet-4-5@20250929",
            "vertex_ai/gemini-embedding-001",
        ] {
            let d = parse(json!({"model": model, "api_key": "t", "vertex_project": "p"})).unwrap();
            assert!(
                d.pricing().is_some_and(|p| p.input_cost_per_token > 0.0),
                "{model}"
            );
        }
    }
}
