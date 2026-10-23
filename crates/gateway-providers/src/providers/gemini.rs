//! Google AI Studio Gemini API (`generativelanguage.googleapis.com`):
//! `generateContent`, `streamGenerateContent?alt=sse` and
//! `batchEmbedContents`, authenticated with `?key=`.
//!
//! Translation follows LiteLLM's `VertexGeminiConfig` and
//! `_gemini_convert_messages_with_history`:
//!
//! * `system`/`developer` messages -> `systemInstruction`;
//! * `assistant` -> role `model`; consecutive same-role turns are merged;
//! * `tool_calls` <-> `functionCall` parts, `role: tool` ->
//!   `functionResponse` (the function name is recovered from the matching
//!   assistant tool call; JSON-object results are passed as objects);
//! * Gemini thought signatures are carried in the tool call id as
//!   `<id>__thought__<signature>` (LiteLLM convention) and restored on replay;
//! * images/audio/files: data URLs -> `inlineData`, URLs -> `fileData`;
//! * tool parameter schemas are reduced to Gemini's OpenAPI subset (or sent
//!   as `parametersJsonSchema` when they use `$ref`);
//! * `response_format` -> `responseMimeType` + `responseJsonSchema`;
//! * `reasoning_effort` -> `thinkingConfig`;
//! * `usageMetadata` -> usage (thinking tokens count as completion tokens).

use serde_json::{Map, Value, json};

use super::{
    HttpRequest, StreamTranslator, encode_path_segment, gen_id, map_finish_reason, mime_from_url,
    now_unix, parse_arguments, parse_data_url, parse_json,
};
use crate::deployment::Deployment;
use crate::error::ProviderError;
use crate::sse::SseEvent;
use crate::tokens::text_tokens;
use crate::types::{
    ChatChunk, ChatMessage, ChatRequest, ChatResponse, Choice, ChunkChoice,
    CompletionTokensDetails, ContentPart, Delta, Embedding, EmbeddingRequest, EmbeddingResponse,
    EmbeddingVector, FunctionCallDelta, JsonObject, PromptTokensDetails, Role, Tool, ToolCall,
    ToolCallDelta, ToolChoice, Usage, finish_reason, part_type,
};

/// Separator between a tool call id and an embedded thought signature.
pub(crate) const THOUGHT_SIGNATURE_SEPARATOR: &str = "__thought__";
const PROVIDER: &str = "gemini";
const PLACEHOLDER: &str = ".";
/// `thinkingBudget` per `reasoning_effort` (LiteLLM defaults).
const THINKING_BUDGETS: &[(&str, i64)] = &[
    ("none", 0),
    ("disable", 0),
    ("minimal", 128),
    ("low", 1024),
    ("medium", 2048),
    ("high", 4096),
];
/// Native fields forwarded from the request's extra fields.
const PASSTHROUGH_FIELDS: &[&str] = &[
    "safetySettings",
    "safety_settings",
    "cachedContent",
    "labels",
];
/// Schema keywords Gemini's OpenAPI-subset `Schema` accepts.
const SCHEMA_KEYS: &[&str] = &[
    "description",
    "format",
    "title",
    "nullable",
    "enum",
    "required",
    "minItems",
    "maxItems",
    "minimum",
    "maximum",
    "minLength",
    "maxLength",
    "pattern",
    "example",
    "default",
    "propertyOrdering",
    "minProperties",
    "maxProperties",
];

pub(crate) fn model_url(dep: &Deployment, method: &str, stream: bool) -> String {
    let base = dep.api_base().trim_end_matches('/');
    let versioned = if ["/v1beta", "/v1", "/v1alpha"]
        .iter()
        .any(|v| base.ends_with(v))
    {
        base.to_owned()
    } else {
        format!("{base}/v1beta")
    };
    let model = dep.model.strip_prefix("models/").unwrap_or(&dep.model);
    let mut url = format!("{versioned}/models/{}:{method}", encode_path_segment(model));
    let mut sep = '?';
    if stream {
        url.push_str("?alt=sse");
        sep = '&';
    }
    if let Some(key) = &dep.api_key {
        url.push(sep);
        url.push_str("key=");
        url.push_str(&encode_path_segment(key.expose()));
    }
    url
}

pub(crate) fn chat_request(
    dep: &Deployment,
    req: &ChatRequest,
    stream: bool,
) -> Result<HttpRequest, ProviderError> {
    let (system, contents) = translate_messages(&req.messages)?;
    let mut body = Map::new();
    body.insert("contents".into(), Value::Array(contents));
    if !system.is_empty() {
        body.insert("systemInstruction".into(), json!({"parts": system}));
    }

    let tools = translate_tools(req.tools.as_deref().unwrap_or_default());
    if !tools.is_empty() {
        body.insert("tools".into(), Value::Array(tools));
        if let Some(tc) = translate_tool_choice(req.tool_choice.as_ref())? {
            body.insert("toolConfig".into(), tc);
        }
    }

    let mut generation = Map::new();
    let mut set = |k: &str, v: Option<Value>| {
        if let Some(v) = v {
            generation.insert(k.to_owned(), v);
        }
    };
    set("temperature", req.temperature.map(Value::from));
    set("topP", req.top_p.map(Value::from));
    set("topK", req.extra.get("top_k").cloned());
    set("maxOutputTokens", req.max_output_tokens().map(Value::from));
    set(
        "stopSequences",
        req.stop.as_ref().map(|s| json!(s.to_vec())),
    );
    set("candidateCount", req.n.map(Value::from));
    set("presencePenalty", req.presence_penalty.map(Value::from));
    set("frequencyPenalty", req.frequency_penalty.map(Value::from));
    set("seed", req.seed.map(Value::from));
    set("responseLogprobs", req.logprobs.map(Value::from));
    set("logprobs", req.top_logprobs.map(Value::from));
    if let Some(f) = &req.response_format {
        match f.kind.as_str() {
            "json_object" => set("responseMimeType", Some(json!("application/json"))),
            "json_schema" => {
                set("responseMimeType", Some(json!("application/json")));
                set(
                    "responseJsonSchema",
                    f.json_schema.as_ref().and_then(|s| s.schema.clone()),
                );
            }
            _ => {}
        }
    }
    if let Some(effort) = req.reasoning_effort.as_deref()
        && let Some((_, budget)) = THINKING_BUDGETS.iter().find(|(e, _)| *e == effort)
    {
        set(
            "thinkingConfig",
            Some(json!({"thinkingBudget": budget, "includeThoughts": *budget > 0})),
        );
    }
    if let Some(Value::Object(extra_gen)) = req.extra.get("generationConfig") {
        for (k, v) in extra_gen {
            generation.insert(k.clone(), v.clone());
        }
    }
    if !generation.is_empty() {
        body.insert("generationConfig".into(), Value::Object(generation));
    }
    for key in PASSTHROUGH_FIELDS {
        if let Some(v) = req.extra.get(*key) {
            body.insert((*key).to_owned(), v.clone());
        }
    }
    for (k, v) in &dep.extra_body {
        body.insert(k.clone(), v.clone());
    }

    let method = if stream {
        "streamGenerateContent"
    } else {
        "generateContent"
    };
    Ok(HttpRequest::new(
        model_url(dep, method, stream),
        Value::Object(body),
    ))
}

/// Returns `(systemInstruction parts, contents)`.
fn translate_messages(msgs: &[ChatMessage]) -> Result<(Vec<Value>, Vec<Value>), ProviderError> {
    let mut system = Vec::new();
    let mut turns: Vec<(&'static str, Vec<Value>)> = Vec::new();
    let mut push = |role: &'static str, parts: Vec<Value>| {
        if parts.is_empty() {
            return;
        }
        match turns.last_mut() {
            Some((r, existing)) if *r == role => existing.extend(parts),
            _ => turns.push((role, parts)),
        }
    };

    for (i, m) in msgs.iter().enumerate() {
        match m.role {
            Role::System | Role::Developer => {
                let text = m.text();
                if !text.is_empty() {
                    system.push(json!({"text": text}));
                }
            }
            Role::User => {
                let parts = match &m.content {
                    None => Vec::new(),
                    Some(c) => c
                        .parts()
                        .iter()
                        .map(user_part)
                        .collect::<Result<Vec<_>, _>>()?,
                };
                push("user", parts.into_iter().flatten().collect());
            }
            Role::Assistant => {
                let mut parts = Vec::new();
                let text = m.text();
                if !text.is_empty() {
                    parts.push(json!({"text": text}));
                }
                for call in m.tool_calls.iter().flatten() {
                    let mut part = json!({"functionCall": {
                        "name": call.function.name,
                        "args": parse_arguments(PROVIDER, &call.function.arguments)?,
                    }});
                    if let Some((_, sig)) = call.id.split_once(THOUGHT_SIGNATURE_SEPARATOR) {
                        part["thoughtSignature"] = Value::String(sig.to_owned());
                    }
                    parts.push(part);
                }
                if let Some(call) = &m.function_call {
                    parts.push(json!({"functionCall": {
                        "name": call.name,
                        "args": parse_arguments(PROVIDER, &call.arguments)?,
                    }}));
                }
                push("model", parts);
            }
            Role::Tool | Role::Function => {
                let name = tool_name_for(&msgs[..i], m).ok_or_else(|| {
                    ProviderError::bad_request(
                        PROVIDER,
                        "tool message does not match any previous tool call",
                    )
                })?;
                push("user", vec![function_response(&name, &m.text())]);
            }
        }
    }
    if turns.is_empty() {
        turns.push(("user", vec![json!({"text": PLACEHOLDER})]));
    }
    let contents = turns
        .into_iter()
        .map(|(role, parts)| json!({"role": role, "parts": parts}))
        .collect();
    Ok((system, contents))
}

/// The function name for a tool result: from the assistant tool call with
/// the same id, else the message's `name`.
fn tool_name_for(history: &[ChatMessage], m: &ChatMessage) -> Option<String> {
    let from_call = m.tool_call_id.as_deref().and_then(|id| {
        history
            .iter()
            .rev()
            .flat_map(|h| h.tool_calls.iter().flatten())
            .find(|c| c.id == id)
            .map(|c| c.function.name.clone())
    });
    from_call.or_else(|| m.name.clone())
}

fn function_response(name: &str, content: &str) -> Value {
    let trimmed = content.trim_start();
    let response = match serde_json::from_str::<Value>(content) {
        Ok(obj @ Value::Object(_)) if trimmed.starts_with('{') => obj,
        _ => json!({"content": content}),
    };
    json!({"functionResponse": {"name": name, "response": response}})
}

fn user_part(p: &ContentPart) -> Result<Option<Value>, ProviderError> {
    let media = |url: &str, mime_override: Option<&str>| match parse_data_url(url) {
        Some((mime, data)) => {
            json!({"inlineData": {"mimeType": mime_override.unwrap_or(mime), "data": data}})
        }
        None => {
            json!({"fileData": {"mimeType": mime_override.unwrap_or_else(|| mime_from_url(url)), "fileUri": url}})
        }
    };
    Ok(match p.kind.as_str() {
        part_type::TEXT => p
            .text
            .as_deref()
            .filter(|t| !t.is_empty())
            .map(|t| json!({"text": t})),
        part_type::IMAGE_URL => p
            .image_url
            .as_ref()
            .map(|i| media(&i.url, i.format.as_deref())),
        part_type::INPUT_AUDIO => p.input_audio.as_ref().map(
            |a| json!({"inlineData": {"mimeType": format!("audio/{}", a.format), "data": a.data}}),
        ),
        part_type::FILE => match p.file.as_ref() {
            Some(f) => match (&f.file_data, &f.file_id) {
                (Some(data), _) => Some(media(data, None)),
                (None, Some(id)) => Some(media(id, None)),
                (None, None) => None,
            },
            None => None,
        },
        other => {
            return Err(ProviderError::bad_request(
                PROVIDER,
                format!("content part type '{other}' is not supported by Gemini"),
            ));
        }
    })
}

fn translate_tools(tools: &[Tool]) -> Vec<Value> {
    let mut declarations = Vec::new();
    let mut native = Vec::new();
    for tool in tools {
        let Some(f) = &tool.function else {
            // Native Gemini tools such as `{"googleSearch": {}}`.
            native.push(Value::Object(tool.extra.clone()));
            continue;
        };
        let mut decl = json!({"name": f.name});
        if let Some(d) = &f.description {
            decl["description"] = Value::String(d.clone());
        }
        if let Some(params) = &f.parameters {
            if contains_ref(params) {
                decl["parametersJsonSchema"] = params.clone();
            } else {
                let schema = gemini_schema(params);
                // Gemini rejects OBJECT schemas without properties.
                let empty_object = schema.get("type").and_then(Value::as_str) == Some("object")
                    && schema
                        .get("properties")
                        .and_then(Value::as_object)
                        .is_none_or(Map::is_empty);
                if !empty_object {
                    decl["parameters"] = schema;
                }
            }
        }
        declarations.push(decl);
    }
    let mut out = Vec::new();
    if !declarations.is_empty() {
        out.push(json!({"functionDeclarations": declarations}));
    }
    out.extend(native);
    out
}

fn contains_ref(v: &Value) -> bool {
    match v {
        Value::Object(o) => o.contains_key("$ref") || o.values().any(contains_ref),
        Value::Array(a) => a.iter().any(contains_ref),
        _ => false,
    }
}

/// Reduce a JSON Schema to the OpenAPI subset Gemini's `Schema` accepts.
fn gemini_schema(v: &Value) -> Value {
    let Value::Object(o) = v else {
        return v.clone();
    };
    let mut out = Map::new();
    for (k, val) in o {
        match k.as_str() {
            "type" => match val {
                Value::Array(types) => {
                    if let Some(t) = types.iter().find(|t| t.as_str() != Some("null")) {
                        out.insert("type".into(), t.clone());
                    }
                    if types.iter().any(|t| t.as_str() == Some("null")) {
                        out.insert("nullable".into(), Value::Bool(true));
                    }
                }
                t => {
                    out.insert("type".into(), t.clone());
                }
            },
            "properties" => {
                if let Value::Object(props) = val {
                    let props = props
                        .iter()
                        .map(|(n, s)| (n.clone(), gemini_schema(s)))
                        .collect();
                    out.insert("properties".into(), Value::Object(props));
                }
            }
            "items" => {
                out.insert("items".into(), gemini_schema(val));
            }
            "anyOf" | "oneOf" => {
                if let Value::Array(alts) = val {
                    out.insert(
                        "anyOf".into(),
                        Value::Array(alts.iter().map(gemini_schema).collect()),
                    );
                }
            }
            "const" => {
                out.insert("enum".into(), json!([val]));
            }
            k if SCHEMA_KEYS.contains(&k) => {
                out.insert(k.to_owned(), val.clone());
            }
            // $schema, additionalProperties, strict, $defs, examples, ...
            _ => {}
        }
    }
    Value::Object(out)
}

fn translate_tool_choice(choice: Option<&ToolChoice>) -> Result<Option<Value>, ProviderError> {
    let mode = |m: &str| json!({"functionCallingConfig": {"mode": m}});
    Ok(match choice {
        None => None,
        Some(ToolChoice::Mode(m)) => Some(match m.as_str() {
            "none" => mode("NONE"),
            "required" => mode("ANY"),
            "auto" => mode("AUTO"),
            other => {
                return Err(ProviderError::bad_request(
                    PROVIDER,
                    format!("unsupported tool_choice '{other}'"),
                ));
            }
        }),
        Some(ToolChoice::Named(n)) => n.function.as_ref().map(
            |f| json!({"functionCallingConfig": {"mode": "ANY", "allowedFunctionNames": [f.name]}}),
        ),
    })
}

/// Usage from `usageMetadata` (LiteLLM `calculate_usage`).
pub(crate) fn usage_from(m: &Value) -> Usage {
    let get = |k: &str| m.get(k).and_then(Value::as_u64).unwrap_or(0);
    let prompt = get("promptTokenCount") + get("toolUsePromptTokenCount");
    let candidates = get("candidatesTokenCount");
    let thoughts = get("thoughtsTokenCount");
    let total = get("totalTokenCount");
    // Some models report candidatesTokenCount inclusive of thinking tokens.
    let inclusive = prompt + candidates == total;
    let completion = if inclusive {
        candidates
    } else {
        candidates + thoughts
    };
    let cached = m.get("cachedContentTokenCount").and_then(Value::as_u64);
    Usage {
        total_tokens: total.max(prompt + completion),
        prompt_tokens_details: cached.map(|c| PromptTokensDetails {
            cached_tokens: Some(c),
            ..PromptTokensDetails::default()
        }),
        completion_tokens_details: (thoughts > 0).then(|| CompletionTokensDetails {
            reasoning_tokens: Some(thoughts),
            ..CompletionTokensDetails::default()
        }),
        cache_read_input_tokens: cached,
        ..Usage::new(prompt, completion)
    }
}

/// Content of one candidate.
#[derive(Default)]
struct CandidateContent {
    text: String,
    reasoning: String,
    tool_calls: Vec<ToolCall>,
}

fn candidate_content(c: &Value) -> CandidateContent {
    let mut out = CandidateContent::default();
    for part in c["content"]["parts"].as_array().into_iter().flatten() {
        if let Some(call) = part.get("functionCall") {
            let base_id = call["id"]
                .as_str()
                .map_or_else(|| gen_id("call_"), str::to_owned);
            let id = match part.get("thoughtSignature").and_then(Value::as_str) {
                Some(sig) => format!("{base_id}{THOUGHT_SIGNATURE_SEPARATOR}{sig}"),
                None => base_id,
            };
            let args = call
                .get("args")
                .map_or_else(|| "{}".to_owned(), Value::to_string);
            out.tool_calls.push(ToolCall::function(
                id,
                call["name"].as_str().unwrap_or_default(),
                args,
            ));
        } else if let Some(text) = part.get("text").and_then(Value::as_str) {
            if part.get("thought").and_then(Value::as_bool) == Some(true) {
                out.reasoning.push_str(text);
            } else {
                out.text.push_str(text);
            }
        }
    }
    out
}

fn finish_for(c: &Value, had_tool_calls: bool) -> Option<String> {
    let reason = map_finish_reason(c.get("finishReason")?.as_str()?);
    // Gemini reports STOP after function calls.
    Some(
        if had_tool_calls && reason == finish_reason::STOP {
            finish_reason::TOOL_CALLS
        } else {
            reason
        }
        .to_owned(),
    )
}

/// A `200` body that is actually an error (`{"error": ...}`).
fn embedded_error(v: &Value, raw: &str) -> Option<ProviderError> {
    let err = v.get("error")?;
    let status = err["code"]
        .as_u64()
        .filter(|c| (400..=599).contains(c))
        .unwrap_or(500) as u16;
    Some(ProviderError::from_upstream(PROVIDER, status, raw, None))
}

pub(crate) fn parse_chat(dep: &Deployment, body: &str) -> Result<ChatResponse, ProviderError> {
    let v: Value = parse_json(PROVIDER, body)?;
    if let Some(e) = embedded_error(&v, body) {
        return Err(e);
    }
    let mut choices: Vec<Choice> = v["candidates"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(i, c)| {
            let content = candidate_content(c);
            let had_tools = !content.tool_calls.is_empty();
            let mut message = ChatMessage::assistant(content.text);
            if had_tools {
                if message.text().is_empty() {
                    message.content = None;
                }
                message.tool_calls = Some(content.tool_calls);
            }
            if !content.reasoning.is_empty() {
                message.reasoning_content = Some(content.reasoning);
            }
            Choice {
                index: c["index"].as_u64().map_or(i as u32, |n| n as u32),
                message,
                finish_reason: finish_for(c, had_tools),
                logprobs: None,
                extra: JsonObject::new(),
            }
        })
        .collect();
    if choices.is_empty() {
        // The prompt itself was blocked (`promptFeedback.blockReason`).
        let mut message = ChatMessage::assistant("");
        message.content = None;
        choices.push(Choice {
            index: 0,
            message,
            finish_reason: Some(finish_reason::CONTENT_FILTER.into()),
            logprobs: None,
            extra: JsonObject::new(),
        });
    }
    Ok(ChatResponse {
        id: v["responseId"]
            .as_str()
            .map_or_else(|| gen_id("chatcmpl-"), str::to_owned),
        object: "chat.completion".into(),
        created: now_unix(),
        model: v["modelVersion"].as_str().unwrap_or(&dep.model).to_owned(),
        choices,
        usage: v.get("usageMetadata").map(usage_from),
        system_fingerprint: None,
        extra: JsonObject::new(),
    })
}

/// Gemini SSE events (each a partial `GenerateContentResponse`) -> OpenAI
/// chunks. Gemini has no end marker: the usage chunk is emitted at EOF.
pub(crate) struct GeminiStream {
    id: Option<String>,
    model: String,
    created: u64,
    usage: Option<Value>,
    /// Per candidate: role sent, tool calls emitted so far.
    candidates: Vec<(bool, u32)>,
}

impl GeminiStream {
    pub fn new(dep: &Deployment) -> Self {
        Self {
            id: None,
            model: dep.model.clone(),
            created: now_unix(),
            usage: None,
            candidates: Vec::new(),
        }
    }

    fn id(&mut self) -> String {
        self.id.get_or_insert_with(|| gen_id("chatcmpl-")).clone()
    }
}

impl StreamTranslator for GeminiStream {
    fn on_event(&mut self, event: SseEvent) -> Result<Vec<ChatChunk>, ProviderError> {
        let v: Value = parse_json(PROVIDER, &event.data)?;
        if let Some(e) = embedded_error(&v, &event.data) {
            return Err(e);
        }
        if self.id.is_none()
            && let Some(id) = v["responseId"].as_str()
        {
            self.id = Some(id.to_owned());
        }
        if let Some(model) = v["modelVersion"].as_str() {
            self.model = model.to_owned();
        }
        if let Some(u) = v.get("usageMetadata") {
            self.usage = Some(u.clone());
        }
        let mut choices = Vec::new();
        for (i, c) in v["candidates"].as_array().into_iter().flatten().enumerate() {
            let index = c["index"].as_u64().map_or(i, |n| n as usize);
            if self.candidates.len() <= index {
                self.candidates.resize(index + 1, (false, 0));
            }
            let content = candidate_content(c);
            let (role_sent, tool_count) = &mut self.candidates[index];
            let mut delta = Delta {
                role: (!*role_sent).then_some(Role::Assistant),
                content: (!content.text.is_empty()).then_some(content.text),
                reasoning_content: (!content.reasoning.is_empty()).then_some(content.reasoning),
                ..Delta::default()
            };
            *role_sent = true;
            if !content.tool_calls.is_empty() {
                let deltas = content
                    .tool_calls
                    .into_iter()
                    .map(|call| {
                        let d = ToolCallDelta {
                            index: *tool_count,
                            id: Some(call.id),
                            kind: Some(call.kind),
                            function: Some(FunctionCallDelta {
                                name: Some(call.function.name),
                                arguments: Some(call.function.arguments),
                            }),
                        };
                        *tool_count += 1;
                        d
                    })
                    .collect();
                delta.tool_calls = Some(deltas);
            }
            choices.push(ChunkChoice {
                index: index as u32,
                delta,
                finish_reason: finish_for(c, *tool_count > 0),
                logprobs: None,
                extra: JsonObject::new(),
            });
        }
        if choices.is_empty() {
            return Ok(Vec::new());
        }
        let mut chunk = ChatChunk::new(self.id(), self.model.clone(), self.created);
        chunk.choices = choices;
        Ok(vec![chunk])
    }

    fn is_done(&self) -> bool {
        false
    }

    fn finish(&mut self) -> Result<Vec<ChatChunk>, ProviderError> {
        let Some(usage) = self.usage.take() else {
            return Ok(Vec::new());
        };
        let chunk = ChatChunk::new(self.id(), self.model.clone(), self.created)
            .with_usage(usage_from(&usage));
        Ok(vec![chunk])
    }
}

pub(crate) fn embeddings_request(
    dep: &Deployment,
    req: &EmbeddingRequest,
) -> Result<HttpRequest, ProviderError> {
    let texts = req.input.texts().ok_or_else(|| {
        ProviderError::bad_request(PROVIDER, "Gemini embeddings require text input")
    })?;
    let model = format!(
        "models/{}",
        dep.model.strip_prefix("models/").unwrap_or(&dep.model)
    );
    let requests: Vec<Value> = texts
        .iter()
        .map(|t| {
            let mut r = json!({"model": model, "content": {"parts": [{"text": t}]}});
            if let Some(d) = req.dimensions {
                r["outputDimensionality"] = json!(d);
            }
            r
        })
        .collect();
    let mut body = json!({"requests": requests});
    for (k, v) in &dep.extra_body {
        body[k] = v.clone();
    }
    Ok(HttpRequest::new(
        model_url(dep, "batchEmbedContents", false),
        body,
    ))
}

pub(crate) fn parse_embeddings(
    dep: &Deployment,
    req: &EmbeddingRequest,
    body: &str,
) -> Result<EmbeddingResponse, ProviderError> {
    let v: Value = parse_json(PROVIDER, body)?;
    if let Some(e) = embedded_error(&v, body) {
        return Err(e);
    }
    let data = v["embeddings"]
        .as_array()
        .ok_or_else(|| {
            ProviderError::invalid_response(
                PROVIDER,
                "batchEmbedContents response without embeddings",
            )
        })?
        .iter()
        .enumerate()
        .map(|(i, e)| {
            let values = e["values"]
                .as_array()
                .map(|vals| vals.iter().filter_map(Value::as_f64).collect())
                .unwrap_or_default();
            Embedding {
                object: "embedding".into(),
                index: i as u32,
                embedding: EmbeddingVector::Float(values),
            }
        })
        .collect();
    // Gemini does not report embedding usage; estimate it.
    let prompt: u64 = req
        .input
        .texts()
        .unwrap_or_default()
        .iter()
        .map(|t| text_tokens(t))
        .sum();
    Ok(EmbeddingResponse {
        object: "list".into(),
        data,
        model: dep.model.clone(),
        usage: Usage::new(prompt, 0),
        extra: JsonObject::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::providers::translate_all;

    fn dep() -> Deployment {
        Deployment::from_litellm_params_with_env(
            &json!({"model": "gemini/gemini-1.5-pro", "api_key": "gk"}),
            |_| None,
        )
        .unwrap()
    }

    fn req(v: Value) -> ChatRequest {
        serde_json::from_value(v).unwrap()
    }

    fn body(v: Value) -> Value {
        chat_request(&dep(), &req(v), false).unwrap().body
    }

    #[test]
    fn urls() {
        let r = req(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}]}));
        assert_eq!(
            chat_request(&dep(), &r, false).unwrap().url,
            "https://generativelanguage.googleapis.com/v1beta/models/gemini-1.5-pro:generateContent?key=gk"
        );
        assert_eq!(
            chat_request(&dep(), &r, true).unwrap().url,
            "https://generativelanguage.googleapis.com/v1beta/models/gemini-1.5-pro:streamGenerateContent?alt=sse&key=gk"
        );
        let mut d = dep();
        d.api_base = Some("http://127.0.0.1:9/v1".into());
        d.api_key = None;
        assert_eq!(
            model_url(&d, "generateContent", false),
            "http://127.0.0.1:9/v1/models/gemini-1.5-pro:generateContent"
        );
    }

    #[test]
    fn messages_and_generation_config() {
        let b = body(json!({"model": "x",
            "messages": [
                {"role": "system", "content": "be brief"},
                {"role": "user", "content": [
                    {"type": "text", "text": "what is this?"},
                    {"type": "image_url", "image_url": {"url": "data:image/png;base64,iVBOR"}},
                    {"type": "image_url", "image_url": "https://example.com/a.webp"},
                    {"type": "input_audio", "input_audio": {"data": "UklG", "format": "wav"}}
                ]},
                {"role": "assistant", "content": "A cat."},
                {"role": "assistant", "content": "Meow."},
                {"role": "user", "content": "thanks"}
            ],
            "temperature": 0.2, "top_p": 0.8, "max_tokens": 100, "stop": "END", "n": 2, "seed": 7, "top_k": 4,
            "response_format": {"type": "json_schema", "json_schema": {"name": "s", "schema": {"type": "object"}}},
            "reasoning_effort": "low",
            "safetySettings": [{"category": "HARM_CATEGORY_HARASSMENT", "threshold": "BLOCK_NONE"}]
        }));
        assert_eq!(
            b["systemInstruction"],
            json!({"parts": [{"text": "be brief"}]})
        );
        assert_eq!(
            b["contents"],
            json!([
                {"role": "user", "parts": [
                    {"text": "what is this?"},
                    {"inlineData": {"mimeType": "image/png", "data": "iVBOR"}},
                    {"fileData": {"mimeType": "image/webp", "fileUri": "https://example.com/a.webp"}},
                    {"inlineData": {"mimeType": "audio/wav", "data": "UklG"}}
                ]},
                {"role": "model", "parts": [{"text": "A cat."}, {"text": "Meow."}]},
                {"role": "user", "parts": [{"text": "thanks"}]}
            ])
        );
        assert_eq!(
            b["generationConfig"],
            json!({
                "temperature": 0.2, "topP": 0.8, "topK": 4, "maxOutputTokens": 100, "stopSequences": ["END"],
                "candidateCount": 2, "seed": 7, "responseMimeType": "application/json",
                "responseJsonSchema": {"type": "object"},
                "thinkingConfig": {"thinkingBudget": 1024, "includeThoughts": true}
            })
        );
        assert_eq!(b["safetySettings"][0]["threshold"], "BLOCK_NONE");
        let b = body(json!({"model": "x", "messages": [{"role": "system", "content": "s"}]}));
        assert_eq!(
            b["contents"],
            json!([{"role": "user", "parts": [{"text": "."}]}])
        );
        assert!(b.get("generationConfig").is_none());
    }

    #[test]
    fn tools_round_trip() {
        let b = body(json!({"model": "x",
            "messages": [
                {"role": "user", "content": "weather?"},
                {"role": "assistant", "content": null, "tool_calls": [
                    {"id": "call_1__thought__c2ln", "type": "function", "function": {"name": "get_weather", "arguments": "{\"city\":\"Paris\"}"}}
                ]},
                {"role": "tool", "tool_call_id": "call_1__thought__c2ln", "content": "{\"temp\": 21}"},
                {"role": "tool", "name": "legacy", "content": "plain text"}
            ],
            "tools": [
                {"type": "function", "function": {"name": "get_weather", "description": "Weather",
                    "parameters": {"$schema": "x", "type": "object", "additionalProperties": false,
                        "properties": {"city": {"type": ["string", "null"], "const": "Paris"}, "tags": {"type": "array", "items": {"type": "string", "examples": ["a"]}}},
                        "required": ["city"]}}},
                {"type": "function", "function": {"name": "no_args", "parameters": {"type": "object", "properties": {}}}},
                {"type": "function", "function": {"name": "refs", "parameters": {"type": "object", "properties": {"a": {"$ref": "#/$defs/A"}}, "$defs": {"A": {"type": "string"}}}}},
                {"googleSearch": {}}
            ],
            "tool_choice": {"type": "function", "function": {"name": "get_weather"}}
        }));
        assert_eq!(
            b["contents"][1],
            json!({"role": "model", "parts": [
                {"functionCall": {"name": "get_weather", "args": {"city": "Paris"}}, "thoughtSignature": "c2ln"}
            ]})
        );
        assert_eq!(
            b["contents"][2],
            json!({"role": "user", "parts": [
                {"functionResponse": {"name": "get_weather", "response": {"temp": 21}}},
                {"functionResponse": {"name": "legacy", "response": {"content": "plain text"}}}
            ]})
        );
        assert_eq!(
            b["tools"][0]["functionDeclarations"][0],
            json!({
                "name": "get_weather", "description": "Weather",
                "parameters": {"type": "object", "required": ["city"], "properties": {
                    "city": {"type": "string", "nullable": true, "enum": ["Paris"]},
                    "tags": {"type": "array", "items": {"type": "string"}}
                }}
            })
        );
        assert_eq!(
            b["tools"][0]["functionDeclarations"][1],
            json!({"name": "no_args"})
        );
        assert!(
            b["tools"][0]["functionDeclarations"][2]
                .get("parametersJsonSchema")
                .is_some()
        );
        assert_eq!(b["tools"][1], json!({"googleSearch": {}}));
        assert_eq!(
            b["toolConfig"],
            json!({"functionCallingConfig": {"mode": "ANY", "allowedFunctionNames": ["get_weather"]}})
        );

        let tc = |c: &str| {
            translate_tool_choice(Some(&ToolChoice::Mode(c.into())))
                .unwrap()
                .unwrap()
        };
        assert_eq!(tc("none")["functionCallingConfig"]["mode"], "NONE");
        assert_eq!(tc("required")["functionCallingConfig"]["mode"], "ANY");
        assert_eq!(tc("auto")["functionCallingConfig"]["mode"], "AUTO");
        assert!(translate_tool_choice(Some(&ToolChoice::Mode("bogus".into()))).is_err());

        let orphan = req(
            json!({"model": "x", "messages": [{"role": "tool", "tool_call_id": "zzz", "content": "x"}]}),
        );
        assert!(chat_request(&dep(), &orphan, false).is_err());
        let unknown = req(
            json!({"model": "x", "messages": [{"role": "user", "content": [{"type": "weird"}]}]}),
        );
        assert!(chat_request(&dep(), &unknown, false).is_err());
    }

    #[test]
    fn response_translation() {
        let resp = parse_chat(&dep(), &json!({
            "candidates": [{
                "content": {"role": "model", "parts": [
                    {"text": "Thinking...", "thought": true},
                    {"text": "It is "},
                    {"text": "sunny."},
                    {"functionCall": {"name": "get_weather", "args": {"city": "Paris"}}, "thoughtSignature": "c2ln"}
                ]},
                "finishReason": "STOP", "index": 0
            }],
            "usageMetadata": {"promptTokenCount": 10, "candidatesTokenCount": 5, "thoughtsTokenCount": 3, "totalTokenCount": 18, "cachedContentTokenCount": 4},
            "modelVersion": "gemini-1.5-pro-002",
            "responseId": "resp-1"
        }).to_string()).unwrap();
        assert_eq!(
            (resp.id.as_str(), resp.model.as_str()),
            ("resp-1", "gemini-1.5-pro-002")
        );
        let c = &resp.choices[0];
        assert_eq!(c.message.text(), "It is sunny.");
        assert_eq!(c.message.reasoning_content.as_deref(), Some("Thinking..."));
        assert_eq!(c.finish_reason.as_deref(), Some("tool_calls"));
        let call = &c.message.tool_calls.as_ref().unwrap()[0];
        assert!(call.id.ends_with("__thought__c2ln"));
        assert_eq!(call.function.arguments, "{\"city\":\"Paris\"}");
        let u = resp.usage.unwrap();
        assert_eq!(
            (u.prompt_tokens, u.completion_tokens, u.total_tokens),
            (10, 8, 18)
        );
        assert_eq!(
            u.completion_tokens_details.unwrap().reasoning_tokens,
            Some(3)
        );
        assert_eq!(u.prompt_tokens_details.unwrap().cached_tokens, Some(4));

        // Inclusive candidate count (prompt + candidates == total).
        let u = usage_from(
            &json!({"promptTokenCount": 10, "candidatesTokenCount": 8, "thoughtsTokenCount": 3, "totalTokenCount": 18}),
        );
        assert_eq!(u.completion_tokens, 8);

        let blocked =
            parse_chat(&dep(), r#"{"promptFeedback": {"blockReason": "SAFETY"}}"#).unwrap();
        assert_eq!(
            blocked.choices[0].finish_reason.as_deref(),
            Some("content_filter")
        );
        let max = parse_chat(&dep(), r#"{"candidates": [{"content": {"parts": [{"text": "x"}]}, "finishReason": "MAX_TOKENS"}]}"#).unwrap();
        assert_eq!(max.choices[0].finish_reason.as_deref(), Some("length"));
        let err = parse_chat(
            &dep(),
            r#"{"error": {"code": 429, "message": "quota", "status": "RESOURCE_EXHAUSTED"}}"#,
        )
        .unwrap_err();
        assert_eq!(err.kind(), crate::ErrorKind::RateLimited);
    }

    #[test]
    fn stream_translation() {
        let chunks = translate_all(GeminiStream::new(&dep()), &[
            ("", r#"{"candidates": [{"content": {"role": "model", "parts": [{"text": "Hel"}]}, "index": 0}], "usageMetadata": {"promptTokenCount": 7, "totalTokenCount": 7}, "modelVersion": "gemini-1.5-pro-002", "responseId": "r1"}"#),
            ("", r#"{"candidates": [{"content": {"role": "model", "parts": [{"text": "lo"}]}, "index": 0}], "responseId": "r1"}"#),
            ("", r#"{"candidates": [{"content": {"role": "model", "parts": [{"functionCall": {"name": "f", "args": {"a": 1}}}]}, "finishReason": "STOP", "index": 0}], "usageMetadata": {"promptTokenCount": 7, "candidatesTokenCount": 4, "totalTokenCount": 11}}"#),
        ]).unwrap();
        assert_eq!(chunks.len(), 4);
        assert_eq!(chunks[0].choices[0].delta.role, Some(Role::Assistant));
        assert_eq!(chunks[0].choices[0].delta.content.as_deref(), Some("Hel"));
        assert_eq!(chunks[1].choices[0].delta.role, None);
        let tc = &chunks[2].choices[0].delta.tool_calls.as_ref().unwrap()[0];
        assert_eq!(
            (tc.index, tc.function.as_ref().unwrap().arguments.as_deref()),
            (0, Some("{\"a\":1}"))
        );
        assert_eq!(
            chunks[2].choices[0].finish_reason.as_deref(),
            Some("tool_calls")
        );
        assert!(chunks[3].is_usage_only());
        let u = chunks[3].usage.as_ref().unwrap();
        assert_eq!(
            (u.prompt_tokens, u.completion_tokens, u.total_tokens),
            (7, 4, 11)
        );
        assert!(
            chunks
                .iter()
                .all(|c| c.id == "r1" && c.model == "gemini-1.5-pro-002")
        );

        let err = translate_all(
            GeminiStream::new(&dep()),
            &[("", r#"{"error": {"code": 503, "message": "overloaded"}}"#)],
        )
        .unwrap_err();
        assert_eq!(err.status_code(), 503);
    }

    #[test]
    fn embeddings() {
        let ereq: EmbeddingRequest =
            serde_json::from_value(json!({"model": "x", "input": ["a", "bb"], "dimensions": 4}))
                .unwrap();
        let mut d = dep();
        d.model = "text-embedding-004".into();
        let r = embeddings_request(&d, &ereq).unwrap();
        assert!(
            r.url
                .ends_with("/models/text-embedding-004:batchEmbedContents?key=gk")
        );
        assert_eq!(
            r.body["requests"][1],
            json!({"model": "models/text-embedding-004", "content": {"parts": [{"text": "bb"}]}, "outputDimensionality": 4})
        );
        let resp = parse_embeddings(
            &d,
            &ereq,
            r#"{"embeddings": [{"values": [0.1, 0.2]}, {"values": [0.3]}]}"#,
        )
        .unwrap();
        assert_eq!(resp.data[1].embedding, EmbeddingVector::Float(vec![0.3]));
        assert_eq!(resp.data[1].index, 1);
        assert_eq!(resp.usage.prompt_tokens, 2);
        let tokens: EmbeddingRequest =
            serde_json::from_value(json!({"model": "x", "input": [1, 2]})).unwrap();
        assert!(embeddings_request(&d, &tokens).is_err());
    }
}
