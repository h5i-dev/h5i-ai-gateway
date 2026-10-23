//! Anthropic Messages API (`POST /v1/messages`).
//!
//! Translation follows LiteLLM's `AnthropicConfig` and
//! `anthropic_messages_pt`:
//!
//! * `system`/`developer` messages are hoisted into `system` text blocks;
//! * consecutive user/tool messages merge into one `user` turn (tool results
//!   first), consecutive assistant messages into one `assistant` turn; the
//!   conversation is made to start with a user turn and the final assistant
//!   prefill loses trailing whitespace;
//! * `tool_calls` <-> `tool_use` blocks, `role: tool` -> `tool_result`;
//! * images: data URLs -> base64 sources, `http(s)` URLs -> URL sources (the
//!   gateway never fetches URLs itself); files -> `document` blocks;
//! * `cache_control` on messages, parts and tools is forwarded;
//! * `max_tokens` is required: the request value, else the model's
//!   `max_output_tokens` from the pricing table, else 4096;
//! * `response_format: json_schema` becomes a forced `json_tool_call` tool
//!   whose input is returned as message content;
//! * `reasoning_effort` maps to an extended-thinking budget; `thinking`,
//!   `top_k` and other native fields in the request pass through.

use std::collections::HashMap;

use serde_json::{Map, Value, json};

use super::{
    HttpRequest, StreamTranslator, gen_id, map_finish_reason, now_unix, parse_arguments,
    parse_data_url, parse_json,
};
use crate::deployment::Deployment;
use crate::error::ProviderError;
use crate::pricing;
use crate::sse::SseEvent;
use crate::types::{
    ChatChunk, ChatMessage, ChatRequest, ChatResponse, Choice, ContentPart, Delta, FileContent,
    FunctionCallDelta, ImageUrl, JsonObject, MessageContent, PromptTokensDetails, ResponseFormat,
    Role, Tool, ToolCall, ToolCallDelta, ToolChoice, Usage, finish_reason, part_type,
};

pub(crate) const ANTHROPIC_VERSION: &str = "2023-06-01";
/// LiteLLM's `DEFAULT_ANTHROPIC_CHAT_MAX_TOKENS`.
pub(crate) const DEFAULT_MAX_TOKENS: u64 = 4096;
/// Tool used to emulate `response_format` (LiteLLM's
/// `RESPONSE_FORMAT_TOOL_NAME`).
pub(crate) const JSON_TOOL_NAME: &str = "json_tool_call";
/// Placeholder for turns Anthropic requires but the conversation lacks.
const PLACEHOLDER: &str = ".";
/// Extended-thinking budgets for `reasoning_effort` (LiteLLM defaults).
const THINKING_BUDGETS: &[(&str, u64)] = &[("low", 1024), ("medium", 2048), ("high", 4096)];
const MIN_THINKING_BUDGET: u64 = 1024;
/// Native Messages API fields forwarded from the request's extra fields.
const PASSTHROUGH_FIELDS: &[&str] = &[
    "top_k",
    "thinking",
    "service_tier",
    "container",
    "mcp_servers",
    "context_management",
];

fn messages_url(dep: &Deployment) -> String {
    let base = dep.api_base().trim_end_matches('/');
    if base.ends_with("/v1/messages") {
        base.to_owned()
    } else if base.ends_with("/v1") {
        format!("{base}/messages")
    } else {
        format!("{base}/v1/messages")
    }
}

/// Whether the request asks for JSON output via a schema (emulated with a
/// forced tool).
fn json_schema_of(format: Option<&ResponseFormat>) -> Option<Value> {
    let f = format?;
    if f.kind != "json_schema" {
        return None;
    }
    f.json_schema.as_ref()?.schema.clone()
}

pub(crate) fn chat_request(
    dep: &Deployment,
    req: &ChatRequest,
    stream: bool,
) -> Result<HttpRequest, ProviderError> {
    let provider = dep.provider.name();
    let (system, messages) = translate_messages(provider, &req.messages)?;

    let mut body = Map::new();
    body.insert("model".into(), Value::String(dep.model.clone()));
    body.insert("messages".into(), Value::Array(messages));
    if !system.is_empty() {
        body.insert("system".into(), Value::Array(system));
    }

    for key in PASSTHROUGH_FIELDS {
        if let Some(v) = req.extra.get(*key) {
            body.insert((*key).to_owned(), v.clone());
        }
    }

    let explicit_max = req.max_output_tokens();
    let mut max_tokens = explicit_max.unwrap_or_else(|| {
        pricing::lookup_with_provider(provider, &dep.model)
            .and_then(|p| p.max_output_tokens)
            .unwrap_or(DEFAULT_MAX_TOKENS)
    });
    if !body.contains_key("thinking")
        && let Some(effort) = req.reasoning_effort.as_deref()
        && let Some(&(_, mut budget)) = THINKING_BUDGETS.iter().find(|(e, _)| *e == effort)
    {
        if explicit_max.is_some() {
            budget = budget.min(max_tokens.saturating_sub(1));
        } else if max_tokens <= budget {
            max_tokens = budget + DEFAULT_MAX_TOKENS;
        }
        if budget >= MIN_THINKING_BUDGET {
            body.insert(
                "thinking".into(),
                json!({"type": "enabled", "budget_tokens": budget}),
            );
        }
    }
    body.insert("max_tokens".into(), json!(max_tokens));
    let thinking = body
        .get("thinking")
        .and_then(|t| t.get("type"))
        .is_some_and(|t| t != "disabled");

    let mut tools: Vec<Value> = req
        .tools
        .iter()
        .flatten()
        .map(translate_tool)
        .collect::<Result<_, _>>()?;
    let mut tool_choice = translate_tool_choice(req.tool_choice.as_ref(), req.parallel_tool_calls);
    if let Some(schema) = json_schema_of(req.response_format.as_ref()) {
        let mut input_schema = json!({"type": "object"});
        if let (Value::Object(target), Value::Object(src)) = (&mut input_schema, schema) {
            target.extend(src);
        }
        tools.push(json!({"name": JSON_TOOL_NAME, "input_schema": input_schema}));
        // Forcing a tool is incompatible with extended thinking.
        if !thinking {
            tool_choice = Some(json!({"type": "tool", "name": JSON_TOOL_NAME}));
        }
    }
    if !tools.is_empty() {
        body.insert("tools".into(), Value::Array(tools));
        if let Some(tc) = tool_choice {
            body.insert("tool_choice".into(), tc);
        }
    }

    if let Some(stop) = &req.stop {
        // Anthropic rejects whitespace-only stop sequences.
        let stops: Vec<String> = stop
            .to_vec()
            .into_iter()
            .filter(|s| !s.trim().is_empty())
            .collect();
        if !stops.is_empty() {
            body.insert("stop_sequences".into(), json!(stops));
        }
    }
    if let Some(t) = req.temperature {
        body.insert("temperature".into(), json!(t));
    }
    if let Some(p) = req.top_p {
        body.insert("top_p".into(), json!(p));
    }
    // Anthropic rejects user ids that look like e-mail addresses.
    if let Some(user) = req
        .user
        .as_deref()
        .filter(|u| !u.is_empty() && !u.contains('@'))
    {
        body.insert("metadata".into(), json!({"user_id": user}));
    }
    if stream {
        body.insert("stream".into(), Value::Bool(true));
    }
    for (k, v) in &dep.extra_body {
        body.insert(k.clone(), v.clone());
    }

    let mut http = HttpRequest::new(messages_url(dep), Value::Object(body))
        .header("anthropic-version", ANTHROPIC_VERSION);
    if let Some(key) = &dep.api_key {
        http = http.header("x-api-key", key.expose());
    }
    Ok(http)
}

/// Returns `(system blocks, messages)`.
fn translate_messages(
    provider: &str,
    msgs: &[ChatMessage],
) -> Result<(Vec<Value>, Vec<Value>), ProviderError> {
    let mut system = Vec::new();
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

    for m in msgs {
        let cache_control = m.extra.get("cache_control");
        match m.role {
            Role::System | Role::Developer => {
                if let Some(content) = &m.content {
                    for part in content.parts().iter() {
                        if let Some(text) = part.text.as_deref().filter(|t| !t.is_empty()) {
                            let cc = part.extra.get("cache_control").or(cache_control);
                            system.push(text_block(text, cc));
                        }
                    }
                }
            }
            Role::User => push("user", user_blocks(provider, m)?),
            Role::Tool | Role::Function => push("user", vec![tool_result(provider, m)?]),
            Role::Assistant => push("assistant", assistant_blocks(provider, m)?),
        }
    }

    if turns.first().is_none_or(|(role, _)| *role != "user") {
        turns.insert(0, ("user", vec![text_block(PLACEHOLDER, None)]));
    }
    // "final assistant content cannot end with trailing whitespace"
    if let Some((role, blocks)) = turns.last_mut()
        && *role == "assistant"
    {
        if let Some(Value::Object(last)) = blocks.last_mut()
            && last.get("type").and_then(Value::as_str) == Some("text")
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
                // tool_result blocks must precede any other content.
                content
                    .sort_by_key(|b| b.get("type").and_then(Value::as_str) != Some("tool_result"));
            }
            json!({"role": role, "content": content})
        })
        .collect();
    Ok((system, messages))
}

fn text_block(text: &str, cache_control: Option<&Value>) -> Value {
    let mut block = json!({"type": "text", "text": text});
    with_cache_control(&mut block, cache_control);
    block
}

fn with_cache_control(block: &mut Value, cache_control: Option<&Value>) {
    if let (Some(cc), Value::Object(obj)) = (cache_control.filter(|c| !c.is_null()), block) {
        obj.insert("cache_control".into(), cc.clone());
    }
}

fn user_blocks(provider: &str, m: &ChatMessage) -> Result<Vec<Value>, ProviderError> {
    let cache_control = m.extra.get("cache_control");
    match &m.content {
        None => Ok(Vec::new()),
        Some(MessageContent::Text(s)) if s.is_empty() => Ok(Vec::new()),
        Some(MessageContent::Text(s)) => Ok(vec![text_block(s, cache_control)]),
        Some(MessageContent::Parts(parts)) => {
            let mut out = Vec::with_capacity(parts.len());
            for p in parts {
                if let Some(mut block) = content_block(provider, p)? {
                    with_cache_control(&mut block, p.extra.get("cache_control"));
                    out.push(block);
                }
            }
            Ok(out)
        }
    }
}

/// Translate one OpenAI content part; unknown part types are assumed to be
/// native Anthropic blocks and pass through unchanged.
fn content_block(provider: &str, p: &ContentPart) -> Result<Option<Value>, ProviderError> {
    let missing = |field: &str| {
        ProviderError::bad_request(provider, format!("{} part without '{field}'", p.kind))
    };
    Ok(match p.kind.as_str() {
        part_type::TEXT => p
            .text
            .as_deref()
            .filter(|t| !t.is_empty())
            .map(|t| text_block(t, None)),
        part_type::IMAGE_URL => Some(image_block(
            provider,
            p.image_url.as_ref().ok_or_else(|| missing("image_url"))?,
        )?),
        part_type::FILE => Some(document_block(
            provider,
            p.file.as_ref().ok_or_else(|| missing("file"))?,
        )?),
        part_type::INPUT_AUDIO => {
            return Err(ProviderError::bad_request(
                provider,
                "Anthropic does not support audio input",
            ));
        }
        _ => {
            let mut raw = serde_json::to_value(p)
                .map_err(|e| ProviderError::bad_request(provider, e.to_string()))?;
            if let Value::Object(o) = &mut raw {
                o.remove("cache_control");
            }
            Some(raw)
        }
    })
}

fn image_block(provider: &str, image: &ImageUrl) -> Result<Value, ProviderError> {
    let url = image.url.as_str();
    if let Some((mime, data)) = parse_data_url(url) {
        let media_type = image.format.as_deref().unwrap_or(mime);
        let kind = if media_type.starts_with("image/") {
            "image"
        } else {
            "document"
        };
        return Ok(
            json!({"type": kind, "source": {"type": "base64", "media_type": media_type, "data": data}}),
        );
    }
    if url.starts_with("https://") || url.starts_with("http://") {
        return Ok(json!({"type": "image", "source": {"type": "url", "url": url}}));
    }
    Err(ProviderError::bad_request(
        provider,
        "image_url must be an http(s) URL or a base64 data URL",
    ))
}

fn document_block(provider: &str, file: &FileContent) -> Result<Value, ProviderError> {
    let mut block = if let Some((mime, data)) = file.file_data.as_deref().and_then(parse_data_url) {
        let kind = if mime.starts_with("image/") {
            "image"
        } else {
            "document"
        };
        json!({"type": kind, "source": {"type": "base64", "media_type": mime, "data": data}})
    } else if let Some(id) = &file.file_id {
        json!({"type": "document", "source": {"type": "file", "file_id": id}})
    } else {
        return Err(ProviderError::bad_request(
            provider,
            "file part needs file_data (base64 data URL) or file_id",
        ));
    };
    if let (Some(name), Some("document")) = (&file.filename, block["type"].as_str()) {
        block["title"] = Value::String(name.clone());
    }
    Ok(block)
}

/// Anthropic tool ids must match `^[a-zA-Z0-9_-]+$`.
fn sanitize_tool_id(id: &str) -> String {
    let s: String = id
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if s.is_empty() {
        "tool_use_id".to_owned()
    } else {
        s
    }
}

/// Synthetic id linking a legacy `function_call` to its `role: function`
/// result.
fn legacy_function_id(name: &str) -> String {
    sanitize_tool_id(&format!("function_call_{name}"))
}

fn tool_result(provider: &str, m: &ChatMessage) -> Result<Value, ProviderError> {
    let id = match (&m.tool_call_id, &m.name) {
        (Some(id), _) => sanitize_tool_id(id),
        (None, Some(name)) if m.role == Role::Function => legacy_function_id(name),
        _ => {
            return Err(ProviderError::bad_request(
                provider,
                "tool message without tool_call_id",
            ));
        }
    };
    let content = match &m.content {
        None => Value::String(String::new()),
        Some(MessageContent::Text(s)) => Value::String(s.clone()),
        Some(MessageContent::Parts(parts)) => {
            let mut blocks = Vec::with_capacity(parts.len());
            for p in parts {
                if let Some(mut b) = content_block(provider, p)? {
                    with_cache_control(&mut b, p.extra.get("cache_control"));
                    blocks.push(b);
                }
            }
            Value::Array(blocks)
        }
    };
    let mut block = json!({"type": "tool_result", "tool_use_id": id, "content": content});
    with_cache_control(&mut block, m.extra.get("cache_control"));
    Ok(block)
}

fn assistant_blocks(provider: &str, m: &ChatMessage) -> Result<Vec<Value>, ProviderError> {
    let mut out = Vec::new();
    // Thinking blocks from a previous response must be replayed first.
    if let Some(Value::Array(thinking)) = m.extra.get("thinking_blocks") {
        out.extend(thinking.iter().cloned());
    }
    match &m.content {
        None => {}
        Some(MessageContent::Text(s)) => {
            if !s.is_empty() {
                out.push(text_block(s, m.extra.get("cache_control")));
            }
        }
        Some(MessageContent::Parts(parts)) => {
            for p in parts {
                if let Some(mut b) = content_block(provider, p)? {
                    with_cache_control(&mut b, p.extra.get("cache_control"));
                    out.push(b);
                }
            }
        }
    }
    for call in m.tool_calls.iter().flatten() {
        out.push(json!({
            "type": "tool_use",
            "id": sanitize_tool_id(&call.id),
            "name": call.function.name,
            "input": parse_arguments(provider, &call.function.arguments)?,
        }));
    }
    if let Some(call) = &m.function_call {
        out.push(json!({
            "type": "tool_use",
            "id": legacy_function_id(&call.name),
            "name": call.name,
            "input": parse_arguments(provider, &call.arguments)?,
        }));
    }
    Ok(out)
}

fn translate_tool(tool: &Tool) -> Result<Value, ProviderError> {
    let Some(f) = &tool.function else {
        // Native Anthropic tools (e.g. `web_search_20250305`) pass through.
        let mut raw = tool.extra.clone();
        raw.insert("type".into(), Value::String(tool.kind.clone()));
        return Ok(Value::Object(raw));
    };
    let mut schema = f
        .parameters
        .clone()
        .unwrap_or_else(|| json!({"type": "object", "properties": {}}));
    if let Value::Object(s) = &mut schema {
        s.entry("type").or_insert_with(|| json!("object"));
    }
    let mut out = json!({"name": f.name, "input_schema": schema});
    if let Some(d) = &f.description {
        out["description"] = Value::String(d.clone());
    }
    with_cache_control(&mut out, tool.extra.get("cache_control"));
    Ok(out)
}

/// LiteLLM `_map_tool_choice`.
fn translate_tool_choice(choice: Option<&ToolChoice>, parallel: Option<bool>) -> Option<Value> {
    let mode = |m: &str| match m {
        "auto" => Some(json!({"type": "auto"})),
        "required" | "any" => Some(json!({"type": "any"})),
        "none" => Some(json!({"type": "none"})),
        _ => None,
    };
    let mut out = match choice {
        None => None,
        Some(ToolChoice::Mode(m)) => mode(m),
        Some(ToolChoice::Named(n)) => match &n.function {
            Some(f) => Some(json!({"type": "tool", "name": f.name})),
            None => mode(&n.kind),
        },
    };
    let is_none = out.as_ref().is_some_and(|c| c["type"] == "none");
    if let Some(parallel) = parallel
        && !is_none
    {
        let choice = out.get_or_insert_with(|| json!({"type": "auto"}));
        choice["disable_parallel_tool_use"] = Value::Bool(!parallel);
    }
    out
}

/// LiteLLM `calculate_usage`: prompt tokens include cache reads and writes.
pub(crate) fn usage_from(u: &JsonObject) -> Usage {
    let get = |k: &str| u.get(k).and_then(Value::as_u64).unwrap_or(0);
    let cache_creation = get("cache_creation_input_tokens");
    let cache_read = get("cache_read_input_tokens");
    let prompt = get("input_tokens") + cache_creation + cache_read;
    Usage {
        prompt_tokens_details: Some(PromptTokensDetails {
            cached_tokens: Some(cache_read),
            cache_creation_tokens: Some(cache_creation),
            ..PromptTokensDetails::default()
        }),
        cache_creation_input_tokens: Some(cache_creation),
        cache_read_input_tokens: Some(cache_read),
        ..Usage::new(prompt, get("output_tokens"))
    }
}

fn finish_reason_for(stop_reason: Option<&str>, json_mode: bool) -> Option<String> {
    let reason = map_finish_reason(stop_reason?);
    Some(
        if json_mode && reason == finish_reason::TOOL_CALLS {
            finish_reason::STOP
        } else {
            reason
        }
        .to_owned(),
    )
}

pub(crate) fn parse_chat(
    dep: &Deployment,
    req: &ChatRequest,
    body: &str,
) -> Result<ChatResponse, ProviderError> {
    let provider = dep.provider.name();
    let json_mode = json_schema_of(req.response_format.as_ref()).is_some();
    let v: Value = parse_json(provider, body)?;
    let blocks = v.get("content").and_then(Value::as_array).ok_or_else(|| {
        ProviderError::invalid_response(provider, "Messages response without content")
    })?;

    let mut text = String::new();
    let mut reasoning = String::new();
    let mut thinking_blocks = Vec::new();
    let mut tool_calls = Vec::new();
    for b in blocks {
        match b.get("type").and_then(Value::as_str) {
            Some("text") => text.push_str(b["text"].as_str().unwrap_or_default()),
            Some("tool_use") => {
                let name = b["name"].as_str().unwrap_or_default();
                let input = serde_json::to_string(&b["input"]).unwrap_or_else(|_| "{}".into());
                if json_mode && name == JSON_TOOL_NAME {
                    text.push_str(&input);
                } else {
                    tool_calls.push(ToolCall::function(
                        b["id"].as_str().unwrap_or_default(),
                        name,
                        input,
                    ));
                }
            }
            Some("thinking") => {
                reasoning.push_str(b["thinking"].as_str().unwrap_or_default());
                thinking_blocks.push(b.clone());
            }
            Some("redacted_thinking") => thinking_blocks.push(b.clone()),
            _ => {}
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
        message
            .extra
            .insert("thinking_blocks".into(), Value::Array(thinking_blocks));
    }

    Ok(ChatResponse {
        id: v["id"]
            .as_str()
            .map_or_else(|| gen_id("chatcmpl-"), str::to_owned),
        object: "chat.completion".into(),
        created: now_unix(),
        model: v["model"].as_str().unwrap_or(&dep.model).to_owned(),
        choices: vec![Choice {
            index: 0,
            message,
            finish_reason: finish_reason_for(v["stop_reason"].as_str(), json_mode),
            logprobs: None,
            extra: JsonObject::new(),
        }],
        usage: v.get("usage").and_then(Value::as_object).map(usage_from),
        system_fingerprint: None,
        extra: JsonObject::new(),
    })
}

/// What an open content block is, by its stream index.
enum Block {
    Text,
    Tool { index: u32, has_args: bool },
    JsonTool,
    Thinking,
    Other,
}

/// Anthropic SSE events -> OpenAI chunks.
pub(crate) struct AnthropicStream {
    json_mode: bool,
    id: String,
    model: String,
    created: u64,
    /// Raw usage, merged from `message_start` and `message_delta` (the
    /// latter is cumulative but may omit fields).
    usage: JsonObject,
    blocks: HashMap<u64, Block>,
    next_tool: u32,
    done: bool,
}

impl AnthropicStream {
    pub fn new(dep: &Deployment, req: &ChatRequest) -> Self {
        Self {
            json_mode: json_schema_of(req.response_format.as_ref()).is_some(),
            id: gen_id("chatcmpl-"),
            model: dep.model.clone(),
            created: now_unix(),
            usage: JsonObject::new(),
            blocks: HashMap::new(),
            next_tool: 0,
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
        vec![self.chunk(
            Delta {
                content: Some(text.to_owned()),
                ..Delta::default()
            },
            None,
        )]
    }

    fn tool_delta(&self, delta: ToolCallDelta) -> ChatChunk {
        self.chunk(
            Delta {
                tool_calls: Some(vec![delta]),
                ..Delta::default()
            },
            None,
        )
    }

    fn args_delta(&self, index: u32, args: &str) -> ChatChunk {
        self.tool_delta(ToolCallDelta {
            index,
            function: Some(FunctionCallDelta {
                name: None,
                arguments: Some(args.to_owned()),
            }),
            ..ToolCallDelta::default()
        })
    }

    fn merge_usage(&mut self, usage: Option<&Value>) {
        if let Some(Value::Object(u)) = usage {
            for (k, v) in u {
                if !v.is_null() {
                    self.usage.insert(k.clone(), v.clone());
                }
            }
        }
    }
}

impl StreamTranslator for AnthropicStream {
    fn on_event(&mut self, event: SseEvent) -> Result<Vec<ChatChunk>, ProviderError> {
        let provider = "anthropic";
        let v: Value = parse_json(provider, &event.data)?;
        let index = v.get("index").and_then(Value::as_u64).unwrap_or(0);
        Ok(
            match v.get("type").and_then(Value::as_str).unwrap_or_default() {
                "message_start" => {
                    let msg = &v["message"];
                    if let Some(id) = msg["id"].as_str() {
                        self.id = id.to_owned();
                    }
                    if let Some(model) = msg["model"].as_str() {
                        self.model = model.to_owned();
                    }
                    self.merge_usage(msg.get("usage"));
                    vec![self.chunk(
                        Delta {
                            role: Some(Role::Assistant),
                            content: Some(String::new()),
                            ..Delta::default()
                        },
                        None,
                    )]
                }
                "content_block_start" => {
                    let block = &v["content_block"];
                    match block["type"].as_str().unwrap_or_default() {
                        "text" => {
                            self.blocks.insert(index, Block::Text);
                            self.content(block["text"].as_str().unwrap_or_default())
                        }
                        "tool_use" => {
                            let name = block["name"].as_str().unwrap_or_default();
                            if self.json_mode && name == JSON_TOOL_NAME {
                                self.blocks.insert(index, Block::JsonTool);
                                return Ok(Vec::new());
                            }
                            let tool_index = self.next_tool;
                            self.next_tool += 1;
                            self.blocks.insert(
                                index,
                                Block::Tool {
                                    index: tool_index,
                                    has_args: false,
                                },
                            );
                            vec![self.tool_delta(ToolCallDelta {
                                index: tool_index,
                                id: block["id"].as_str().map(str::to_owned),
                                kind: Some("function".into()),
                                function: Some(FunctionCallDelta {
                                    name: Some(name.to_owned()),
                                    arguments: Some(String::new()),
                                }),
                            })]
                        }
                        "thinking" => {
                            self.blocks.insert(index, Block::Thinking);
                            Vec::new()
                        }
                        _ => {
                            self.blocks.insert(index, Block::Other);
                            Vec::new()
                        }
                    }
                }
                "content_block_delta" => {
                    let delta = &v["delta"];
                    match (
                        delta["type"].as_str().unwrap_or_default(),
                        self.blocks.get_mut(&index),
                    ) {
                        ("text_delta", _) => {
                            self.content(delta["text"].as_str().unwrap_or_default())
                        }
                        ("input_json_delta", Some(Block::Tool { index, has_args })) => {
                            let partial = delta["partial_json"].as_str().unwrap_or_default();
                            if partial.is_empty() {
                                return Ok(Vec::new());
                            }
                            *has_args = true;
                            let index = *index;
                            vec![self.args_delta(index, partial)]
                        }
                        ("input_json_delta", Some(Block::JsonTool)) => {
                            self.content(delta["partial_json"].as_str().unwrap_or_default())
                        }
                        ("thinking_delta", _) => {
                            let thinking = delta["thinking"].as_str().unwrap_or_default();
                            if thinking.is_empty() {
                                return Ok(Vec::new());
                            }
                            vec![self.chunk(
                                Delta {
                                    reasoning_content: Some(thinking.to_owned()),
                                    ..Delta::default()
                                },
                                None,
                            )]
                        }
                        // signature_delta, citations_delta, deltas of server
                        // tool blocks: nothing to surface.
                        _ => Vec::new(),
                    }
                }
                "content_block_stop" => match self.blocks.remove(&index) {
                    // A tool called without arguments still needs valid JSON.
                    Some(Block::Tool {
                        index,
                        has_args: false,
                    }) => vec![self.args_delta(index, "{}")],
                    _ => Vec::new(),
                },
                "message_delta" => {
                    self.merge_usage(v.get("usage"));
                    let finish =
                        finish_reason_for(v["delta"]["stop_reason"].as_str(), self.json_mode);
                    match finish {
                        Some(f) => vec![self.chunk(Delta::default(), Some(f))],
                        None => Vec::new(),
                    }
                }
                "message_stop" => {
                    self.done = true;
                    if self.usage.is_empty() {
                        Vec::new()
                    } else {
                        vec![
                            ChatChunk::new(self.id.clone(), self.model.clone(), self.created)
                                .with_usage(usage_from(&self.usage)),
                        ]
                    }
                }
                "error" => return Err(ProviderError::from_stream_error(provider, &v["error"])),
                // ping and future event types
                _ => Vec::new(),
            },
        )
    }

    fn is_done(&self) -> bool {
        self.done
    }

    fn finish(&mut self) -> Result<Vec<ChatChunk>, ProviderError> {
        Err(ProviderError::new(
            crate::ErrorKind::Connection,
            "anthropic",
            "stream ended before message_stop",
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::providers::translate_all;

    fn dep() -> Deployment {
        Deployment::from_litellm_params_with_env(
            &json!({"model": "anthropic/claude-3-5-sonnet-20241022", "api_key": "sk-ant"}),
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
    fn url_headers_and_basics() {
        let r = chat_request(
            &dep(),
            &req(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}],
                        "temperature": 0.3, "top_p": 0.9, "stop": ["END", " "], "user": "u-1", "top_k": 5})),
            true,
        )
        .unwrap();
        assert_eq!(r.url, "https://api.anthropic.com/v1/messages");
        assert!(r.headers.contains(&("x-api-key".into(), "sk-ant".into())));
        assert!(
            r.headers
                .contains(&("anthropic-version".into(), ANTHROPIC_VERSION.into()))
        );
        let b = r.body;
        assert_eq!(b["model"], "claude-3-5-sonnet-20241022");
        assert_eq!(
            b["messages"],
            json!([{"role": "user", "content": [{"type": "text", "text": "hi"}]}])
        );
        assert_eq!(b["stop_sequences"], json!(["END"]));
        assert_eq!(
            (b["temperature"].clone(), b["top_p"].clone()),
            (json!(0.3), json!(0.9))
        );
        assert_eq!(b["metadata"], json!({"user_id": "u-1"}));
        assert_eq!(b["top_k"], 5);
        assert_eq!(b["stream"], true);
        assert!(b["max_tokens"].as_u64().unwrap() > 0);

        let mut d = dep();
        d.api_base = Some("https://proxy/v1".into());
        assert_eq!(messages_url(&d), "https://proxy/v1/messages");
        d.api_base = Some("https://proxy/v1/messages/".into());
        assert_eq!(messages_url(&d), "https://proxy/v1/messages");
    }

    #[test]
    fn max_tokens_defaults() {
        let m = json!([{"role": "user", "content": "hi"}]);
        assert_eq!(
            body(json!({"model": "x", "messages": m, "max_tokens": 77}))["max_tokens"],
            77
        );
        assert_eq!(
            body(json!({"model": "x", "messages": m, "max_completion_tokens": 88}))["max_tokens"],
            88
        );
        let mut d = dep();
        d.model = "claude-unknown-model".into();
        let r = chat_request(&d, &req(json!({"model": "x", "messages": m})), false).unwrap();
        assert_eq!(r.body["max_tokens"], DEFAULT_MAX_TOKENS);
        assert!(
            body(json!({"model": "x", "messages": m, "user": "a@b.c"}))
                .get("metadata")
                .is_none()
        );
    }

    #[test]
    fn system_merging_and_alternation() {
        let b = body(json!({"model": "x", "messages": [
            {"role": "system", "content": "be brief"},
            {"role": "developer", "content": [{"type": "text", "text": "and kind", "cache_control": {"type": "ephemeral"}}]},
            {"role": "assistant", "content": "earlier"},
            {"role": "user", "content": "a"},
            {"role": "user", "content": "b"},
            {"role": "assistant", "content": "Sure:  "}
        ]}));
        assert_eq!(
            b["system"],
            json!([
                {"type": "text", "text": "be brief"},
                {"type": "text", "text": "and kind", "cache_control": {"type": "ephemeral"}}
            ])
        );
        assert_eq!(
            b["messages"],
            json!([
                {"role": "user", "content": [{"type": "text", "text": "."}]},
                {"role": "assistant", "content": [{"type": "text", "text": "earlier"}]},
                {"role": "user", "content": [{"type": "text", "text": "a"}, {"type": "text", "text": "b"}]},
                {"role": "assistant", "content": [{"type": "text", "text": "Sure:"}]}
            ])
        );
        // Only a system prompt: a placeholder user turn is added.
        let b = body(json!({"model": "x", "messages": [{"role": "system", "content": "s"}]}));
        assert_eq!(
            b["messages"],
            json!([{"role": "user", "content": [{"type": "text", "text": "."}]}])
        );
    }

    #[test]
    fn tools_and_tool_round_trip() {
        let b = body(json!({"model": "x",
            "messages": [
                {"role": "user", "content": "weather?"},
                {"role": "assistant", "content": "Let me check.", "tool_calls": [
                    {"id": "call_1", "type": "function", "function": {"name": "get_weather", "arguments": "{\"city\":\"Paris\"}"}},
                    {"id": "call.2", "type": "function", "function": {"name": "get_time", "arguments": ""}}
                ]},
                {"role": "tool", "tool_call_id": "call_1", "content": "sunny"},
                {"role": "tool", "tool_call_id": "call.2", "content": [{"type": "text", "text": "noon"}]},
                {"role": "user", "content": "thanks"}
            ],
            "tools": [
                {"type": "function", "function": {"name": "get_weather", "description": "Weather", "parameters": {"properties": {"city": {"type": "string"}}}}, "cache_control": {"type": "ephemeral"}},
                {"type": "function", "function": {"name": "get_time"}},
                {"type": "web_search_20250305", "name": "web_search", "max_uses": 2}
            ],
            "tool_choice": "required",
            "parallel_tool_calls": false
        }));
        assert_eq!(
            b["tools"],
            json!([
                {"name": "get_weather", "description": "Weather", "input_schema": {"type": "object", "properties": {"city": {"type": "string"}}}, "cache_control": {"type": "ephemeral"}},
                {"name": "get_time", "input_schema": {"type": "object", "properties": {}}},
                {"type": "web_search_20250305", "name": "web_search", "max_uses": 2}
            ])
        );
        assert_eq!(
            b["tool_choice"],
            json!({"type": "any", "disable_parallel_tool_use": true})
        );
        assert_eq!(
            b["messages"][1],
            json!({"role": "assistant", "content": [
                {"type": "text", "text": "Let me check."},
                {"type": "tool_use", "id": "call_1", "name": "get_weather", "input": {"city": "Paris"}},
                {"type": "tool_use", "id": "call_2", "name": "get_time", "input": {}}
            ]})
        );
        assert_eq!(
            b["messages"][2],
            json!({"role": "user", "content": [
                {"type": "tool_result", "tool_use_id": "call_1", "content": "sunny"},
                {"type": "tool_result", "tool_use_id": "call_2", "content": [{"type": "text", "text": "noon"}]},
                {"type": "text", "text": "thanks"}
            ]})
        );
    }

    #[test]
    fn tool_choice_mapping() {
        let tc = |c: Value, p: Option<bool>| {
            translate_tool_choice(Some(&serde_json::from_value(c).unwrap()), p)
        };
        assert_eq!(tc(json!("auto"), None), Some(json!({"type": "auto"})));
        assert_eq!(
            tc(json!("none"), Some(false)),
            Some(json!({"type": "none"}))
        );
        assert_eq!(
            tc(
                json!({"type": "function", "function": {"name": "f"}}),
                Some(true)
            ),
            Some(json!({"type": "tool", "name": "f", "disable_parallel_tool_use": false}))
        );
        assert_eq!(
            translate_tool_choice(None, Some(false)),
            Some(json!({"type": "auto", "disable_parallel_tool_use": true}))
        );
        assert_eq!(translate_tool_choice(None, None), None);
        // tool_choice without tools is dropped.
        let b = body(
            json!({"model": "x", "messages": [{"role": "user", "content": "hi"}], "tool_choice": "auto"}),
        );
        assert!(b.get("tool_choice").is_none());
    }

    #[test]
    fn images_and_documents() {
        let b = body(
            json!({"model": "x", "messages": [{"role": "user", "content": [
                {"type": "image_url", "image_url": {"url": "data:image/png;base64,iVBOR"}},
                {"type": "image_url", "image_url": "https://example.com/cat.jpg", "cache_control": {"type": "ephemeral"}},
                {"type": "image_url", "image_url": {"url": "data:application/pdf;base64,JVBER"}},
                {"type": "file", "file": {"file_data": "data:application/pdf;base64,JVBER", "filename": "a.pdf"}},
                {"type": "file", "file": {"file_id": "file_123"}},
                {"type": "document", "source": {"type": "text", "media_type": "text/plain", "data": "raw"}}
            ]}]}),
        );
        assert_eq!(
            b["messages"][0]["content"],
            json!([
                {"type": "image", "source": {"type": "base64", "media_type": "image/png", "data": "iVBOR"}},
                {"type": "image", "source": {"type": "url", "url": "https://example.com/cat.jpg"}, "cache_control": {"type": "ephemeral"}},
                {"type": "document", "source": {"type": "base64", "media_type": "application/pdf", "data": "JVBER"}},
                {"type": "document", "source": {"type": "base64", "media_type": "application/pdf", "data": "JVBER"}, "title": "a.pdf"},
                {"type": "document", "source": {"type": "file", "file_id": "file_123"}},
                {"type": "document", "source": {"type": "text", "media_type": "text/plain", "data": "raw"}}
            ])
        );
        let bad = req(
            json!({"model": "x", "messages": [{"role": "user", "content": [
            {"type": "input_audio", "input_audio": {"data": "x", "format": "wav"}}]}]}),
        );
        assert_eq!(
            chat_request(&dep(), &bad, false).unwrap_err().kind(),
            crate::ErrorKind::BadRequest
        );
        let bad = req(
            json!({"model": "x", "messages": [{"role": "user", "content": [
            {"type": "image_url", "image_url": "ftp://x"}]}]}),
        );
        assert!(chat_request(&dep(), &bad, false).is_err());
    }

    #[test]
    fn thinking_and_json_mode() {
        let m = json!([{"role": "user", "content": "hi"}]);
        let b = body(json!({"model": "x", "messages": m, "reasoning_effort": "high"}));
        assert_eq!(
            b["thinking"],
            json!({"type": "enabled", "budget_tokens": 4096})
        );
        assert!(b["max_tokens"].as_u64().unwrap() > 4096);
        let b = body(
            json!({"model": "x", "messages": m, "reasoning_effort": "medium", "max_tokens": 1500}),
        );
        assert_eq!(
            b["thinking"],
            json!({"type": "enabled", "budget_tokens": 1499})
        );
        let b = body(
            json!({"model": "x", "messages": m, "reasoning_effort": "low", "max_tokens": 500}),
        );
        assert!(b.get("thinking").is_none(), "budget below minimum");
        let b = body(
            json!({"model": "x", "messages": m, "thinking": {"type": "enabled", "budget_tokens": 2000}, "reasoning_effort": "high"}),
        );
        assert_eq!(b["thinking"]["budget_tokens"], 2000);

        let rf = json!({"type": "json_schema", "json_schema": {"name": "p", "schema": {"properties": {"a": {"type": "integer"}}}}});
        let b = body(json!({"model": "x", "messages": m, "response_format": rf}));
        assert_eq!(
            b["tools"],
            json!([{"name": JSON_TOOL_NAME, "input_schema": {"type": "object", "properties": {"a": {"type": "integer"}}}}])
        );
        assert_eq!(
            b["tool_choice"],
            json!({"type": "tool", "name": JSON_TOOL_NAME})
        );
        let b =
            body(json!({"model": "x", "messages": m, "response_format": {"type": "json_object"}}));
        assert!(b.get("tools").is_none());
    }

    #[test]
    fn thinking_blocks_replayed_first() {
        let b = body(json!({"model": "x", "messages": [
            {"role": "user", "content": "q"},
            {"role": "assistant", "content": null,
             "thinking_blocks": [{"type": "thinking", "thinking": "hmm", "signature": "sig"}],
             "tool_calls": [{"id": "toolu_1", "type": "function", "function": {"name": "f", "arguments": "{}"}}]},
            {"role": "tool", "tool_call_id": "toolu_1", "content": "ok"}
        ]}));
        assert_eq!(
            b["messages"][1]["content"][0],
            json!({"type": "thinking", "thinking": "hmm", "signature": "sig"})
        );
        assert_eq!(b["messages"][1]["content"][1]["type"], "tool_use");
    }

    #[test]
    fn response_translation() {
        let r = req(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}]}));
        let resp = parse_chat(&dep(), &r, &json!({
            "id": "msg_01", "type": "message", "role": "assistant", "model": "claude-3-5-sonnet-20241022",
            "content": [
                {"type": "thinking", "thinking": "Let me think", "signature": "s"},
                {"type": "text", "text": "Checking."},
                {"type": "tool_use", "id": "toolu_1", "name": "get_weather", "input": {"city": "Paris"}}
            ],
            "stop_reason": "tool_use",
            "usage": {"input_tokens": 10, "output_tokens": 5, "cache_creation_input_tokens": 3, "cache_read_input_tokens": 2}
        }).to_string()).unwrap();
        assert_eq!(resp.id, "msg_01");
        assert_eq!(resp.model, "claude-3-5-sonnet-20241022");
        let c = &resp.choices[0];
        assert_eq!(c.finish_reason.as_deref(), Some("tool_calls"));
        assert_eq!(c.message.text(), "Checking.");
        assert_eq!(c.message.reasoning_content.as_deref(), Some("Let me think"));
        assert_eq!(c.message.extra["thinking_blocks"][0]["signature"], "s");
        let calls = c.message.tool_calls.as_ref().unwrap();
        assert_eq!(
            calls[0],
            ToolCall::function("toolu_1", "get_weather", "{\"city\":\"Paris\"}")
        );
        let u = resp.usage.unwrap();
        assert_eq!(
            (u.prompt_tokens, u.completion_tokens, u.total_tokens),
            (15, 5, 20)
        );
        assert_eq!(u.prompt_tokens_details.unwrap().cached_tokens, Some(2));
        assert_eq!(
            (u.cache_creation_input_tokens, u.cache_read_input_tokens),
            (Some(3), Some(2))
        );

        let only_tool = parse_chat(
            &dep(),
            &r,
            &json!({"id": "m", "model": "c", "content": [
            {"type": "tool_use", "id": "t", "name": "f", "input": {}}], "stop_reason": "tool_use"})
            .to_string(),
        )
        .unwrap();
        assert!(only_tool.choices[0].message.content.is_none());
        for (reason, expected) in [
            ("end_turn", "stop"),
            ("max_tokens", "length"),
            ("stop_sequence", "stop"),
            ("refusal", "content_filter"),
        ] {
            let resp = parse_chat(&dep(), &r, &json!({"id": "m", "model": "c", "content": [{"type": "text", "text": "x"}], "stop_reason": reason}).to_string()).unwrap();
            assert_eq!(resp.choices[0].finish_reason.as_deref(), Some(expected));
        }
        assert!(parse_chat(&dep(), &r, "{}").is_err());
    }

    #[test]
    fn json_mode_response() {
        let r = req(
            json!({"model": "x", "messages": [{"role": "user", "content": "hi"}],
            "response_format": {"type": "json_schema", "json_schema": {"name": "p", "schema": {"type": "object"}}}}),
        );
        let resp = parse_chat(&dep(), &r, &json!({"id": "m", "model": "c", "content": [
            {"type": "tool_use", "id": "t", "name": JSON_TOOL_NAME, "input": {"a": 1}}], "stop_reason": "tool_use"}).to_string()).unwrap();
        assert_eq!(resp.choices[0].message.text(), "{\"a\":1}");
        assert!(resp.choices[0].message.tool_calls.is_none());
        assert_eq!(resp.choices[0].finish_reason.as_deref(), Some("stop"));
    }

    fn stream_req() -> ChatRequest {
        req(json!({"model": "x", "messages": [{"role": "user", "content": "hi"}]}))
    }

    #[test]
    fn stream_text_and_usage() {
        let chunks = translate_all(AnthropicStream::new(&dep(), &stream_req()), &[
            ("message_start", r#"{"type":"message_start","message":{"id":"msg_1","type":"message","role":"assistant","model":"claude-x","content":[],"usage":{"input_tokens":25,"output_tokens":1,"cache_read_input_tokens":5}}}"#),
            ("content_block_start", r#"{"type":"content_block_start","index":0,"content_block":{"type":"text","text":""}}"#),
            ("ping", r#"{"type":"ping"}"#),
            ("content_block_delta", r#"{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"Hello"}}"#),
            ("content_block_delta", r#"{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":" world"}}"#),
            ("content_block_stop", r#"{"type":"content_block_stop","index":0}"#),
            ("message_delta", r#"{"type":"message_delta","delta":{"stop_reason":"end_turn","stop_sequence":null},"usage":{"output_tokens":15}}"#),
            ("message_stop", r#"{"type":"message_stop"}"#),
        ]).unwrap();
        assert_eq!(chunks.len(), 5);
        assert_eq!(chunks[0].choices[0].delta.role, Some(Role::Assistant));
        assert_eq!(chunks[1].choices[0].delta.content.as_deref(), Some("Hello"));
        assert_eq!(
            chunks[2].choices[0].delta.content.as_deref(),
            Some(" world")
        );
        assert_eq!(chunks[3].choices[0].finish_reason.as_deref(), Some("stop"));
        assert!(chunks[4].is_usage_only());
        let u = chunks[4].usage.as_ref().unwrap();
        assert_eq!(
            (u.prompt_tokens, u.completion_tokens, u.total_tokens),
            (30, 15, 45)
        );
        assert!(
            chunks
                .iter()
                .all(|c| c.id == "msg_1" && c.model == "claude-x")
        );
    }

    #[test]
    fn stream_tool_calls() {
        let chunks = translate_all(AnthropicStream::new(&dep(), &stream_req()), &[
            ("", r#"{"type":"message_start","message":{"id":"msg_2","model":"c","usage":{"input_tokens":10,"output_tokens":1}}}"#),
            ("", r#"{"type":"content_block_start","index":0,"content_block":{"type":"thinking","thinking":""}}"#),
            ("", r#"{"type":"content_block_delta","index":0,"delta":{"type":"thinking_delta","thinking":"hmm"}}"#),
            ("", r#"{"type":"content_block_delta","index":0,"delta":{"type":"signature_delta","signature":"x"}}"#),
            ("", r#"{"type":"content_block_stop","index":0}"#),
            ("", r#"{"type":"content_block_start","index":1,"content_block":{"type":"tool_use","id":"toolu_A","name":"get_weather","input":{}}}"#),
            ("", r#"{"type":"content_block_delta","index":1,"delta":{"type":"input_json_delta","partial_json":""}}"#),
            ("", r#"{"type":"content_block_delta","index":1,"delta":{"type":"input_json_delta","partial_json":"{\"city\":"}}"#),
            ("", r#"{"type":"content_block_delta","index":1,"delta":{"type":"input_json_delta","partial_json":"\"Paris\"}"}}"#),
            ("", r#"{"type":"content_block_stop","index":1}"#),
            ("", r#"{"type":"content_block_start","index":2,"content_block":{"type":"tool_use","id":"toolu_B","name":"get_time","input":{}}}"#),
            ("", r#"{"type":"content_block_stop","index":2}"#),
            ("", r#"{"type":"message_delta","delta":{"stop_reason":"tool_use"},"usage":{"output_tokens":40}}"#),
            ("", r#"{"type":"message_stop"}"#),
        ]).unwrap();
        let deltas: Vec<&ToolCallDelta> = chunks
            .iter()
            .filter_map(|c| c.choices.first()?.delta.tool_calls.as_ref()?.first())
            .collect();
        assert_eq!(deltas.len(), 5);
        assert_eq!(
            (deltas[0].index, deltas[0].id.as_deref()),
            (0, Some("toolu_A"))
        );
        assert_eq!(
            deltas[0].function.as_ref().unwrap().name.as_deref(),
            Some("get_weather")
        );
        let args: String = deltas[..3]
            .iter()
            .filter_map(|d| d.function.as_ref()?.arguments.clone())
            .collect();
        assert_eq!(args, "{\"city\":\"Paris\"}");
        assert_eq!(
            (deltas[3].index, deltas[3].id.as_deref()),
            (1, Some("toolu_B"))
        );
        assert_eq!(
            deltas[4].function.as_ref().unwrap().arguments.as_deref(),
            Some("{}")
        );
        assert_eq!(
            chunks[1].choices[0].delta.reasoning_content.as_deref(),
            Some("hmm")
        );
        let finish = chunks
            .iter()
            .find_map(|c| c.choices.first()?.finish_reason.clone());
        assert_eq!(finish.as_deref(), Some("tool_calls"));
        assert_eq!(
            chunks
                .last()
                .unwrap()
                .usage
                .as_ref()
                .unwrap()
                .completion_tokens,
            40
        );
    }

    #[test]
    fn stream_json_mode_becomes_content() {
        let r = req(
            json!({"model": "x", "messages": [{"role": "user", "content": "hi"}],
            "response_format": {"type": "json_schema", "json_schema": {"name": "p", "schema": {"type": "object"}}}}),
        );
        let chunks = translate_all(AnthropicStream::new(&dep(), &r), &[
            ("", r#"{"type":"content_block_start","index":0,"content_block":{"type":"tool_use","id":"t","name":"json_tool_call","input":{}}}"#),
            ("", r#"{"type":"content_block_delta","index":0,"delta":{"type":"input_json_delta","partial_json":"{\"a\":1}"}}"#),
            ("", r#"{"type":"content_block_stop","index":0}"#),
            ("", r#"{"type":"message_delta","delta":{"stop_reason":"tool_use"},"usage":{"output_tokens":3}}"#),
            ("", r#"{"type":"message_stop"}"#),
        ]).unwrap();
        assert_eq!(
            chunks[0].choices[0].delta.content.as_deref(),
            Some("{\"a\":1}")
        );
        assert_eq!(chunks[1].choices[0].finish_reason.as_deref(), Some("stop"));
    }

    #[test]
    fn stream_errors() {
        let err = translate_all(AnthropicStream::new(&dep(), &stream_req()), &[
            ("", r#"{"type":"message_start","message":{"id":"m","model":"c","usage":{"input_tokens":1}}}"#),
            ("error", r#"{"type":"error","error":{"type":"overloaded_error","message":"Overloaded"}}"#),
        ]).unwrap_err();
        assert_eq!((err.status_code(), err.message()), (529, "Overloaded"));
        assert!(err.is_retryable());
        let err = translate_all(
            AnthropicStream::new(&dep(), &stream_req()),
            &[(
                "",
                r#"{"type":"message_start","message":{"id":"m","model":"c"}}"#,
            )],
        )
        .unwrap_err();
        assert_eq!(err.kind(), crate::ErrorKind::Connection);
    }
}
