//! Anthropic's Messages API as an inbound format (LiteLLM's
//! `LiteLLMAnthropicMessagesAdapter`): a `/v1/messages` request becomes a
//! [`ChatRequest`], and the chat response or chunk stream becomes a Messages
//! response or Anthropic's SSE events.
//!
//! Request translation:
//!
//! * `system` (a string or text blocks) -> a `system` message;
//! * text blocks -> text parts; `image` blocks (base64 or URL source) ->
//!   `image_url` parts; `document` blocks (base64 PDF etc. or file id) ->
//!   `file` parts, plain-text documents -> text; other blocks (search
//!   results, server tool blocks, ...) pass through as native parts, which
//!   only the Anthropic adapter understands;
//! * `tool_use` blocks -> assistant `tool_calls`; `tool_result` blocks ->
//!   `role: tool` messages ahead of the rest of the user turn;
//! * `thinking` / `redacted_thinking` blocks of earlier turns ->
//!   `thinking_blocks`, which the Anthropic adapter replays;
//! * `tools` (`input_schema`) -> function tools; server tools (`type:
//!   web_search_20250305`, ...) pass through; `tool_choice` `auto`/`any`/
//!   `tool`/`none` -> `auto`/`required`/named/`none`, and
//!   `disable_parallel_tool_use` -> `parallel_tool_calls: false`;
//! * `stop_sequences` -> `stop`, `max_tokens` -> `max_completion_tokens`,
//!   `metadata.user_id` -> `user`, `top_k` and `thinking` are kept for
//!   upstreams that understand them, and `thinking.budget_tokens` also sets
//!   `reasoning_effort` for the others;
//! * `cache_control` markers are kept on messages, parts and tools.
//!
//! Upstreams that are not Anthropic lose the native fields through
//! [`super::adapt_to_target`].

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

use super::FormatError;
use crate::providers::gen_id;
use crate::tokens::estimate_prompt_tokens;
use crate::types::{
    ChatChunk, ChatMessage, ChatRequest, ChatResponse, ContentPart, FileContent, JsonObject,
    MessageContent, Stop, StreamOptions, Tool, ToolCall, ToolChoice, Usage, finish_reason,
};

/// `POST /v1/messages` (and `/v1/messages/count_tokens`) request body.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct MessagesRequest {
    pub model: String,
    pub messages: Vec<InputMessage>,
    /// A string or a list of text blocks.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub system: Option<Value>,
    /// Required by Anthropic; the gateway fills in a default when missing.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_tokens: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stop_sequences: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stream: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub temperature: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub top_p: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub top_k: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tools: Option<Vec<Value>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_choice: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thinking: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metadata: Option<Value>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

impl MessagesRequest {
    pub fn is_stream(&self) -> bool {
        self.stream == Some(true)
    }
}

/// One input message: `role` and a string or a list of content blocks.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct InputMessage {
    pub role: String,
    pub content: Value,
}

/// Native Messages API fields forwarded to upstreams that understand them.
const PASSTHROUGH_FIELDS: &[&str] = &[
    "service_tier",
    "container",
    "mcp_servers",
    "context_management",
];

/// `thinking.budget_tokens` -> `reasoning_effort`, the inverse of the
/// budgets the Anthropic and Gemini adapters use for each effort.
pub fn effort_for_budget(budget: u64) -> &'static str {
    match budget {
        0..=1024 => "low",
        1025..=2048 => "medium",
        _ => "high",
    }
}

/// Translate a Messages request to a chat completion request.
pub fn to_chat_request(req: &MessagesRequest) -> Result<ChatRequest, FormatError> {
    let mut messages = Vec::new();
    if let Some(system) = &req.system
        && let Some(m) = system_message(system)?
    {
        messages.push(m);
    }
    for (i, m) in req.messages.iter().enumerate() {
        let at = format!("messages.{i}");
        let blocks = blocks_of(&m.content, &format!("{at}.content"))?;
        match m.role.as_str() {
            "user" => user_messages(&blocks, &at, &mut messages)?,
            "assistant" => {
                if let Some(msg) = assistant_message(&blocks, &at)? {
                    messages.push(msg);
                }
            }
            other => {
                return Err(FormatError::new(format!(
                    "{at}.role: unexpected role {other:?}; expected \"user\" or \"assistant\""
                ))
                .param(format!("{at}.role")));
            }
        }
    }

    let mut chat = ChatRequest {
        model: req.model.clone(),
        messages,
        temperature: req.temperature,
        top_p: req.top_p,
        max_completion_tokens: req.max_tokens,
        ..ChatRequest::default()
    };
    if let Some(stops) = req.stop_sequences.as_ref().filter(|s| !s.is_empty()) {
        chat.stop = Some(Stop::Many(stops.clone()));
    }
    if req.is_stream() {
        chat.stream = Some(true);
        chat.stream_options = Some(StreamOptions {
            include_usage: Some(true),
            extra: JsonObject::new(),
        });
    }
    if let Some(tools) = &req.tools {
        let tools = tools
            .iter()
            .enumerate()
            .map(|(i, t)| tool(t, i))
            .collect::<Result<Vec<_>, _>>()?;
        if !tools.is_empty() {
            chat.tools = Some(tools);
        }
    }
    if let Some(tc) = &req.tool_choice {
        let (choice, parallel) = tool_choice(tc)?;
        chat.tool_choice = choice;
        chat.parallel_tool_calls = parallel;
    }
    if let Some(thinking) = &req.thinking {
        if thinking.get("type").and_then(Value::as_str) == Some("enabled")
            && let Some(budget) = thinking.get("budget_tokens").and_then(Value::as_u64)
        {
            chat.reasoning_effort = Some(effort_for_budget(budget).to_owned());
        }
        chat.extra.insert("thinking".into(), thinking.clone());
    }
    if let Some(k) = req.top_k {
        chat.extra.insert("top_k".into(), json!(k));
    }
    if let Some(user) = req
        .metadata
        .as_ref()
        .and_then(|m| m.get("user_id"))
        .and_then(Value::as_str)
        .filter(|u| !u.is_empty())
    {
        chat.user = Some(user.to_owned());
    }
    for f in PASSTHROUGH_FIELDS {
        if let Some(v) = req.extra.get(*f) {
            chat.extra.insert((*f).to_owned(), v.clone());
        }
    }
    if let Some(Value::String(mock)) = req.extra.get("mock_response") {
        chat.mock_response = Some(mock.clone());
    }
    Ok(chat)
}

/// The prompt-size estimate of a `count_tokens` request.
pub fn count_tokens(req: &MessagesRequest) -> Result<u64, FormatError> {
    Ok(estimate_prompt_tokens(&to_chat_request(req)?))
}

/// Content as blocks: a string is one text block.
fn blocks_of(content: &Value, at: &str) -> Result<Vec<Value>, FormatError> {
    match content {
        Value::String(s) => Ok(vec![json!({"type": "text", "text": s})]),
        Value::Array(blocks) => {
            for (j, b) in blocks.iter().enumerate() {
                if b.get("type").and_then(Value::as_str).is_none() {
                    return Err(FormatError::new(format!("{at}.{j}.type: Field required"))
                        .param(format!("{at}.{j}.type")));
                }
            }
            Ok(blocks.clone())
        }
        _ => Err(FormatError::new(format!(
            "{at}: expected a string or a list of content blocks"
        ))
        .param(at)),
    }
}

fn kind(b: &Value) -> &str {
    b.get("type").and_then(Value::as_str).unwrap_or_default()
}

fn cache_control(b: &Value) -> Option<&Value> {
    b.get("cache_control").filter(|c| !c.is_null())
}

fn with_cache_control(mut part: ContentPart, b: &Value) -> ContentPart {
    if let Some(cc) = cache_control(b) {
        part.extra.insert("cache_control".into(), cc.clone());
    }
    part
}

fn system_message(system: &Value) -> Result<Option<ChatMessage>, FormatError> {
    let blocks = blocks_of(system, "system")?;
    let parts: Vec<ContentPart> = blocks
        .iter()
        .filter(|b| kind(b) == "text")
        .filter_map(|b| {
            let text = b.get("text").and_then(Value::as_str)?;
            (!text.is_empty()).then(|| with_cache_control(ContentPart::text(text), b))
        })
        .collect();
    Ok(content_of(parts).map(|content| ChatMessage {
        content: Some(content),
        ..ChatMessage::system("")
    }))
}

/// Parts as message content: plain text when that loses nothing.
fn content_of(parts: Vec<ContentPart>) -> Option<MessageContent> {
    match parts.as_slice() {
        [] => None,
        [p] if p.kind == "text" && p.extra.is_empty() => {
            Some(MessageContent::Text(p.text.clone().unwrap_or_default()))
        }
        _ => Some(MessageContent::Parts(parts)),
    }
}

/// A native block kept as is (only the Anthropic adapter understands it).
fn native_part(b: &Value, at: &str) -> Result<ContentPart, FormatError> {
    serde_json::from_value(b.clone())
        .map_err(|e| FormatError::new(format!("{at}: invalid content block: {e}")).param(at))
}

fn data_url(source: &Value) -> Option<String> {
    let media = source.get("media_type").and_then(Value::as_str)?;
    let data = source.get("data").and_then(Value::as_str)?;
    Some(format!("data:{media};base64,{data}"))
}

/// One user content block that is not a `tool_result`.
fn user_part(b: &Value, at: &str) -> Result<Option<ContentPart>, FormatError> {
    let source = b.get("source").unwrap_or(&Value::Null);
    let source_type = source.get("type").and_then(Value::as_str);
    let part = match (kind(b), source_type) {
        ("text", _) => match b.get("text").and_then(Value::as_str) {
            Some("") => return Ok(None),
            Some(t) => ContentPart::text(t),
            None => {
                return Err(FormatError::new(format!("{at}.text: Field required"))
                    .param(format!("{at}.text")));
            }
        },
        ("image", Some("base64")) => match data_url(source) {
            Some(url) => ContentPart::image_url(url),
            None => {
                return Err(FormatError::new(format!(
                    "{at}.source: base64 sources need media_type and data"
                ))
                .param(format!("{at}.source")));
            }
        },
        ("image", Some("url")) => match source.get("url").and_then(Value::as_str) {
            Some(url) => ContentPart::image_url(url),
            None => {
                return Err(FormatError::new(format!("{at}.source.url: Field required"))
                    .param(format!("{at}.source.url")));
            }
        },
        ("document", Some("base64")) => {
            let file_data = data_url(source).ok_or_else(|| {
                FormatError::new(format!(
                    "{at}.source: base64 sources need media_type and data"
                ))
                .param(format!("{at}.source"))
            })?;
            file_part(FileContent {
                file_data: Some(file_data),
                filename: b.get("title").and_then(Value::as_str).map(str::to_owned),
                ..FileContent::default()
            })
        }
        ("document", Some("text")) => {
            let text = source
                .get("data")
                .and_then(Value::as_str)
                .unwrap_or_default();
            match b.get("title").and_then(Value::as_str) {
                Some(title) => ContentPart::text(format!("{title}\n\n{text}")),
                None => ContentPart::text(text),
            }
        }
        ("document" | "image", Some("file")) => match source.get("file_id").and_then(Value::as_str)
        {
            Some(id) => file_part(FileContent {
                file_id: Some(id.to_owned()),
                ..FileContent::default()
            }),
            None => native_part(b, at)?,
        },
        _ => native_part(b, at)?,
    };
    Ok(Some(with_cache_control(part, b)))
}

fn file_part(file: FileContent) -> ContentPart {
    let mut p = ContentPart::text("");
    p.kind = "file".into();
    p.text = None;
    p.file = Some(file);
    p
}

/// A user turn: its `tool_result` blocks become `role: tool` messages, the
/// rest one user message after them.
fn user_messages(
    blocks: &[Value],
    at: &str,
    out: &mut Vec<ChatMessage>,
) -> Result<(), FormatError> {
    let mut parts = Vec::new();
    for (j, b) in blocks.iter().enumerate() {
        let at = format!("{at}.content.{j}");
        if kind(b) == "tool_result" {
            out.push(tool_message(b, &at)?);
        } else if let Some(p) = user_part(b, &at)? {
            parts.push(p);
        }
    }
    if let Some(content) = content_of(parts) {
        out.push(ChatMessage {
            content: Some(content),
            ..ChatMessage::user("")
        });
    }
    Ok(())
}

fn tool_message(b: &Value, at: &str) -> Result<ChatMessage, FormatError> {
    let id = b
        .get("tool_use_id")
        .and_then(Value::as_str)
        .ok_or_else(|| {
            FormatError::new(format!("{at}.tool_use_id: Field required"))
                .param(format!("{at}.tool_use_id"))
        })?;
    let content = match b.get("content") {
        None | Some(Value::Null) => MessageContent::Text(String::new()),
        Some(Value::String(s)) => MessageContent::Text(s.clone()),
        Some(Value::Array(blocks)) => {
            let mut parts = Vec::new();
            for (k, inner) in blocks.iter().enumerate() {
                if let Some(p) = user_part(inner, &format!("{at}.content.{k}"))? {
                    parts.push(p);
                }
            }
            if parts.iter().all(|p| p.kind == "text" && p.extra.is_empty()) {
                let texts: Vec<&str> = parts.iter().filter_map(|p| p.text.as_deref()).collect();
                MessageContent::Text(texts.join("\n"))
            } else {
                MessageContent::Parts(parts)
            }
        }
        Some(_) => {
            return Err(FormatError::new(format!(
                "{at}.content: expected a string or a list of content blocks"
            ))
            .param(format!("{at}.content")));
        }
    };
    let mut m = ChatMessage::tool(id, "");
    m.content = Some(content);
    if let Some(cc) = cache_control(b) {
        m.extra.insert("cache_control".into(), cc.clone());
    }
    Ok(m)
}

fn assistant_message(blocks: &[Value], at: &str) -> Result<Option<ChatMessage>, FormatError> {
    let mut parts = Vec::new();
    let mut tool_calls = Vec::new();
    let mut thinking_blocks = Vec::new();
    for (j, b) in blocks.iter().enumerate() {
        let at = format!("{at}.content.{j}");
        match kind(b) {
            "text" => {
                if let Some(t) = b
                    .get("text")
                    .and_then(Value::as_str)
                    .filter(|t| !t.is_empty())
                {
                    parts.push(with_cache_control(ContentPart::text(t), b));
                }
            }
            "tool_use" => {
                let id = b.get("id").and_then(Value::as_str).unwrap_or_default();
                let name = b.get("name").and_then(Value::as_str).ok_or_else(|| {
                    FormatError::new(format!("{at}.name: Field required"))
                        .param(format!("{at}.name"))
                })?;
                let input = b.get("input").cloned().unwrap_or_else(|| json!({}));
                let mut call = ToolCall::function(id, name, input.to_string());
                if let Some(cc) = cache_control(b) {
                    call.extra.insert("cache_control".into(), cc.clone());
                }
                tool_calls.push(call);
            }
            "thinking" | "redacted_thinking" => thinking_blocks.push(b.clone()),
            _ => parts.push(native_part(b, &at)?),
        }
    }
    if parts.is_empty() && tool_calls.is_empty() && thinking_blocks.is_empty() {
        return Ok(None);
    }
    let mut m = ChatMessage::assistant("");
    m.content = content_of(parts);
    if !tool_calls.is_empty() {
        m.tool_calls = Some(tool_calls);
    }
    if !thinking_blocks.is_empty() {
        m.extra
            .insert("thinking_blocks".into(), Value::Array(thinking_blocks));
    }
    Ok(Some(m))
}

fn tool(t: &Value, i: usize) -> Result<Tool, FormatError> {
    let at = format!("tools.{i}");
    let Value::Object(obj) = t else {
        return Err(FormatError::new(format!("{at}: expected an object")).param(at));
    };
    match obj.get("type").and_then(Value::as_str) {
        None | Some("custom") => {
            let name = obj.get("name").and_then(Value::as_str).ok_or_else(|| {
                FormatError::new(format!("{at}.name: Field required")).param(format!("{at}.name"))
            })?;
            let schema = obj
                .get("input_schema")
                .cloned()
                .unwrap_or_else(|| json!({"type": "object", "properties": {}}));
            let description = obj
                .get("description")
                .and_then(Value::as_str)
                .map(str::to_owned);
            let mut tool = Tool::function(name, description, Some(schema));
            if let Some(cc) = cache_control(t) {
                tool.extra.insert("cache_control".into(), cc.clone());
            }
            Ok(tool)
        }
        // Server tools (`web_search_20250305`, `bash_20250124`, ...).
        Some(kind) => {
            let mut extra = obj.clone();
            extra.remove("type");
            Ok(Tool {
                kind: kind.to_owned(),
                function: None,
                extra,
            })
        }
    }
}

fn tool_choice(tc: &Value) -> Result<(Option<ToolChoice>, Option<bool>), FormatError> {
    let bad = || {
        FormatError::new(
            "tool_choice: expected {\"type\": \"auto\" | \"any\" | \"tool\" | \"none\"}",
        )
        .param("tool_choice")
    };
    let kind = tc.get("type").and_then(Value::as_str).ok_or_else(bad)?;
    let choice = match kind {
        "auto" => ToolChoice::Mode("auto".into()),
        "any" => ToolChoice::Mode("required".into()),
        "none" => ToolChoice::Mode("none".into()),
        "tool" => {
            let name = tc.get("name").and_then(Value::as_str).ok_or_else(|| {
                FormatError::new("tool_choice.name: Field required").param("tool_choice.name")
            })?;
            ToolChoice::named(name)
        }
        _ => return Err(bad()),
    };
    let parallel = tc
        .get("disable_parallel_tool_use")
        .and_then(Value::as_bool)
        .map(|disable| !disable);
    Ok((Some(choice), parallel))
}

// ---------------------------------------------------------------------------
// Responses

/// OpenAI `finish_reason` -> Anthropic `stop_reason`.
pub fn stop_reason(finish: Option<&str>) -> &'static str {
    match finish {
        Some(finish_reason::LENGTH) => "max_tokens",
        Some(finish_reason::TOOL_CALLS | finish_reason::FUNCTION_CALL) => "tool_use",
        Some(finish_reason::CONTENT_FILTER) => "refusal",
        _ => "end_turn",
    }
}

/// Anthropic usage: `input_tokens` excludes cache reads and writes, which
/// OpenAI's `prompt_tokens` includes.
pub fn usage(u: &Usage) -> Value {
    let details = u.prompt_tokens_details.as_ref();
    let cache_read = u
        .cache_read_input_tokens
        .or(details.and_then(|d| d.cached_tokens))
        .unwrap_or(0);
    let cache_creation = u
        .cache_creation_input_tokens
        .or(details.and_then(|d| d.cache_creation_tokens))
        .unwrap_or(0);
    json!({
        "input_tokens": u.prompt_tokens.saturating_sub(cache_read + cache_creation),
        "output_tokens": u.completion_tokens,
        "cache_creation_input_tokens": cache_creation,
        "cache_read_input_tokens": cache_read,
    })
}

fn message_id(chat_id: &str) -> String {
    if chat_id.starts_with("msg_") {
        chat_id.to_owned()
    } else if chat_id.is_empty() {
        gen_id("msg_")
    } else {
        format!("msg_{}", chat_id.trim_start_matches("chatcmpl-"))
    }
}

/// Parse tool-call arguments into the object Anthropic's `input` needs.
fn tool_input(arguments: &str) -> Value {
    match serde_json::from_str::<Value>(arguments) {
        Ok(v @ Value::Object(_)) => v,
        _ if arguments.trim().is_empty() => json!({}),
        // Not an object: keep what the model produced, visibly.
        _ => json!({"arguments": arguments}),
    }
}

/// A chat completion as a Messages response. `model` is the model the
/// client asked for.
pub fn from_chat_response(resp: &ChatResponse, model: &str) -> Value {
    let mut content = Vec::new();
    let choice = resp.choices.first();
    if let Some(m) = choice.map(|c| &c.message) {
        match m.extra.get("thinking_blocks") {
            Some(Value::Array(blocks)) if !blocks.is_empty() => {
                content.extend(blocks.iter().cloned())
            }
            _ => {
                if let Some(r) = m.reasoning_content.as_deref().filter(|r| !r.is_empty()) {
                    content.push(json!({"type": "thinking", "thinking": r, "signature": ""}));
                }
            }
        }
        let text = m.text();
        if !text.is_empty() {
            content.push(json!({"type": "text", "text": text}));
        }
        if let Some(r) = m.refusal.as_deref().filter(|r| !r.is_empty()) {
            content.push(json!({"type": "text", "text": r}));
        }
        for call in m.tool_calls.iter().flatten() {
            content.push(json!({
                "type": "tool_use",
                "id": call.id,
                "name": call.function.name,
                "input": tool_input(&call.function.arguments),
            }));
        }
    }
    let has_tools = content.iter().any(|b| b["type"] == "tool_use");
    let finish = choice.and_then(|c| c.finish_reason.as_deref());
    let stop = match (finish, has_tools) {
        (None | Some(finish_reason::STOP), true) => "tool_use",
        (f, _) => stop_reason(f),
    };
    json!({
        "id": message_id(&resp.id),
        "type": "message",
        "role": "assistant",
        "model": model,
        "content": content,
        "stop_reason": stop,
        "stop_sequence": null,
        "usage": usage(&resp.usage.clone().unwrap_or_default()),
    })
}

/// Anthropic's error `type` for an HTTP status.
pub fn error_type(status: u16) -> &'static str {
    match status {
        400 | 422 => "invalid_request_error",
        401 => "authentication_error",
        402 => "billing_error",
        403 => "permission_error",
        404 => "not_found_error",
        408 | 504 => "timeout_error",
        413 => "request_too_large",
        429 => "rate_limit_error",
        503 | 529 => "overloaded_error",
        _ => "api_error",
    }
}

/// `{"type": "error", "error": {"type", "message"}}`.
pub fn error_body(status: u16, message: &str) -> Value {
    json!({"type": "error", "error": {"type": error_type(status), "message": message}})
}

// ---------------------------------------------------------------------------
// Streaming

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Open {
    Text,
    Thinking,
    /// A tool call, by its OpenAI `index`.
    Tool(u32),
}

/// Turns a chat chunk stream into Anthropic's SSE events: `message_start`,
/// `ping`, per block `content_block_start` / `content_block_delta`
/// (`text_delta`, `thinking_delta`, `input_json_delta`) /
/// `content_block_stop`, then `message_delta` (with `stop_reason` and the
/// final usage) and `message_stop`. A failure becomes an `error` event.
#[derive(Debug)]
pub struct MessagesStream {
    model: String,
    id: Option<String>,
    input_estimate: u64,
    started: bool,
    next_index: u32,
    open: Option<(u32, Open)>,
    /// OpenAI tool index -> block index.
    tools: HashMap<u32, u32>,
    finish: Option<String>,
    usage: Option<Usage>,
    output_chars: u64,
    done: bool,
}

impl MessagesStream {
    /// `model` is the model the client asked for; `input_estimate` the
    /// prompt estimate reported in `message_start` (the upstream's count
    /// arrives with the last chunk and is reported in `message_delta`).
    pub fn new(model: impl Into<String>, input_estimate: u64) -> Self {
        Self {
            model: model.into(),
            id: None,
            input_estimate,
            started: false,
            next_index: 0,
            open: None,
            tools: HashMap::new(),
            finish: None,
            usage: None,
            output_chars: 0,
            done: false,
        }
    }

    fn start(&mut self, out: &mut Vec<Value>) {
        if self.started {
            return;
        }
        self.started = true;
        let id = message_id(self.id.as_deref().unwrap_or_default());
        self.id = Some(id.clone());
        out.push(json!({
            "type": "message_start",
            "message": {
                "id": id,
                "type": "message",
                "role": "assistant",
                "model": self.model,
                "content": [],
                "stop_reason": null,
                "stop_sequence": null,
                "usage": {
                    "input_tokens": self.input_estimate,
                    "output_tokens": 0,
                    "cache_creation_input_tokens": 0,
                    "cache_read_input_tokens": 0,
                },
            },
        }));
        out.push(json!({"type": "ping"}));
    }

    fn close(&mut self, out: &mut Vec<Value>) {
        if let Some((index, _)) = self.open.take() {
            out.push(json!({"type": "content_block_stop", "index": index}));
        }
    }

    /// Make `kind` the open block, opening it with `block` if needed;
    /// returns its index.
    fn ensure(&mut self, kind: Open, block: impl FnOnce() -> Value, out: &mut Vec<Value>) -> u32 {
        if let Some((index, open)) = self.open
            && open == kind
        {
            return index;
        }
        self.close(out);
        let index = self.next_index;
        self.next_index += 1;
        self.open = Some((index, kind));
        out.push(json!({"type": "content_block_start", "index": index, "content_block": block()}));
        index
    }

    fn delta(index: u32, delta: Value) -> Value {
        json!({"type": "content_block_delta", "index": index, "delta": delta})
    }

    /// The events for one chunk (`message_start` first, on the first one).
    pub fn on_chunk(&mut self, chunk: &ChatChunk) -> Vec<Value> {
        let mut out = Vec::new();
        if self.done {
            return out;
        }
        if self.id.is_none() && !chunk.id.is_empty() {
            self.id = Some(chunk.id.clone());
        }
        self.start(&mut out);
        if let Some(u) = &chunk.usage {
            self.usage = Some(u.clone());
        }
        let Some(choice) = chunk.choices.iter().find(|c| c.index == 0) else {
            return out;
        };
        let d = &choice.delta;
        if let Some(r) = d.reasoning_content.as_deref().filter(|r| !r.is_empty()) {
            self.output_chars += r.len() as u64;
            let i = self.ensure(
                Open::Thinking,
                || json!({"type": "thinking", "thinking": "", "signature": ""}),
                &mut out,
            );
            out.push(Self::delta(
                i,
                json!({"type": "thinking_delta", "thinking": r}),
            ));
        }
        for text in [d.content.as_deref(), d.refusal.as_deref()]
            .into_iter()
            .flatten()
        {
            if text.is_empty() {
                continue;
            }
            self.output_chars += text.len() as u64;
            let i = self.ensure(Open::Text, || json!({"type": "text", "text": ""}), &mut out);
            out.push(Self::delta(i, json!({"type": "text_delta", "text": text})));
        }
        for tc in d.tool_calls.iter().flatten() {
            let f = tc.function.as_ref();
            let block = match self.tools.get(&tc.index) {
                Some(&b) => b,
                None => {
                    let id = tc.id.clone().unwrap_or_else(|| gen_id("toolu_"));
                    let name = f.and_then(|f| f.name.clone()).unwrap_or_default();
                    self.close(&mut out);
                    let b = self.ensure(
                        Open::Tool(tc.index),
                        || json!({"type": "tool_use", "id": id, "name": name, "input": {}}),
                        &mut out,
                    );
                    self.tools.insert(tc.index, b);
                    b
                }
            };
            if let Some(args) = f
                .and_then(|f| f.arguments.as_deref())
                .filter(|a| !a.is_empty())
            {
                self.output_chars += args.len() as u64;
                out.push(Self::delta(
                    block,
                    json!({"type": "input_json_delta", "partial_json": args}),
                ));
            }
        }
        if let Some(f) = &choice.finish_reason {
            self.finish = Some(f.clone());
        }
        out
    }

    /// The closing events once the chunk stream ended.
    pub fn finish(&mut self) -> Vec<Value> {
        let mut out = Vec::new();
        if self.done {
            return out;
        }
        self.start(&mut out);
        self.close(&mut out);
        self.done = true;
        let stop = match (self.finish.as_deref(), self.tools.is_empty()) {
            (None | Some(finish_reason::STOP), false) => "tool_use",
            (f, _) => stop_reason(f),
        };
        let u = self
            .usage
            .clone()
            .unwrap_or_else(|| Usage::new(self.input_estimate, self.output_chars.div_ceil(4)));
        out.push(json!({
            "type": "message_delta",
            "delta": {"stop_reason": stop, "stop_sequence": null},
            "usage": usage(&u),
        }));
        out.push(json!({"type": "message_stop"}));
        out
    }

    /// The stream failed: an `error` event, and nothing after it.
    pub fn error(&mut self, status: u16, message: &str) -> Vec<Value> {
        if self.done {
            return Vec::new();
        }
        self.done = true;
        vec![error_body(status, message)]
    }
}

/// Events as SSE bytes, each named by its `type`.
pub fn encode_events(events: &[Value]) -> String {
    events
        .iter()
        .map(|e| super::sse_event(e["type"].as_str().unwrap_or("message"), e))
        .collect()
}

#[cfg(test)]
mod tests;
