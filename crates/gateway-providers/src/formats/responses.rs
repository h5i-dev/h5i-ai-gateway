//! OpenAI's Responses API as an inbound format, bridged to Chat Completions
//! like LiteLLM's `litellm_completion_transformation`: a `/v1/responses`
//! request becomes a [`ChatRequest`], and the chat response or chunk stream
//! becomes a Response object or the Responses streaming events.
//!
//! Request translation:
//!
//! * `instructions` -> a leading `system` message (not carried over to
//!   later turns, as in OpenAI's API);
//! * `input` as a string -> one user message; as items: messages (`role`
//!   user/system/developer/assistant; parts `input_text`, `input_image`,
//!   `input_file`, `input_audio`, `output_text`, `refusal`) -> chat
//!   messages, `function_call` -> assistant `tool_calls` (consecutive calls
//!   join one assistant turn), `function_call_output` -> `role: tool`;
//!   `reasoning` items are dropped (they have no chat equivalent);
//! * the conversation of `previous_response_id` (kept by the caller) goes
//!   before the new input;
//! * function `tools` -> chat function tools, `tool_choice` likewise;
//!   hosted tools (web search, file search, computer use, ...) are refused;
//! * `max_output_tokens` -> `max_completion_tokens`, `text.format`
//!   (`json_schema`, `json_object`) -> `response_format`,
//!   `reasoning.effort` -> `reasoning_effort`, `temperature`, `top_p`,
//!   `parallel_tool_calls`, `user` as they are.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

use super::FormatError;
use crate::providers::gen_id;
use crate::types::{
    ChatChunk, ChatMessage, ChatRequest, ChatResponse, ContentPart, FileContent, ImageUrl, InputAudio, JsonObject, JsonSchemaFormat, MessageContent,
    ResponseFormat, Role, StreamOptions, Tool, ToolCall, ToolChoice, Usage, finish_reason,
};

/// `POST /v1/responses` request body.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ResponsesRequest {
    pub model: String,
    /// A string or a list of input items.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instructions: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tools: Option<Vec<Value>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_choice: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_output_tokens: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub temperature: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub top_p: Option<f64>,
    /// `{"format": {"type": "text" | "json_object" | "json_schema", ...}}`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub text: Option<Value>,
    /// `{"effort": "low" | "medium" | "high", "summary": ...}`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reasoning: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stream: Option<bool>,
    /// Whether to keep the response for `previous_response_id` and
    /// `GET /v1/responses/{id}`; defaults to `true`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub store: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub previous_response_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parallel_tool_calls: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub user: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metadata: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub background: Option<bool>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

impl ResponsesRequest {
    pub fn is_stream(&self) -> bool {
        self.stream == Some(true)
    }

    /// Whether the response is to be stored (the default).
    pub fn stores(&self) -> bool {
        self.store != Some(false)
    }
}

/// A translated request.
#[derive(Debug, Clone, PartialEq)]
pub struct Translated {
    pub chat: ChatRequest,
    /// The history and this request's input, without `instructions`: what a
    /// later `previous_response_id` continues from (with the output added).
    pub conversation: Vec<ChatMessage>,
}

/// Translate a Responses request, continuing `history` (the conversation
/// of `previous_response_id`, if any).
pub fn to_chat_request(req: &ResponsesRequest, history: &[ChatMessage]) -> Result<Translated, FormatError> {
    if req.background == Some(true) {
        return Err(FormatError::new("background responses are not supported").param("background"));
    }
    let mut conversation = history.to_vec();
    match &req.input {
        None | Some(Value::Null) => {}
        Some(Value::String(s)) => conversation.push(ChatMessage::user(s.clone())),
        Some(Value::Array(items)) => append_items(items, &mut conversation)?,
        Some(_) => {
            return Err(FormatError::new("input: expected a string or a list of items").param("input"));
        }
    }
    let mut messages = Vec::with_capacity(conversation.len() + 1);
    if let Some(i) = req.instructions.as_deref().filter(|i| !i.is_empty()) {
        messages.push(ChatMessage::system(i));
    }
    messages.extend(conversation.iter().cloned());

    let mut chat = ChatRequest {
        model: req.model.clone(),
        messages,
        temperature: req.temperature,
        top_p: req.top_p,
        max_completion_tokens: req.max_output_tokens,
        parallel_tool_calls: req.parallel_tool_calls,
        user: req.user.clone(),
        ..ChatRequest::default()
    };
    if req.is_stream() {
        chat.stream = Some(true);
        chat.stream_options = Some(StreamOptions { include_usage: Some(true), extra: JsonObject::new() });
    }
    if let Some(tools) = &req.tools {
        let tools = tools.iter().enumerate().map(|(i, t)| tool(t, i)).collect::<Result<Vec<_>, _>>()?;
        if !tools.is_empty() {
            chat.tools = Some(tools);
        }
    }
    if let Some(tc) = &req.tool_choice {
        chat.tool_choice = Some(tool_choice(tc)?);
    }
    if let Some(format) = req.text.as_ref().and_then(|t| t.get("format")) {
        chat.response_format = response_format(format)?;
    }
    if let Some(effort) = req.reasoning.as_ref().and_then(|r| r.get("effort")).and_then(Value::as_str) {
        chat.reasoning_effort = Some(effort.to_owned());
    }
    if let Some(Value::String(mock)) = req.extra.get("mock_response") {
        chat.mock_response = Some(mock.clone());
    }
    Ok(Translated { chat, conversation })
}

fn item_type(item: &Value) -> &str {
    match item.get("type").and_then(Value::as_str) {
        Some(t) => t,
        // EasyInputMessage: `{"role", "content"}` without a type.
        None if item.get("role").is_some() => "message",
        None => "",
    }
}

fn field<'a>(item: &'a Value, name: &str, at: &str) -> Result<&'a str, FormatError> {
    item.get(name).and_then(Value::as_str).ok_or_else(|| FormatError::new(format!("{at}.{name}: Field required")).param(format!("{at}.{name}")))
}

/// Append input items to `out` as chat messages.
fn append_items(items: &[Value], out: &mut Vec<ChatMessage>) -> Result<(), FormatError> {
    for (i, item) in items.iter().enumerate() {
        let at = format!("input.{i}");
        match item_type(item) {
            "message" => out.push(message(item, &at)?),
            "function_call" => {
                let call_id = item
                    .get("call_id")
                    .or_else(|| item.get("id"))
                    .and_then(Value::as_str)
                    .ok_or_else(|| FormatError::new(format!("{at}.call_id: Field required")).param(format!("{at}.call_id")))?;
                let name = field(item, "name", &at)?;
                let arguments = item.get("arguments").and_then(Value::as_str).unwrap_or("{}");
                let call = ToolCall::function(call_id, name, arguments);
                // Calls of one turn join the assistant message before them.
                match out.last_mut() {
                    Some(m) if m.role == Role::Assistant => m.tool_calls.get_or_insert_with(Vec::new).push(call),
                    _ => {
                        let mut m = ChatMessage::assistant("");
                        m.content = None;
                        m.tool_calls = Some(vec![call]);
                        out.push(m);
                    }
                }
            }
            "function_call_output" => {
                let call_id = field(item, "call_id", &at)?;
                let content = match item.get("output") {
                    Some(Value::String(s)) => MessageContent::Text(s.clone()),
                    Some(Value::Array(parts)) => parts_content(parts, &format!("{at}.output"))?,
                    Some(other) if !other.is_null() => MessageContent::Text(other.to_string()),
                    _ => {
                        return Err(FormatError::new(format!("{at}.output: Field required")).param(format!("{at}.output")));
                    }
                };
                let mut m = ChatMessage::tool(call_id, "");
                m.content = Some(content);
                out.push(m);
            }
            // Reasoning has no chat equivalent; the model re-derives it.
            "reasoning" => {}
            "" => {
                return Err(FormatError::new(format!("{at}.type: Field required")).param(format!("{at}.type")));
            }
            other => {
                return Err(FormatError::new(format!("{at}: input items of type {other:?} are not supported")).param(format!("{at}.type")));
            }
        }
    }
    Ok(())
}

fn message(item: &Value, at: &str) -> Result<ChatMessage, FormatError> {
    let role = match field(item, "role", at)? {
        "user" => Role::User,
        "system" => Role::System,
        "developer" => Role::Developer,
        "assistant" => Role::Assistant,
        other => {
            return Err(FormatError::new(format!("{at}.role: unexpected role {other:?}")).param(format!("{at}.role")));
        }
    };
    let content = match item.get("content") {
        Some(Value::String(s)) => MessageContent::Text(s.clone()),
        Some(Value::Array(parts)) => parts_content(parts, &format!("{at}.content"))?,
        _ => {
            return Err(FormatError::new(format!("{at}.content: expected a string or a list of content parts")).param(format!("{at}.content")));
        }
    };
    let mut m = ChatMessage::user("");
    m.role = role;
    m.content = Some(match (role, content) {
        // Assistant history is text.
        (Role::Assistant, c) => MessageContent::Text(c.text().into_owned()),
        (_, c) => c,
    });
    Ok(m)
}

/// Content parts as chat content: plain text when there are only texts.
fn parts_content(parts: &[Value], at: &str) -> Result<MessageContent, FormatError> {
    let parts = parts.iter().enumerate().map(|(j, p)| part(p, &format!("{at}.{j}"))).collect::<Result<Vec<_>, _>>()?;
    if parts.iter().all(|p| p.kind == "text") {
        let texts: Vec<&str> = parts.iter().filter_map(|p| p.text.as_deref()).collect();
        Ok(MessageContent::Text(texts.concat()))
    } else {
        Ok(MessageContent::Parts(parts))
    }
}

fn part(p: &Value, at: &str) -> Result<ContentPart, FormatError> {
    let kind = p.get("type").and_then(Value::as_str).unwrap_or_default();
    let mut out = ContentPart::text("");
    out.text = None;
    match kind {
        "input_text" | "output_text" | "text" => out.text = Some(field(p, "text", at)?.to_owned()),
        "refusal" => out.text = Some(field(p, "refusal", at)?.to_owned()),
        "input_image" => {
            let url = match (p.get("image_url").and_then(Value::as_str), p.get("file_id").and_then(Value::as_str)) {
                (Some(url), _) => url,
                (None, Some(id)) => {
                    out.kind = "file".into();
                    out.file = Some(FileContent { file_id: Some(id.to_owned()), ..FileContent::default() });
                    return Ok(out);
                }
                (None, None) => {
                    return Err(FormatError::new(format!("{at}: input_image needs image_url or file_id")).param(format!("{at}.image_url")));
                }
            };
            out.kind = "image_url".into();
            out.image_url = Some(ImageUrl {
                url: url.to_owned(),
                detail: p.get("detail").and_then(Value::as_str).filter(|d| *d != "auto").map(str::to_owned),
                format: None,
            });
        }
        "input_file" => {
            if p.get("file_url").is_some() && p.get("file_data").is_none() && p.get("file_id").is_none() {
                return Err(FormatError::new(format!("{at}.file_url: file URLs are not supported; send file_data or file_id"))
                    .param(format!("{at}.file_url")));
            }
            let get = |k: &str| p.get(k).and_then(Value::as_str).map(str::to_owned);
            let file = FileContent { file_id: get("file_id"), file_data: get("file_data"), filename: get("filename"), extra: JsonObject::new() };
            if file.file_id.is_none() && file.file_data.is_none() {
                return Err(FormatError::new(format!("{at}: input_file needs file_data or file_id")).param(format!("{at}.file_data")));
            }
            out.kind = "file".into();
            out.file = Some(file);
        }
        "input_audio" => {
            let audio = p.get("input_audio").unwrap_or(p);
            out.kind = "input_audio".into();
            out.input_audio = Some(InputAudio { data: field(audio, "data", at)?.to_owned(), format: field(audio, "format", at)?.to_owned() });
        }
        other => {
            return Err(FormatError::new(format!("{at}: content parts of type {other:?} are not supported")).param(format!("{at}.type")));
        }
    }
    Ok(out)
}

fn tool(t: &Value, i: usize) -> Result<Tool, FormatError> {
    let at = format!("tools.{i}");
    match t.get("type").and_then(Value::as_str) {
        Some("function") => {
            let name = field(t, "name", &at)?;
            let description = t.get("description").and_then(Value::as_str).map(str::to_owned);
            let parameters = t.get("parameters").filter(|p| !p.is_null()).cloned();
            let mut tool = Tool::function(name, description, parameters);
            if let (Some(f), Some(strict)) = (&mut tool.function, t.get("strict").and_then(Value::as_bool)) {
                f.strict = Some(strict);
            }
            Ok(tool)
        }
        other => Err(FormatError::new(format!(
            "{at}: tools of type {} are not supported (only function tools are bridged to chat completions)",
            other.map_or_else(|| "<missing>".to_owned(), |t| format!("{t:?}"))
        ))
        .param(format!("{at}.type"))),
    }
}

fn tool_choice(tc: &Value) -> Result<ToolChoice, FormatError> {
    match tc {
        Value::String(m) if matches!(m.as_str(), "auto" | "none" | "required") => Ok(ToolChoice::Mode(m.clone())),
        Value::Object(o) => match o.get("type").and_then(Value::as_str) {
            Some("function") => Ok(ToolChoice::named(field(tc, "name", "tool_choice")?)),
            Some("allowed_tools") => Ok(ToolChoice::Mode(o.get("mode").and_then(Value::as_str).unwrap_or("auto").to_owned())),
            _ => Err(FormatError::new("tool_choice: only \"auto\", \"none\", \"required\" and function choices are supported").param("tool_choice")),
        },
        _ => Err(FormatError::new("tool_choice: expected \"auto\", \"none\", \"required\" or {\"type\": \"function\", \"name\": ...}")
            .param("tool_choice")),
    }
}

fn response_format(format: &Value) -> Result<Option<ResponseFormat>, FormatError> {
    let kind = format.get("type").and_then(Value::as_str).unwrap_or("text");
    Ok(match kind {
        "text" => None,
        "json_object" => Some(ResponseFormat { kind: kind.into(), json_schema: None, extra: JsonObject::new() }),
        "json_schema" => Some(ResponseFormat {
            kind: kind.into(),
            json_schema: Some(JsonSchemaFormat {
                name: format.get("name").and_then(Value::as_str).unwrap_or("response").to_owned(),
                description: format.get("description").and_then(Value::as_str).map(str::to_owned),
                schema: format.get("schema").cloned(),
                strict: format.get("strict").and_then(Value::as_bool),
            }),
            extra: JsonObject::new(),
        }),
        other => {
            return Err(FormatError::new(format!("text.format.type: unsupported format {other:?}")).param("text.format.type"));
        }
    })
}

// ---------------------------------------------------------------------------
// Responses

/// A new response id.
pub fn new_response_id() -> String {
    gen_id("resp_")
}

/// Responses usage from chat usage.
pub fn usage(u: &Usage) -> Value {
    let cached = u.prompt_tokens_details.as_ref().and_then(|d| d.cached_tokens).or(u.cache_read_input_tokens).unwrap_or(0);
    let reasoning = u.completion_tokens_details.as_ref().and_then(|d| d.reasoning_tokens).unwrap_or(0);
    json!({
        "input_tokens": u.prompt_tokens,
        "input_tokens_details": {"cached_tokens": cached},
        "output_tokens": u.completion_tokens,
        "output_tokens_details": {"reasoning_tokens": reasoning},
        "total_tokens": u.prompt_tokens + u.completion_tokens,
    })
}

/// `status` and `incomplete_details.reason` for a finish reason.
fn status_for(finish: Option<&str>) -> (&'static str, Option<&'static str>) {
    match finish {
        Some(finish_reason::LENGTH) => ("incomplete", Some("max_output_tokens")),
        Some(finish_reason::CONTENT_FILTER) => ("incomplete", Some("content_filter")),
        _ => ("completed", None),
    }
}

/// Identity of a response: its id and creation time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResponseId {
    pub id: String,
    pub created_at: u64,
}

/// A Response object, echoing the request's parameters.
pub fn response_object(
    req: &ResponsesRequest,
    rid: &ResponseId,
    status: &str,
    output: Vec<Value>,
    usage: Option<Value>,
    incomplete: Option<&str>,
    error: Option<Value>,
) -> Value {
    json!({
        "id": rid.id,
        "object": "response",
        "created_at": rid.created_at,
        "status": status,
        "background": false,
        "error": error,
        "incomplete_details": incomplete.map(|r| json!({"reason": r})),
        "instructions": req.instructions,
        "max_output_tokens": req.max_output_tokens,
        "model": req.model,
        "output": output,
        "parallel_tool_calls": req.parallel_tool_calls.unwrap_or(true),
        "previous_response_id": req.previous_response_id,
        "reasoning": {
            "effort": req.reasoning.as_ref().and_then(|r| r.get("effort")).cloned(),
            "summary": req.reasoning.as_ref().and_then(|r| r.get("summary")).cloned(),
        },
        "store": req.stores(),
        "temperature": req.temperature.unwrap_or(1.0),
        "text": req.text.clone().unwrap_or_else(|| json!({"format": {"type": "text"}})),
        "tool_choice": req.tool_choice.clone().unwrap_or_else(|| json!("auto")),
        "tools": req.tools.clone().unwrap_or_default(),
        "top_p": req.top_p.unwrap_or(1.0),
        "truncation": "disabled",
        "usage": usage,
        "user": req.user,
        "metadata": req.metadata.clone().unwrap_or_else(|| json!({})),
    })
}

fn reasoning_item(id: &str, text: &str) -> Value {
    json!({"type": "reasoning", "id": id, "summary": [{"type": "summary_text", "text": text}]})
}

fn output_text(text: &str) -> Value {
    json!({"type": "output_text", "text": text, "annotations": []})
}

fn message_item(id: &str, status: &str, content: Vec<Value>) -> Value {
    json!({"type": "message", "id": id, "status": status, "role": "assistant", "content": content})
}

fn function_call_item(id: &str, call_id: &str, name: &str, arguments: &str, status: &str) -> Value {
    json!({"type": "function_call", "id": id, "call_id": call_id, "name": name, "arguments": arguments, "status": status})
}

/// A chat completion as a Response object.
pub fn from_chat_response(req: &ResponsesRequest, rid: &ResponseId, resp: &ChatResponse) -> Value {
    let mut output = Vec::new();
    let choice = resp.choices.first();
    if let Some(m) = choice.map(|c| &c.message) {
        if let Some(r) = m.reasoning_content.as_deref().filter(|r| !r.is_empty()) {
            output.push(reasoning_item(&gen_id("rs_"), r));
        }
        let mut content = Vec::new();
        let text = m.text();
        if !text.is_empty() {
            content.push(output_text(&text));
        }
        if let Some(r) = m.refusal.as_deref().filter(|r| !r.is_empty()) {
            content.push(json!({"type": "refusal", "refusal": r}));
        }
        if !content.is_empty() {
            output.push(message_item(&gen_id("msg_"), "completed", content));
        }
        for call in m.tool_calls.iter().flatten() {
            output.push(function_call_item(&gen_id("fc_"), &call.id, &call.function.name, &call.function.arguments, "completed"));
        }
    }
    let (status, incomplete) = status_for(choice.and_then(|c| c.finish_reason.as_deref()));
    let usage = resp.usage.as_ref().map(usage);
    response_object(req, rid, status, output, usage, incomplete, None)
}

/// The chat messages a response's `output` adds to the conversation (for
/// `previous_response_id`). `thinking_blocks` from an Anthropic upstream
/// are attached to the assistant turn so they can be replayed.
pub fn output_messages(response: &Value, thinking_blocks: Option<&Value>) -> Vec<ChatMessage> {
    let mut out = Vec::new();
    if let Some(Value::Array(items)) = response.get("output") {
        // Our own output always translates.
        let _ = append_items(items, &mut out);
    }
    if let Some(tb) = thinking_blocks.filter(|t| t.as_array().is_some_and(|a| !a.is_empty())) {
        match out.iter_mut().find(|m| m.role == Role::Assistant) {
            Some(m) => {
                m.extra.insert("thinking_blocks".into(), tb.clone());
            }
            None => {
                let mut m = ChatMessage::assistant("");
                m.extra.insert("thinking_blocks".into(), tb.clone());
                out.push(m);
            }
        }
    }
    out
}

/// An error in OpenAI's shape, also used for `previous_response_id` misses.
pub fn error_object(code: &str, message: &str) -> Value {
    json!({"code": code, "message": message})
}

// ---------------------------------------------------------------------------
// Streaming

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Open {
    Reasoning,
    Message,
    Tool(u32),
}

/// Turns a chat chunk stream into Responses streaming events, each with a
/// `sequence_number`: `response.created`, `response.in_progress`, per
/// output item `response.output_item.added` ... `response.output_item.done`
/// (messages: `response.content_part.added`, `response.output_text.delta`,
/// `response.output_text.done`, `response.content_part.done`; function
/// calls: `response.function_call_arguments.delta/done`; reasoning:
/// `response.reasoning_summary_part.added`,
/// `response.reasoning_summary_text.delta/done`,
/// `response.reasoning_summary_part.done`), then `response.completed` (or
/// `response.incomplete`). A failure becomes `error` and `response.failed`.
#[derive(Debug)]
pub struct ResponsesStream {
    req: ResponsesRequest,
    rid: ResponseId,
    seq: u64,
    started: bool,
    output: Vec<Value>,
    /// The open item: its output index and kind.
    open: Option<(usize, Open)>,
    /// OpenAI tool index -> output index.
    tools: HashMap<u32, usize>,
    finish: Option<String>,
    usage: Option<Usage>,
    input_estimate: u64,
    output_chars: u64,
    done: bool,
    final_response: Option<Value>,
}

impl ResponsesStream {
    pub fn new(req: ResponsesRequest, rid: ResponseId, input_estimate: u64) -> Self {
        Self {
            req,
            rid,
            seq: 0,
            started: false,
            output: Vec::new(),
            open: None,
            tools: HashMap::new(),
            finish: None,
            usage: None,
            input_estimate,
            output_chars: 0,
            done: false,
            final_response: None,
        }
    }

    /// The finished Response (`completed` or `incomplete`) once the stream
    /// ended normally.
    pub fn final_response(&self) -> Option<&Value> {
        self.final_response.as_ref()
    }

    fn emit(&mut self, out: &mut Vec<Value>, kind: &str, mut event: Value) {
        if let Value::Object(o) = &mut event {
            o.insert("type".into(), json!(kind));
            o.insert("sequence_number".into(), json!(self.seq));
        }
        self.seq += 1;
        out.push(event);
    }

    fn snapshot(&self, status: &str) -> Value {
        response_object(&self.req, &self.rid, status, self.output.clone(), None, None, None)
    }

    fn start(&mut self, out: &mut Vec<Value>) {
        if self.started {
            return;
        }
        self.started = true;
        let r = self.snapshot("in_progress");
        self.emit(out, "response.created", json!({"response": r}));
        self.emit(out, "response.in_progress", json!({"response": r}));
    }

    fn item_id(&self, index: usize) -> String {
        self.output[index]["id"].as_str().unwrap_or_default().to_owned()
    }

    fn close(&mut self, out: &mut Vec<Value>) {
        let Some((index, kind)) = self.open.take() else {
            return;
        };
        let id = self.item_id(index);
        match kind {
            Open::Reasoning => {
                let text = self.output[index]["summary"][0]["text"].clone();
                self.emit(
                    out,
                    "response.reasoning_summary_text.done",
                    json!({"item_id": id, "output_index": index, "summary_index": 0, "text": text}),
                );
                let part = self.output[index]["summary"][0].clone();
                self.emit(
                    out,
                    "response.reasoning_summary_part.done",
                    json!({"item_id": id, "output_index": index, "summary_index": 0, "part": part}),
                );
            }
            Open::Message => {
                let part = self.output[index]["content"][0].clone();
                self.emit(out, "response.output_text.done", json!({"item_id": id, "output_index": index, "content_index": 0, "text": part["text"]}));
                self.emit(out, "response.content_part.done", json!({"item_id": id, "output_index": index, "content_index": 0, "part": part}));
                self.output[index]["status"] = json!("completed");
            }
            Open::Tool(_) => {
                let args = self.output[index]["arguments"].clone();
                self.emit(out, "response.function_call_arguments.done", json!({"item_id": id, "output_index": index, "arguments": args}));
                self.output[index]["status"] = json!("completed");
            }
        }
        let item = self.output[index].clone();
        self.emit(out, "response.output_item.done", json!({"output_index": index, "item": item}));
    }

    /// Make `kind` the open item, adding `item` if needed; its output index.
    fn ensure(&mut self, kind: Open, item: impl FnOnce() -> Value, out: &mut Vec<Value>) -> usize {
        if let Some((index, open)) = self.open
            && open == kind
        {
            return index;
        }
        self.close(out);
        let index = self.output.len();
        let item = item();
        self.output.push(item.clone());
        self.open = Some((index, kind));
        self.emit(out, "response.output_item.added", json!({"output_index": index, "item": item}));
        let id = self.item_id(index);
        match kind {
            Open::Reasoning => {
                self.output[index]["summary"] = json!([{"type": "summary_text", "text": ""}]);
                self.emit(
                    out,
                    "response.reasoning_summary_part.added",
                    json!({"item_id": id, "output_index": index, "summary_index": 0, "part": {"type": "summary_text", "text": ""}}),
                );
            }
            Open::Message => {
                self.output[index]["content"] = json!([output_text("")]);
                self.emit(
                    out,
                    "response.content_part.added",
                    json!({"item_id": id, "output_index": index, "content_index": 0, "part": output_text("")}),
                );
            }
            Open::Tool(_) => {}
        }
        index
    }

    fn append(value: &mut Value, s: &str) {
        let mut text = value.as_str().unwrap_or_default().to_owned();
        text.push_str(s);
        *value = Value::String(text);
    }

    /// The events for one chunk (`response.created` and
    /// `response.in_progress` first, on the first one).
    pub fn on_chunk(&mut self, chunk: &ChatChunk) -> Vec<Value> {
        let mut out = Vec::new();
        if self.done {
            return out;
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
            let i = self.ensure(Open::Reasoning, || json!({"type": "reasoning", "id": gen_id("rs_"), "summary": []}), &mut out);
            Self::append(&mut self.output[i]["summary"][0]["text"], r);
            let id = self.item_id(i);
            self.emit(&mut out, "response.reasoning_summary_text.delta", json!({"item_id": id, "output_index": i, "summary_index": 0, "delta": r}));
        }
        for text in [d.content.as_deref(), d.refusal.as_deref()].into_iter().flatten() {
            if text.is_empty() {
                continue;
            }
            self.output_chars += text.len() as u64;
            let i = self.ensure(Open::Message, || message_item(&gen_id("msg_"), "in_progress", Vec::new()), &mut out);
            Self::append(&mut self.output[i]["content"][0]["text"], text);
            let id = self.item_id(i);
            self.emit(&mut out, "response.output_text.delta", json!({"item_id": id, "output_index": i, "content_index": 0, "delta": text}));
        }
        for tc in d.tool_calls.iter().flatten() {
            let f = tc.function.as_ref();
            let i = match self.tools.get(&tc.index) {
                Some(&i) => i,
                None => {
                    let call_id = tc.id.clone().unwrap_or_else(|| gen_id("call_"));
                    let name = f.and_then(|f| f.name.clone()).unwrap_or_default();
                    self.close(&mut out);
                    let i = self.ensure(Open::Tool(tc.index), || function_call_item(&gen_id("fc_"), &call_id, &name, "", "in_progress"), &mut out);
                    self.tools.insert(tc.index, i);
                    i
                }
            };
            if let Some(args) = f.and_then(|f| f.arguments.as_deref()).filter(|a| !a.is_empty()) {
                self.output_chars += args.len() as u64;
                Self::append(&mut self.output[i]["arguments"], args);
                let id = self.item_id(i);
                self.emit(&mut out, "response.function_call_arguments.delta", json!({"item_id": id, "output_index": i, "delta": args}));
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
        let (status, incomplete) = status_for(self.finish.as_deref());
        let u = self.usage.clone().unwrap_or_else(|| Usage::new(self.input_estimate, self.output_chars.div_ceil(4)));
        let r = response_object(&self.req, &self.rid, status, self.output.clone(), Some(usage(&u)), incomplete, None);
        self.final_response = Some(r.clone());
        let kind = if status == "completed" { "response.completed" } else { "response.incomplete" };
        self.emit(&mut out, kind, json!({"response": r}));
        out
    }

    /// The stream failed: `error`, then `response.failed`.
    pub fn error(&mut self, code: &str, message: &str) -> Vec<Value> {
        let mut out = Vec::new();
        if self.done {
            return out;
        }
        self.start(&mut out);
        self.done = true;
        self.emit(&mut out, "error", json!({"code": code, "message": message, "param": null}));
        let r = response_object(&self.req, &self.rid, "failed", self.output.clone(), None, None, Some(error_object(code, message)));
        self.emit(&mut out, "response.failed", json!({"response": r}));
        out
    }
}

/// Events as SSE bytes, each named by its `type`.
pub fn encode_events(events: &[Value]) -> String {
    events.iter().map(|e| super::sse_event(e["type"].as_str().unwrap_or("message"), e)).collect()
}

#[cfg(test)]
mod tests;
