//! OpenAI-compatible wire types: Chat Completions (request, response, stream
//! chunk), Embeddings, and the OpenAI error body.
//!
//! These types are the lingua franca of the gateway: clients speak them, and
//! every provider adapter translates from/to them. They are deliberately
//! permissive:
//!
//! * every object carries a `#[serde(flatten)] extra` map, so fields this crate
//!   does not model (new OpenAI parameters, provider-specific knobs such as
//!   `top_k` or `chat_template_kwargs`) round-trip unchanged to
//!   OpenAI-compatible upstreams and back to clients;
//! * open-ended enumerations (`finish_reason`, tool `type`, content part
//!   `type`) are plain strings, with constants for the well-known values.

use std::borrow::Cow;

use serde::{Deserialize, Deserializer, Serialize};
use serde_json::{Map, Value};

/// A JSON object, used for pass-through fields.
pub type JsonObject = Map<String, Value>;

/// Well-known values of `finish_reason`.
pub mod finish_reason {
    pub const STOP: &str = "stop";
    pub const LENGTH: &str = "length";
    pub const TOOL_CALLS: &str = "tool_calls";
    pub const CONTENT_FILTER: &str = "content_filter";
    pub const FUNCTION_CALL: &str = "function_call";
}

// ---------------------------------------------------------------------------
// Chat Completions request
// ---------------------------------------------------------------------------

/// `POST /v1/chat/completions` request body.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ChatRequest {
    pub model: String,
    pub messages: Vec<ChatMessage>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub temperature: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub top_p: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub n: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stream: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stream_options: Option<StreamOptions>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stop: Option<Stop>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_tokens: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_completion_tokens: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub presence_penalty: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub frequency_penalty: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub logit_bias: Option<JsonObject>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub logprobs: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub top_logprobs: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub seed: Option<i64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub user: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tools: Option<Vec<Tool>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_choice: Option<ToolChoice>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parallel_tool_calls: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub response_format: Option<ResponseFormat>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reasoning_effort: Option<String>,
    /// LiteLLM extension: return this canned completion without calling the
    /// upstream (see [`crate::Client::chat`]). Never forwarded upstream.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mock_response: Option<String>,
    /// Every other field, forwarded verbatim to OpenAI-compatible upstreams.
    #[serde(flatten)]
    pub extra: JsonObject,
}

impl ChatRequest {
    /// Whether the client asked for a streamed response.
    pub fn is_stream(&self) -> bool {
        self.stream == Some(true)
    }

    /// Whether the client asked for the trailing usage chunk
    /// (`stream_options.include_usage`). Adapters always request usage from
    /// the upstream so spend can be tracked; the server should drop the
    /// usage-only chunk before forwarding when this returns `false`.
    pub fn wants_stream_usage(&self) -> bool {
        self.stream_options.as_ref().and_then(|o| o.include_usage) == Some(true)
    }

    /// `max_completion_tokens`, falling back to the legacy `max_tokens`.
    pub fn max_output_tokens(&self) -> Option<u64> {
        self.max_completion_tokens.or(self.max_tokens)
    }
}

/// `stream_options` request field.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct StreamOptions {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub include_usage: Option<bool>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// `stop`: a single sequence or a list of them.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Stop {
    One(String),
    Many(Vec<String>),
}

impl Stop {
    pub fn to_vec(&self) -> Vec<String> {
        match self {
            Stop::One(s) => vec![s.clone()],
            Stop::Many(v) => v.clone(),
        }
    }
}

/// Message author role.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    System,
    Developer,
    User,
    Assistant,
    Tool,
    /// Legacy function-calling result message.
    Function,
}

/// One chat message (request) or the assistant message of a response choice.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ChatMessage {
    pub role: Role,
    /// `null` is legal for assistant messages that only carry tool calls.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub content: Option<MessageContent>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_calls: Option<Vec<ToolCall>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_call_id: Option<String>,
    /// Legacy single function call on an assistant message.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function_call: Option<FunctionCall>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub refusal: Option<String>,
    /// Reasoning / thinking text (LiteLLM convention), on responses.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reasoning_content: Option<String>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

impl ChatMessage {
    fn with_text(role: Role, text: impl Into<String>) -> Self {
        Self {
            role,
            content: Some(MessageContent::Text(text.into())),
            name: None,
            tool_calls: None,
            tool_call_id: None,
            function_call: None,
            refusal: None,
            reasoning_content: None,
            extra: JsonObject::new(),
        }
    }

    pub fn system(text: impl Into<String>) -> Self {
        Self::with_text(Role::System, text)
    }

    pub fn user(text: impl Into<String>) -> Self {
        Self::with_text(Role::User, text)
    }

    pub fn assistant(text: impl Into<String>) -> Self {
        Self::with_text(Role::Assistant, text)
    }

    /// A `role: "tool"` result for the given tool call.
    pub fn tool(tool_call_id: impl Into<String>, text: impl Into<String>) -> Self {
        Self {
            tool_call_id: Some(tool_call_id.into()),
            ..Self::with_text(Role::Tool, text)
        }
    }

    /// Concatenated text of the message content (empty if none).
    pub fn text(&self) -> Cow<'_, str> {
        self.content
            .as_ref()
            .map_or(Cow::Borrowed(""), MessageContent::text)
    }
}

/// Message content: a plain string or an array of typed parts.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum MessageContent {
    Text(String),
    Parts(Vec<ContentPart>),
}

impl MessageContent {
    /// Concatenation of all text (string content or `text` parts).
    pub fn text(&self) -> Cow<'_, str> {
        match self {
            MessageContent::Text(s) => Cow::Borrowed(s),
            MessageContent::Parts(parts) => {
                let texts: Vec<&str> = parts.iter().filter_map(|p| p.text.as_deref()).collect();
                match texts.as_slice() {
                    [] => Cow::Borrowed(""),
                    [one] => Cow::Borrowed(one),
                    many => Cow::Owned(many.concat()),
                }
            }
        }
    }

    /// The content as a list of parts (a string becomes one `text` part).
    pub fn parts(&self) -> Cow<'_, [ContentPart]> {
        match self {
            MessageContent::Text(s) => Cow::Owned(vec![ContentPart::text(s.clone())]),
            MessageContent::Parts(p) => Cow::Borrowed(p),
        }
    }
}

/// Well-known content part `type` values.
pub mod part_type {
    pub const TEXT: &str = "text";
    pub const IMAGE_URL: &str = "image_url";
    pub const INPUT_AUDIO: &str = "input_audio";
    pub const FILE: &str = "file";
}

/// One element of an array `content`.
///
/// Modelled as a struct with optional payload fields rather than an enum so
/// that unknown part types (and unknown fields such as Anthropic's
/// `cache_control`) survive a round trip.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ContentPart {
    #[serde(rename = "type")]
    pub kind: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub text: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub image_url: Option<ImageUrl>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input_audio: Option<InputAudio>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file: Option<FileContent>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

impl ContentPart {
    fn empty(kind: &str) -> Self {
        Self {
            kind: kind.to_owned(),
            text: None,
            image_url: None,
            input_audio: None,
            file: None,
            extra: JsonObject::new(),
        }
    }

    pub fn text(text: impl Into<String>) -> Self {
        Self {
            text: Some(text.into()),
            ..Self::empty(part_type::TEXT)
        }
    }

    pub fn image_url(url: impl Into<String>) -> Self {
        Self {
            image_url: Some(ImageUrl {
                url: url.into(),
                detail: None,
                format: None,
            }),
            ..Self::empty(part_type::IMAGE_URL)
        }
    }
}

/// `image_url` payload. Accepts the bare-string form LiteLLM also accepts.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ImageUrl {
    /// `https://...` or `data:<mime>;base64,<data>`.
    pub url: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    /// LiteLLM extension: explicit MIME type for the image.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub format: Option<String>,
}

impl<'de> Deserialize<'de> for ImageUrl {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        struct Obj {
            url: String,
            #[serde(default)]
            detail: Option<String>,
            #[serde(default)]
            format: Option<String>,
        }
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Repr {
            Url(String),
            Obj(Obj),
        }
        Ok(match Repr::deserialize(d)? {
            Repr::Url(url) => ImageUrl {
                url,
                detail: None,
                format: None,
            },
            Repr::Obj(o) => ImageUrl {
                url: o.url,
                detail: o.detail,
                format: o.format,
            },
        })
    }
}

/// `input_audio` payload.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct InputAudio {
    /// Base64-encoded audio.
    pub data: String,
    /// `wav`, `mp3`, ...
    pub format: String,
}

/// `file` payload.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct FileContent {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file_id: Option<String>,
    /// `data:<mime>;base64,<data>`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file_data: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub filename: Option<String>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// A tool the model may call.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Tool {
    /// `"function"` for function tools.
    #[serde(rename = "type", default = "function_type")]
    pub kind: String,
    /// Present for `function` tools; other tool types keep their payload in
    /// `extra` and are only supported by OpenAI-compatible upstreams.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function: Option<FunctionDefinition>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

fn function_type() -> String {
    "function".to_owned()
}

impl Tool {
    /// A function tool.
    pub fn function(
        name: impl Into<String>,
        description: Option<String>,
        parameters: Option<Value>,
    ) -> Self {
        Self {
            kind: function_type(),
            function: Some(FunctionDefinition {
                name: name.into(),
                description,
                parameters,
                strict: None,
                extra: JsonObject::new(),
            }),
            extra: JsonObject::new(),
        }
    }
}

/// Function tool definition.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FunctionDefinition {
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
    /// JSON Schema of the arguments object.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parameters: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub strict: Option<bool>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// `tool_choice`: `"none" | "auto" | "required"` or a named function.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ToolChoice {
    Mode(String),
    Named(NamedToolChoice),
}

impl ToolChoice {
    pub fn named(name: impl Into<String>) -> Self {
        ToolChoice::Named(NamedToolChoice {
            kind: function_type(),
            function: Some(ToolChoiceFunction { name: name.into() }),
            extra: JsonObject::new(),
        })
    }
}

/// `{"type": "function", "function": {"name": ...}}`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NamedToolChoice {
    #[serde(rename = "type", default = "function_type")]
    pub kind: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function: Option<ToolChoiceFunction>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ToolChoiceFunction {
    pub name: String,
}

/// A tool call made by the assistant.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ToolCall {
    pub id: String,
    #[serde(rename = "type", default = "function_type")]
    pub kind: String,
    pub function: FunctionCall,
    #[serde(flatten)]
    pub extra: JsonObject,
}

impl ToolCall {
    pub fn function(
        id: impl Into<String>,
        name: impl Into<String>,
        arguments: impl Into<String>,
    ) -> Self {
        Self {
            id: id.into(),
            kind: function_type(),
            function: FunctionCall {
                name: name.into(),
                arguments: arguments.into(),
            },
            extra: JsonObject::new(),
        }
    }
}

/// Function name plus JSON-encoded arguments.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FunctionCall {
    pub name: String,
    /// JSON-encoded arguments object, as a string.
    #[serde(default)]
    pub arguments: String,
}

/// `response_format`: `text`, `json_object`, or `json_schema`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ResponseFormat {
    #[serde(rename = "type")]
    pub kind: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub json_schema: Option<JsonSchemaFormat>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct JsonSchemaFormat {
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub schema: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub strict: Option<bool>,
}

// ---------------------------------------------------------------------------
// Chat Completions response
// ---------------------------------------------------------------------------

/// Non-streaming `chat.completion` response.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ChatResponse {
    pub id: String,
    #[serde(default = "chat_completion_object")]
    pub object: String,
    #[serde(default)]
    pub created: u64,
    pub model: String,
    pub choices: Vec<Choice>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage: Option<Usage>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub system_fingerprint: Option<String>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

fn chat_completion_object() -> String {
    "chat.completion".to_owned()
}

/// One response choice.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Choice {
    #[serde(default)]
    pub index: u32,
    pub message: ChatMessage,
    /// See [`finish_reason`]. Always serialized (may be `null`).
    #[serde(default)]
    pub finish_reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub logprobs: Option<Value>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// Token accounting.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Usage {
    /// Total input tokens, *including* cached / cache-creation tokens.
    #[serde(default)]
    pub prompt_tokens: u64,
    #[serde(default)]
    pub completion_tokens: u64,
    #[serde(default)]
    pub total_tokens: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prompt_tokens_details: Option<PromptTokensDetails>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub completion_tokens_details: Option<CompletionTokensDetails>,
    /// Anthropic-style cache accounting (LiteLLM exposes both shapes).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cache_creation_input_tokens: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cache_read_input_tokens: Option<u64>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

impl Usage {
    /// Usage with only the three totals set.
    pub fn new(prompt_tokens: u64, completion_tokens: u64) -> Self {
        Self {
            prompt_tokens,
            completion_tokens,
            total_tokens: prompt_tokens + completion_tokens,
            ..Self::default()
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PromptTokensDetails {
    /// Tokens served from the provider's prompt cache.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cached_tokens: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub audio_tokens: Option<u64>,
    /// Tokens written to the provider's prompt cache (Anthropic).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cache_creation_tokens: Option<u64>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompletionTokensDetails {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reasoning_tokens: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub audio_tokens: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub accepted_prediction_tokens: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rejected_prediction_tokens: Option<u64>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

// ---------------------------------------------------------------------------
// Streaming
// ---------------------------------------------------------------------------

/// One `chat.completion.chunk` of a streamed response.
///
/// The final chunk of every stream produced by this crate carries `usage`
/// (with empty `choices`) whenever the upstream reports usage.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ChatChunk {
    pub id: String,
    #[serde(default = "chat_chunk_object")]
    pub object: String,
    #[serde(default)]
    pub created: u64,
    #[serde(default)]
    pub model: String,
    #[serde(default)]
    pub choices: Vec<ChunkChoice>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage: Option<Usage>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub system_fingerprint: Option<String>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

fn chat_chunk_object() -> String {
    "chat.completion.chunk".to_owned()
}

impl ChatChunk {
    /// A chunk with no choices; fill in `choices` / `usage`.
    pub fn new(id: impl Into<String>, model: impl Into<String>, created: u64) -> Self {
        Self {
            id: id.into(),
            object: chat_chunk_object(),
            created,
            model: model.into(),
            choices: Vec::new(),
            usage: None,
            system_fingerprint: None,
            extra: JsonObject::new(),
        }
    }

    /// Builder: set a single choice at index 0.
    pub fn with_delta(mut self, delta: Delta, finish_reason: Option<String>) -> Self {
        self.choices = vec![ChunkChoice {
            index: 0,
            delta,
            finish_reason,
            logprobs: None,
            extra: JsonObject::new(),
        }];
        self
    }

    /// Builder: set usage.
    pub fn with_usage(mut self, usage: Usage) -> Self {
        self.usage = Some(usage);
        self
    }

    /// True for the trailing chunk that only carries usage.
    pub fn is_usage_only(&self) -> bool {
        self.choices.is_empty() && self.usage.is_some()
    }
}

/// One choice of a stream chunk.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ChunkChoice {
    #[serde(default)]
    pub index: u32,
    #[serde(default)]
    pub delta: Delta,
    /// Always serialized (`null` until the last content chunk).
    #[serde(default)]
    pub finish_reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub logprobs: Option<Value>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// Incremental message content.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Delta {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub role: Option<Role>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub content: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_calls: Option<Vec<ToolCallDelta>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reasoning_content: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub refusal: Option<String>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// Incremental tool call. `id`, `type` and `function.name` arrive on the first
/// delta of a call; later deltas append to `function.arguments`.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ToolCallDelta {
    pub index: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    #[serde(rename = "type", default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function: Option<FunctionCallDelta>,
}

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct FunctionCallDelta {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub arguments: Option<String>,
}

// ---------------------------------------------------------------------------
// Embeddings
// ---------------------------------------------------------------------------

/// `POST /v1/embeddings` request body.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EmbeddingRequest {
    pub model: String,
    pub input: EmbeddingInput,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub encoding_format: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dimensions: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub user: Option<String>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// Embedding input: text(s) or pre-tokenized input(s).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum EmbeddingInput {
    Text(String),
    Texts(Vec<String>),
    Tokens(Vec<u32>),
    TokenBatches(Vec<Vec<u32>>),
}

impl EmbeddingInput {
    /// Number of inputs (embeddings that will be returned).
    pub fn len(&self) -> usize {
        match self {
            EmbeddingInput::Text(_) | EmbeddingInput::Tokens(_) => 1,
            EmbeddingInput::Texts(v) => v.len(),
            EmbeddingInput::TokenBatches(v) => v.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The textual inputs, or `None` for pre-tokenized input.
    pub fn texts(&self) -> Option<Vec<&str>> {
        match self {
            EmbeddingInput::Text(s) => Some(vec![s.as_str()]),
            EmbeddingInput::Texts(v) => Some(v.iter().map(String::as_str).collect()),
            EmbeddingInput::Tokens(_) | EmbeddingInput::TokenBatches(_) => None,
        }
    }
}

/// `POST /v1/embeddings` response body.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EmbeddingResponse {
    #[serde(default = "list_object")]
    pub object: String,
    pub data: Vec<Embedding>,
    #[serde(default)]
    pub model: String,
    /// `prompt_tokens` and `total_tokens` are set; `completion_tokens` is 0.
    #[serde(default)]
    pub usage: Usage,
    #[serde(flatten)]
    pub extra: JsonObject,
}

fn list_object() -> String {
    "list".to_owned()
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Embedding {
    #[serde(default = "embedding_object")]
    pub object: String,
    #[serde(default)]
    pub index: u32,
    pub embedding: EmbeddingVector,
}

fn embedding_object() -> String {
    "embedding".to_owned()
}

/// A float vector, or base64 when `encoding_format: "base64"` was requested.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum EmbeddingVector {
    Float(Vec<f64>),
    Base64(String),
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// OpenAI error envelope: `{"error": {"message", "type", "param", "code"}}`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ErrorBody {
    pub error: ErrorDetail,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ErrorDetail {
    pub message: String,
    #[serde(rename = "type", default, deserialize_with = "string_or_number")]
    pub kind: Option<String>,
    #[serde(default, deserialize_with = "string_or_number")]
    pub param: Option<String>,
    /// OpenAI uses strings; some providers send numbers, which are stringified.
    #[serde(default, deserialize_with = "string_or_number")]
    pub code: Option<String>,
}

fn string_or_number<'de, D: Deserializer<'de>>(d: D) -> Result<Option<String>, D::Error> {
    Ok(match Option::<Value>::deserialize(d)? {
        Some(Value::String(s)) => Some(s),
        Some(Value::Number(n)) => Some(n.to_string()),
        Some(Value::Bool(b)) => Some(b.to_string()),
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn request_round_trips_unknown_fields() {
        let raw = json!({
            "model": "gpt-4o",
            "messages": [{"role": "user", "content": "hi", "cache_control": {"type": "ephemeral"}}],
            "top_k": 5,
            "chat_template_kwargs": {"enable_thinking": false},
            "stop": "END",
            "max_tokens": 10,
        });
        let req: ChatRequest = serde_json::from_value(raw.clone()).unwrap();
        assert_eq!(req.extra["top_k"], 5);
        assert_eq!(req.messages[0].extra["cache_control"]["type"], "ephemeral");
        assert_eq!(req.stop, Some(Stop::One("END".into())));
        assert_eq!(serde_json::to_value(&req).unwrap(), raw);
    }

    #[test]
    fn multimodal_content_parts() {
        let raw = json!({"role": "user", "content": [
            {"type": "text", "text": "what is this?"},
            {"type": "image_url", "image_url": {"url": "https://x/y.png", "detail": "low"}},
            {"type": "image_url", "image_url": "data:image/png;base64,AAAA"},
            {"type": "input_audio", "input_audio": {"data": "UklG", "format": "wav"}},
            {"type": "future_part", "payload": 1}
        ]});
        let msg: ChatMessage = serde_json::from_value(raw).unwrap();
        let MessageContent::Parts(parts) = msg.content.as_ref().unwrap() else {
            panic!("expected parts")
        };
        assert_eq!(
            parts[1].image_url.as_ref().unwrap().detail.as_deref(),
            Some("low")
        );
        assert_eq!(
            parts[2].image_url.as_ref().unwrap().url,
            "data:image/png;base64,AAAA"
        );
        assert_eq!(parts[3].input_audio.as_ref().unwrap().format, "wav");
        assert_eq!(parts[4].kind, "future_part");
        assert_eq!(parts[4].extra["payload"], 1);
        assert_eq!(msg.text(), "what is this?");
    }

    #[test]
    fn tools_and_tool_choice() {
        let req: ChatRequest = serde_json::from_value(json!({
            "model": "m",
            "messages": [
                {"role": "assistant", "content": null, "tool_calls": [
                    {"id": "call_1", "type": "function", "function": {"name": "f", "arguments": "{\"a\":1}"}}
                ]},
                {"role": "tool", "tool_call_id": "call_1", "content": "42"}
            ],
            "tools": [{"type": "function", "function": {"name": "f", "parameters": {"type": "object"}}}],
            "tool_choice": {"type": "function", "function": {"name": "f"}},
            "response_format": {"type": "json_schema", "json_schema": {"name": "x", "schema": {"type": "object"}}}
        }))
        .unwrap();
        assert_eq!(req.tool_choice, Some(ToolChoice::named("f")));
        assert_eq!(
            req.messages[0].tool_calls.as_ref().unwrap()[0]
                .function
                .name,
            "f"
        );
        assert!(req.messages[0].content.is_none());
        assert_eq!(req.response_format.unwrap().json_schema.unwrap().name, "x");
        let mode: ToolChoice = serde_json::from_value(json!("required")).unwrap();
        assert_eq!(mode, ToolChoice::Mode("required".into()));
    }

    #[test]
    fn response_and_chunk_shapes() {
        let resp: ChatResponse = serde_json::from_value(json!({
            "id": "x", "object": "chat.completion", "created": 1, "model": "m",
            "choices": [{"index": 0, "message": {"role": "assistant", "content": "hi"}, "finish_reason": "stop"}],
            "usage": {"prompt_tokens": 3, "completion_tokens": 1, "total_tokens": 4,
                      "prompt_tokens_details": {"cached_tokens": 2}},
            "service_tier": "default"
        }))
        .unwrap();
        assert_eq!(
            resp.usage
                .as_ref()
                .unwrap()
                .prompt_tokens_details
                .as_ref()
                .unwrap()
                .cached_tokens,
            Some(2)
        );
        assert_eq!(resp.extra["service_tier"], "default");

        let chunk = ChatChunk::new("c", "m", 1).with_delta(
            Delta {
                content: Some("he".into()),
                ..Delta::default()
            },
            None,
        );
        let v = serde_json::to_value(&chunk).unwrap();
        assert_eq!(v["object"], "chat.completion.chunk");
        assert_eq!(v["choices"][0]["finish_reason"], Value::Null);
        assert!(v.get("usage").is_none());
        assert!(
            ChatChunk::new("c", "m", 1)
                .with_usage(Usage::new(1, 2))
                .is_usage_only()
        );
    }

    #[test]
    fn embeddings_shapes() {
        let req: EmbeddingRequest =
            serde_json::from_value(json!({"model": "e", "input": ["a", "b"], "dimensions": 8}))
                .unwrap();
        assert_eq!(req.input.len(), 2);
        assert_eq!(req.input.texts().unwrap(), vec!["a", "b"]);
        let tokens: EmbeddingInput = serde_json::from_value(json!([1, 2, 3])).unwrap();
        assert_eq!(tokens, EmbeddingInput::Tokens(vec![1, 2, 3]));
        let resp: EmbeddingResponse = serde_json::from_value(json!({
            "object": "list", "model": "e",
            "data": [{"object": "embedding", "index": 0, "embedding": [0.5, -1.0]},
                     {"object": "embedding", "index": 1, "embedding": "AAAA"}],
            "usage": {"prompt_tokens": 2, "total_tokens": 2}
        }))
        .unwrap();
        assert_eq!(
            resp.data[0].embedding,
            EmbeddingVector::Float(vec![0.5, -1.0])
        );
        assert_eq!(
            resp.data[1].embedding,
            EmbeddingVector::Base64("AAAA".into())
        );
        assert_eq!(resp.usage.total_tokens, 2);
    }

    #[test]
    fn error_body_accepts_numeric_code() {
        let e: ErrorBody =
            serde_json::from_value(json!({"error": {"message": "m", "type": "t", "code": 429}}))
                .unwrap();
        assert_eq!(e.error.code.as_deref(), Some("429"));
        assert_eq!(e.error.param, None);
    }
}
