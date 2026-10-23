//! LLM provider adapters for h5i-ai-gateway — the trusted data plane.
//!
//! This crate speaks the OpenAI Chat Completions / Embeddings wire format
//! ([`types`]) to the gateway and translates to and from each upstream
//! provider (OpenAI-compatible, Azure, Anthropic, Gemini, Amazon Bedrock,
//! Google Vertex AI), including streaming. It makes no policy decisions: keys,
//! budgets, rate limits, routing and retries live in the server.
//!
//! ```no_run
//! # async fn demo() -> Result<(), gateway_providers::ProviderError> {
//! use gateway_providers::{ChatRequest, Client, Deployment, HttpSettings};
//! use futures::StreamExt;
//!
//! let client = Client::new(HttpSettings::default())?;
//! let params = serde_json::json!({"model": "anthropic/claude-3-5-sonnet-20241022",
//!                                 "api_key": "os.environ/ANTHROPIC_API_KEY"});
//! let dep = Deployment::from_litellm_params(&params)?;
//! let req: ChatRequest = serde_json::from_value(serde_json::json!({
//!     "model": "claude", "messages": [{"role": "user", "content": "Hello"}]
//! })).unwrap();
//!
//! let resp = client.chat(&dep, &req).await?;
//! let mut stream = client.chat_stream(&dep, &req).await?;
//! while let Some(chunk) = stream.next().await {
//!     let chunk = chunk?; // the last chunk carries `usage` (empty `choices`)
//! }
//! # Ok(()) }
//! ```
//!
//! # Public surface
//!
//! * [`Client::new`]`(HttpSettings) -> Result<Client, ProviderError>`
//! * [`Deployment::from_litellm_params`]`(&serde_json::Value)` and
//!   [`Deployment::from_litellm_params_with_env`] (injectable env lookup for
//!   `os.environ/NAME`)
//! * [`Client::chat`], [`Client::chat_stream`] (returns [`ChatStream`]),
//!   [`Client::embeddings`]
//! * [`ProviderError::is_retryable`], [`ProviderError::status_code`],
//!   [`ProviderError::to_openai_body`], [`ProviderError::kind`]
//! * [`estimate_prompt_tokens`]
//! * images and audio ([`media`]): [`Client::image_generation`],
//!   [`Client::image_edit`], [`Client::transcription`], [`Client::speech`],
//!   and [`media::audio_duration`] for uploaded audio files
//! * [`pricing::lookup`], [`pricing::lookup_with_provider`],
//!   [`pricing::to_nano_per_token`], [`Deployment::pricing`]
//!
//! # Notes for the server
//!
//! Refinements relative to the originally sketched API:
//!
//! * `ProviderError` is a struct with an [`ErrorKind`] (match on
//!   `err.kind()`), not an enum.
//! * `Deployment::from_litellm_params` takes a `serde_json::Value`; convert
//!   YAML with `serde_json::to_value(&yaml_value)`.
//! * `Deployment.api_key` is a [`Secret`] (redacted `Debug`); use
//!   `.expose()`.
//! * `Pricing` additionally carries cache read/creation prices.
//! * `reqwest` 0.13 is used; its rustls backend feature is named `rustls`
//!   (formerly `rustls-tls`).
//!
//! Behaviour worth knowing:
//!
//! * **Stream usage.** Streams always end with a usage-only chunk
//!   (`choices: []`, `usage: Some(..)`) when the upstream reports usage
//!   (OpenAI-compatible providers get `stream_options.include_usage = true`
//!   where supported; Anthropic/Gemini usage is accumulated). Drop that chunk
//!   before forwarding if [`ChatRequest::wants_stream_usage`] is false.
//! * **Errors.** Build the client response from
//!   `(err.status_code(), err.to_openai_body())`. Mid-stream failures arrive
//!   as the stream's final `Err` item; emit them as an SSE `data:` error
//!   object.
//! * **Mocking.** `mock_response` in the request body (or in
//!   `litellm_params`) short-circuits the upstream call, as in LiteLLM.
//!   Strip it from untrusted requests if clients must not use it.
//! * **Gateway-only fields** (`metadata`, `mock_response`, `fallbacks`,
//!   `api_key`, ... — see [`GATEWAY_ONLY_FIELDS`]) are never forwarded.
//! * The `model` in responses is the upstream's; replace it with the alias
//!   the client used if desired.
//! * **Bedrock** (`bedrock/...`) chat goes through the Converse API, signed
//!   with SigV4 (a self-contained implementation checked against AWS's test
//!   suite) or sent with a Bedrock API key; streams are AWS event-stream
//!   frames ([`eventstream`]). Embeddings support Amazon Titan and Cohere.
//!   Settings live in [`Deployment::cloud`] ([`BedrockConfig`]).
//! * **Vertex AI** (`vertex_ai/...`) reuses the Gemini and Anthropic
//!   translations. Google OAuth2 access tokens (service-account JWT
//!   exchange, authorized-user refresh, or the GCE metadata server) are
//!   cached inside the [`Client`], shared by its clones and refreshed five
//!   minutes before expiry, so keep one `Client` per process. Settings live
//!   in [`Deployment::cloud`] ([`VertexConfig`]).

mod auth;
mod client;
mod deployment;
mod error;
pub mod eventstream;
pub mod formats;
pub mod media;
pub mod pricing;
mod providers;
pub mod sse;
mod tokens;
pub mod types;

use std::pin::Pin;

use futures::Stream;

pub use auth::gcp::{AuthorizedUser, GcpCredentials, ServiceAccountKey};
pub use client::{Client, HttpSettings};
pub use deployment::{CloudConfig, DEFAULT_AZURE_API_VERSION, Deployment, Provider, REQUEST_DEFAULT_KEYS, Secret};
pub use error::{ErrorKind, ProviderError};
pub use pricing::Pricing;
pub use providers::bedrock::{AwsAuth, AwsCredentials, BedrockConfig};
pub use providers::openai::GATEWAY_ONLY_FIELDS;
pub use providers::vertex::VertexConfig;
pub use tokens::estimate_prompt_tokens;
pub use types::{ChatChunk, ChatMessage, ChatRequest, ChatResponse, EmbeddingRequest, EmbeddingResponse, ErrorBody, Usage};

/// A streamed chat completion: OpenAI `chat.completion.chunk`s. Ends after
/// the first `Err`.
pub type ChatStream = Pin<Box<dyn Stream<Item = Result<ChatChunk, ProviderError>> + Send>>;
