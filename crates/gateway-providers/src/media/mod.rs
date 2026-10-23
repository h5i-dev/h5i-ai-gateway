//! Images and audio: OpenAI's `/images/generations`, `/images/edits`,
//! `/audio/transcriptions`, `/audio/translations` and `/audio/speech`.
//!
//! | Endpoint | Upstreams |
//! |---|---|
//! | image generation | OpenAI and OpenAI-compatible, Azure OpenAI, Gemini (Imagen `:predict`, `gemini-*-image` `:generateContent`) |
//! | image edits | OpenAI and OpenAI-compatible, Azure OpenAI |
//! | transcriptions, translations | OpenAI and OpenAI-compatible (Groq, …), Azure OpenAI |
//! | speech | OpenAI and OpenAI-compatible, Azure OpenAI |
//!
//! Requests pass through to OpenAI-shaped upstreams with gateway-only fields
//! removed, the upstream model name substituted and `extra_body` merged in;
//! multipart uploads are re-encoded with the same parts. `mock_response`
//! (in the request, the deployment, or a `mock/` deployment) answers without
//! a network call, honouring LiteLLM's error triggers.
//!
//! Pricing is the server's business; this module reports what it can
//! measure: image counts and token usage, the audio duration a provider
//! reports, and the duration of an uploaded audio file ([`audio_duration`]).

mod audio;
pub mod duration;
mod images;
pub mod multipart;

use std::pin::Pin;
use std::time::Duration;

use bytes::Bytes;
use futures::{Stream, StreamExt, stream};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::client::Client;
use crate::deployment::{Deployment, Protocol};
use crate::error::{ErrorKind, ProviderError};
use crate::providers::mock;
use crate::types::JsonObject;

pub use audio::subtitle_end;
pub use duration::{AudioDuration, audio_duration};
pub use multipart::Multipart;

/// Default canned image for `mock/` deployments.
pub const DEFAULT_MOCK_IMAGE_URL: &str = "https://example.com/mock-image.png";

// ---------------------------------------------------------------------------
// Images

/// `POST /v1/images/generations` request body. Fields not modelled here
/// (`output_compression`, `moderation`, provider-specific knobs) are kept in
/// `extra` and passed through to OpenAI-shaped upstreams.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ImageRequest {
    #[serde(default)]
    pub model: String,
    pub prompt: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub n: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub size: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub quality: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub style: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub response_format: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub background: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_format: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub user: Option<String>,
    /// Gateway-only: answer with this image URL instead of calling upstream.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mock_response: Option<String>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// An images response: `{created, data: [{url | b64_json, revised_prompt}], usage?}`.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ImageResponse {
    #[serde(default)]
    pub created: u64,
    #[serde(default)]
    pub data: Vec<ImageData>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage: Option<ImageUsage>,
    /// gpt-image models also report `size`, `quality`, `output_format`, `background`.
    #[serde(flatten)]
    pub extra: JsonObject,
}

impl ImageResponse {
    /// A string field the upstream reported (`size`, `quality`, …).
    pub fn reported(&self, field: &str) -> Option<&str> {
        self.extra.get(field).and_then(Value::as_str)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ImageData {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub url: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub b64_json: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub revised_prompt: Option<String>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// Token usage of a token-priced image model (gpt-image, Gemini image models).
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ImageUsage {
    #[serde(default)]
    pub input_tokens: u64,
    #[serde(default)]
    pub output_tokens: u64,
    #[serde(default)]
    pub total_tokens: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input_tokens_details: Option<ImageTokenDetails>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_tokens_details: Option<ImageTokenDetails>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ImageTokenDetails {
    #[serde(default)]
    pub text_tokens: u64,
    #[serde(default)]
    pub image_tokens: u64,
    #[serde(flatten)]
    pub extra: JsonObject,
}

// ---------------------------------------------------------------------------
// Multipart requests (image edits, transcriptions)

/// One uploaded file of a multipart request.
#[derive(Debug, Clone, PartialEq)]
pub struct FilePart {
    /// The form field (`file`, `image`, `image[]`, `mask`).
    pub field: String,
    pub filename: String,
    pub content_type: Option<String>,
    pub data: Bytes,
}

/// A multipart request: its text fields in order (without `model`) and its
/// files.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct MediaForm {
    pub model: String,
    pub fields: Vec<(String, String)>,
    pub files: Vec<FilePart>,
}

impl MediaForm {
    /// The last value of a text field.
    pub fn field(&self, name: &str) -> Option<&str> {
        self.fields.iter().rev().find(|(k, _)| k == name).map(|(_, v)| v.as_str())
    }

    /// The first file uploaded under `name`.
    pub fn file(&self, name: &str) -> Option<&FilePart> {
        self.files.iter().find(|f| f.field == name)
    }

    pub fn mock_response(&self) -> Option<&str> {
        self.field("mock_response")
    }
}

// ---------------------------------------------------------------------------
// Transcriptions

/// A transcription or translation: JSON (`json`, `verbose_json`), or text
/// (`text`, `srt`, `vtt`) passed through with the upstream's content type.
#[derive(Debug, Clone, PartialEq)]
pub enum TranscriptionResponse {
    Json(Value),
    Text { content_type: String, body: String },
}

/// Token usage a token-priced transcription model reports
/// (`usage: {type: "tokens", input_tokens, output_tokens, input_token_details}`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TranscriptionTokens {
    pub audio_tokens: u64,
    pub text_tokens: u64,
    pub output_tokens: u64,
}

impl TranscriptionResponse {
    /// Seconds of audio the provider reports: `duration` (verbose_json) or
    /// `usage: {type: "duration", seconds}`; for subtitles, the end of the
    /// last cue (a lower bound).
    pub fn duration(&self) -> Option<f64> {
        match self {
            TranscriptionResponse::Json(v) => v.get("duration").and_then(Value::as_f64).or_else(|| {
                let u = v.get("usage")?;
                (u.get("type").and_then(Value::as_str) == Some("duration")).then(|| u.get("seconds").and_then(Value::as_f64)).flatten()
            }),
            TranscriptionResponse::Text { .. } => None,
        }
    }

    /// The end of the last subtitle cue, for `srt`/`vtt` responses.
    pub fn subtitle_end(&self) -> Option<f64> {
        match self {
            TranscriptionResponse::Text { body, .. } => subtitle_end(body),
            TranscriptionResponse::Json(_) => None,
        }
    }

    /// Token usage, if the provider reports it.
    pub fn tokens(&self) -> Option<TranscriptionTokens> {
        let TranscriptionResponse::Json(v) = self else {
            return None;
        };
        let u = v.get("usage")?;
        if u.get("type").and_then(Value::as_str) == Some("duration") {
            return None;
        }
        let get = |o: &Value, k: &str| o.get(k).and_then(Value::as_u64);
        let input = get(u, "input_tokens")?;
        let output = get(u, "output_tokens").unwrap_or(0);
        let details = u.get("input_token_details").or(u.get("input_tokens_details"));
        let (audio, text) = match details {
            Some(d) => (get(d, "audio_tokens").unwrap_or(0), get(d, "text_tokens").unwrap_or(0)),
            None => (input, 0),
        };
        Some(TranscriptionTokens { audio_tokens: audio, text_tokens: text.max(input.saturating_sub(audio)), output_tokens: output })
    }
}

// ---------------------------------------------------------------------------
// Speech

/// `POST /v1/audio/speech` request body.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct SpeechRequest {
    #[serde(default)]
    pub model: String,
    pub input: String,
    /// A voice name, or `{"id": ...}` for custom voices.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub voice: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub response_format: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub speed: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instructions: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stream_format: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mock_response: Option<String>,
    #[serde(flatten)]
    pub extra: JsonObject,
}

/// A stream of bytes from the upstream. Ends after the first `Err`.
pub type ByteStream = Pin<Box<dyn Stream<Item = Result<Bytes, ProviderError>> + Send>>;

/// Synthesized audio, streamed as the upstream sends it.
pub struct SpeechResponse {
    pub content_type: String,
    pub body: ByteStream,
}

impl std::fmt::Debug for SpeechResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SpeechResponse").field("content_type", &self.content_type).finish_non_exhaustive()
    }
}

impl SpeechResponse {
    /// Collect the whole body.
    pub async fn bytes(self) -> Result<Bytes, ProviderError> {
        let mut out = Vec::new();
        let mut body = self.body;
        while let Some(chunk) = body.next().await {
            out.extend_from_slice(&chunk?);
        }
        Ok(Bytes::from(out))
    }
}

// ---------------------------------------------------------------------------
// Calls

/// The canned answer, if this call should be mocked.
fn mock_text<'a>(dep: &'a Deployment, requested: Option<&'a str>, default: &'static str) -> Option<&'a str> {
    requested.or(dep.mock_response.as_deref()).or_else(|| (dep.provider.protocol() == Protocol::Mock).then_some(default))
}

fn unsupported(dep: &Deployment, what: &str) -> ProviderError {
    ProviderError::bad_request(dep.provider.name(), format!("{what} is not supported for provider '{}'", dep.provider))
}

impl Client {
    /// Generate images. Supported for OpenAI-compatible providers, Azure,
    /// Gemini and mock deployments.
    pub async fn image_generation(&self, dep: &Deployment, req: &ImageRequest) -> Result<ImageResponse, ProviderError> {
        if let Some(text) = mock_text(dep, req.mock_response.as_deref(), DEFAULT_MOCK_IMAGE_URL) {
            return images::mock(dep, req.n, text);
        }
        let http = match dep.provider.protocol() {
            Protocol::OpenAi | Protocol::Azure => images::openai_request(dep, req)?,
            Protocol::Gemini => images::gemini_request(dep, req)?,
            _ => return Err(unsupported(dep, "image generation")),
        };
        let body = self.send(dep, http, self.timeout(dep)).await?.text().await;
        let body = body.map_err(|e| ProviderError::from_reqwest(dep.provider.name(), e))?;
        match dep.provider.protocol() {
            Protocol::Gemini => images::parse_gemini(dep, &body),
            _ => images::parse_openai(dep, &body),
        }
    }

    /// Edit images (multipart `image`/`image[]`, `mask`, `prompt`, …).
    /// Supported for OpenAI-compatible providers, Azure and mock deployments.
    pub async fn image_edit(&self, dep: &Deployment, form: &MediaForm) -> Result<ImageResponse, ProviderError> {
        if let Some(text) = mock_text(dep, form.mock_response(), DEFAULT_MOCK_IMAGE_URL) {
            let n = form.field("n").and_then(|n| n.parse().ok());
            return images::mock(dep, n, text);
        }
        if !matches!(dep.provider.protocol(), Protocol::OpenAi | Protocol::Azure) {
            return Err(unsupported(dep, "image editing"));
        }
        let body = self.send_form(dep, "images/edits", form).await?;
        images::parse_openai(dep, &body.1)
    }

    /// Transcribe (or, with `translate`, translate to English) an audio
    /// file. Supported for OpenAI-compatible providers, Azure and mock
    /// deployments.
    pub async fn transcription(&self, dep: &Deployment, form: &MediaForm, translate: bool) -> Result<TranscriptionResponse, ProviderError> {
        if let Some(text) = mock_text(dep, form.mock_response(), mock::DEFAULT_MOCK_RESPONSE) {
            mock::check_error_trigger(dep, text)?;
            return Ok(audio::mock_transcription(form, text));
        }
        if !matches!(dep.provider.protocol(), Protocol::OpenAi | Protocol::Azure) {
            return Err(unsupported(dep, "audio transcription"));
        }
        let path = if translate { "audio/translations" } else { "audio/transcriptions" };
        let (content_type, body) = self.send_form(dep, path, form).await?;
        audio::parse_transcription(dep, form, content_type.as_deref(), body)
    }

    /// Text to speech, streamed. Supported for OpenAI-compatible providers,
    /// Azure and mock deployments.
    pub async fn speech(&self, dep: &Deployment, req: &SpeechRequest) -> Result<SpeechResponse, ProviderError> {
        if let Some(text) = mock_text(dep, req.mock_response.as_deref(), mock::DEFAULT_MOCK_RESPONSE) {
            mock::check_error_trigger(dep, text)?;
            let body: ByteStream = Box::pin(stream::once(async { Ok(audio::silent_wav()) }));
            return Ok(SpeechResponse { content_type: "audio/wav".into(), body });
        }
        if !matches!(dep.provider.protocol(), Protocol::OpenAi | Protocol::Azure) {
            return Err(unsupported(dep, "text to speech"));
        }
        let provider = dep.provider.name();
        let http = audio::speech_request(dep, req)?;
        let timeout = self.stream_timeout(dep);
        // No whole-request timeout: long audio streams for a while. Time to
        // headers and gaps between chunks are bounded instead.
        let response = tokio::time::timeout(timeout, self.send(dep, http, None)).await.map_err(|_| headers_timeout(provider, timeout))??;
        let content_type = content_type(&response).unwrap_or_else(|| audio::speech_content_type(req.response_format.as_deref()).to_owned());
        Ok(SpeechResponse { content_type, body: idle_timeout(provider, response.bytes_stream(), timeout) })
    }

    /// POST `form` as multipart to the OpenAI-shaped `path`; the response's
    /// content type and body.
    async fn send_form(&self, dep: &Deployment, path: &str, form: &MediaForm) -> Result<(Option<String>, String), ProviderError> {
        let provider = dep.provider.name();
        let (url, headers, multipart) = audio::form_request(dep, path, form);
        let (form_type, body) = multipart.finish();
        let builder = self.post(&url).header(reqwest::header::CONTENT_TYPE, form_type).body(body);
        let response = self.execute(dep, builder, &headers, self.timeout(dep)).await?;
        let content_type = content_type(&response);
        let body = response.text().await.map_err(|e| ProviderError::from_reqwest(provider, e))?;
        Ok((content_type, body))
    }
}

fn content_type(response: &reqwest::Response) -> Option<String> {
    response.headers().get(reqwest::header::CONTENT_TYPE).and_then(|v| v.to_str().ok()).map(str::to_owned)
}

fn headers_timeout(provider: &str, timeout: Duration) -> ProviderError {
    ProviderError::new(ErrorKind::Timeout, provider, format!("no response headers within {}s", timeout.as_secs_f64()))
}

/// Map a body stream's errors and bound the gaps between chunks.
fn idle_timeout<S>(provider: &'static str, body: S, timeout: Duration) -> ByteStream
where
    S: Stream<Item = Result<Bytes, reqwest::Error>> + Send + 'static,
{
    Box::pin(stream::unfold((Box::pin(body), false), move |(mut body, done)| async move {
        if done {
            return None;
        }
        match tokio::time::timeout(timeout, body.next()).await {
            Ok(Some(Ok(b))) => Some((Ok(b), (body, false))),
            Ok(Some(Err(e))) => Some((Err(ProviderError::from_reqwest(provider, e)), (body, true))),
            Ok(None) => None,
            Err(_) => Some((
                Err(ProviderError::new(ErrorKind::Timeout, provider, format!("no data from upstream for {}s", timeout.as_secs_f64()))),
                (body, true),
            )),
        }
    }))
}
