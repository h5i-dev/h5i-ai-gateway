//! The HTTP client: dispatches a request for a [`Deployment`] to the right
//! adapter, performs the upstream call, and classifies failures.
//!
//! The client is policy-free: it never retries, never picks a deployment and
//! never checks budgets. One `Client` should be shared by the whole process
//! (it wraps a pooled `reqwest::Client`).

use std::time::Duration;

use reqwest::header::{HeaderMap, HeaderName, HeaderValue};

use crate::ChatStream;
use crate::deployment::{Deployment, Protocol};
use crate::error::{ErrorKind, ProviderError};
use crate::providers::{self, HttpRequest, StreamTranslator, anthropic, gemini, mock, openai};
use crate::sse;
use crate::types::{ChatRequest, ChatResponse, EmbeddingRequest, EmbeddingResponse};

/// Transport settings shared by all deployments.
#[derive(Debug, Clone)]
pub struct HttpSettings {
    /// TCP + TLS connect timeout.
    pub connect_timeout: Duration,
    /// Whole-request timeout for non-streaming calls, and the time-to-first-
    /// byte / between-events timeout for streams, when the deployment sets no
    /// `timeout` / `stream_timeout`. LiteLLM's default is 600 s.
    pub default_timeout: Duration,
    /// How long idle pooled connections are kept.
    pub pool_idle_timeout: Duration,
    pub user_agent: String,
}

impl Default for HttpSettings {
    fn default() -> Self {
        Self {
            connect_timeout: Duration::from_secs(10),
            default_timeout: Duration::from_secs(600),
            pool_idle_timeout: Duration::from_secs(90),
            user_agent: concat!("h5i-ai-gateway/", env!("CARGO_PKG_VERSION")).to_owned(),
        }
    }
}

/// Upstream client.
#[derive(Debug, Clone)]
pub struct Client {
    http: reqwest::Client,
    settings: HttpSettings,
}

impl Client {
    /// Build a client (rustls, HTTP/1.1 + HTTP/2, connection pooling).
    pub fn new(settings: HttpSettings) -> Result<Self, ProviderError> {
        let http = reqwest::Client::builder()
            .connect_timeout(settings.connect_timeout)
            .pool_idle_timeout(settings.pool_idle_timeout)
            .user_agent(settings.user_agent.clone())
            .build()
            .map_err(|e| {
                ProviderError::config("client", format!("cannot build HTTP client: {e}"))
            })?;
        Ok(Self { http, settings })
    }

    /// Non-streaming chat completion.
    ///
    /// The response's `model` is the upstream's model name; the server may
    /// replace it with the alias the client asked for.
    pub async fn chat(
        &self,
        dep: &Deployment,
        req: &ChatRequest,
    ) -> Result<ChatResponse, ProviderError> {
        if let Some(text) = mock::mock_text(dep, req) {
            return mock::chat(dep, req, text);
        }
        let req = providers::apply_request_defaults(dep, req)?;
        let http = match dep.provider.protocol() {
            Protocol::OpenAi | Protocol::Azure => openai::chat_request(dep, &req, false)?,
            Protocol::Anthropic => anthropic::chat_request(dep, &req, false)?,
            Protocol::Gemini => gemini::chat_request(dep, &req, false)?,
            Protocol::Mock => unreachable!("mock deployments are answered above"),
        };
        let body = self.send(dep, http, self.timeout(dep)).await?.text().await;
        let body = body.map_err(|e| ProviderError::from_reqwest(dep.provider.name(), e))?;
        match dep.provider.protocol() {
            Protocol::Anthropic => anthropic::parse_chat(dep, &req, &body),
            Protocol::Gemini => gemini::parse_chat(dep, &body),
            _ => openai::parse_chat(dep, &body),
        }
    }

    /// Streaming chat completion.
    ///
    /// Errors before the first byte (connection, HTTP status) are returned
    /// directly; later failures arrive as the stream's last item. When the
    /// upstream reports usage, the final item is a usage-only chunk (empty
    /// `choices`), whether or not the client set
    /// `stream_options.include_usage` (see
    /// [`ChatRequest::wants_stream_usage`]).
    pub async fn chat_stream(
        &self,
        dep: &Deployment,
        req: &ChatRequest,
    ) -> Result<ChatStream, ProviderError> {
        if let Some(text) = mock::mock_text(dep, req) {
            return mock::chat_stream(dep, req, text);
        }
        let req = providers::apply_request_defaults(dep, req)?;
        let provider = dep.provider.name();
        let timeout = dep
            .stream_timeout
            .or(dep.timeout)
            .unwrap_or(self.settings.default_timeout);
        let http = match dep.provider.protocol() {
            Protocol::OpenAi | Protocol::Azure => openai::chat_request(dep, &req, true)?,
            Protocol::Anthropic => anthropic::chat_request(dep, &req, true)?,
            Protocol::Gemini => gemini::chat_request(dep, &req, true)?,
            Protocol::Mock => unreachable!("mock deployments are answered above"),
        };
        // No whole-request timeout: the stream may legitimately run long.
        // Time to headers and gaps between events are bounded instead.
        let response = tokio::time::timeout(timeout, self.send(dep, http, None))
            .await
            .map_err(|_| {
                ProviderError::new(
                    ErrorKind::Timeout,
                    provider,
                    format!("no response headers within {}s", timeout.as_secs_f64()),
                )
            })??;
        let events = sse::events(provider, response.bytes_stream());
        let translator: Box<dyn StreamTranslator> = match dep.provider.protocol() {
            Protocol::Anthropic => Box::new(anthropic::AnthropicStream::new(dep, &req)),
            Protocol::Gemini => Box::new(gemini::GeminiStream::new(dep)),
            _ => Box::new(openai::OpenAiStream::new(provider)),
        };
        Ok(providers::drive(provider, events, translator, timeout))
    }

    /// Embeddings. Supported for OpenAI-compatible providers, Azure, Gemini
    /// and mock deployments.
    pub async fn embeddings(
        &self,
        dep: &Deployment,
        req: &EmbeddingRequest,
    ) -> Result<EmbeddingResponse, ProviderError> {
        let provider = dep.provider.name();
        let http = match dep.provider.protocol() {
            Protocol::Mock => return Ok(mock::embeddings(dep, req)),
            Protocol::OpenAi | Protocol::Azure => openai::embeddings_request(dep, req)?,
            Protocol::Gemini => gemini::embeddings_request(dep, req)?,
            Protocol::Anthropic => {
                return Err(ProviderError::bad_request(
                    provider,
                    "Anthropic does not offer an embeddings API",
                ));
            }
        };
        let body = self.send(dep, http, self.timeout(dep)).await?.text().await;
        let body = body.map_err(|e| ProviderError::from_reqwest(provider, e))?;
        match dep.provider.protocol() {
            Protocol::Gemini => gemini::parse_embeddings(dep, req, &body),
            _ => openai::parse_embeddings(dep, &body),
        }
    }

    fn timeout(&self, dep: &Deployment) -> Option<Duration> {
        Some(dep.timeout.unwrap_or(self.settings.default_timeout))
    }

    /// POST the request; non-2xx responses become classified errors.
    async fn send(
        &self,
        dep: &Deployment,
        req: HttpRequest,
        timeout: Option<Duration>,
    ) -> Result<reqwest::Response, ProviderError> {
        let provider = dep.provider.name();
        let mut headers = HeaderMap::new();
        for (name, value) in req.headers.iter().chain(&dep.extra_headers) {
            let name = HeaderName::from_bytes(name.as_bytes()).map_err(|_| {
                ProviderError::config(provider, format!("invalid header name '{name}'"))
            })?;
            let mut value = HeaderValue::from_str(value).map_err(|_| {
                ProviderError::config(provider, format!("invalid value for header '{name}'"))
            })?;
            if is_credential(&name) {
                value.set_sensitive(true);
            }
            // Deployment `extra_headers` come last and override.
            headers.insert(name, value);
        }
        let mut builder = self.http.post(&req.url).headers(headers).json(&req.body);
        if let Some(t) = timeout {
            builder = builder.timeout(t);
        }
        let response = builder
            .send()
            .await
            .map_err(|e| ProviderError::from_reqwest(provider, e))?;
        let status = response.status();
        if status.is_success() {
            return Ok(response);
        }
        let retry_after = retry_after(response.headers());
        let body = response.text().await.unwrap_or_default();
        Err(ProviderError::from_upstream(
            provider,
            status.as_u16(),
            &body,
            retry_after,
        ))
    }
}

fn is_credential(name: &HeaderName) -> bool {
    matches!(
        name.as_str(),
        "authorization" | "api-key" | "x-api-key" | "x-goog-api-key"
    )
}

/// `retry-after-ms` (OpenAI) or `retry-after` in seconds.
fn retry_after(headers: &HeaderMap) -> Option<Duration> {
    let parse = |name: &str| headers.get(name)?.to_str().ok()?.trim().parse::<f64>().ok();
    let secs = parse("retry-after-ms")
        .map(|ms| ms / 1000.0)
        .or_else(|| parse("retry-after"))?;
    Duration::try_from_secs_f64(secs).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retry_after_headers() {
        let mut h = HeaderMap::new();
        assert_eq!(retry_after(&h), None);
        h.insert("retry-after", HeaderValue::from_static("2"));
        assert_eq!(retry_after(&h), Some(Duration::from_secs(2)));
        h.insert("retry-after-ms", HeaderValue::from_static("1500"));
        assert_eq!(retry_after(&h), Some(Duration::from_millis(1500)));
        let mut h = HeaderMap::new();
        h.insert(
            "retry-after",
            HeaderValue::from_static("Wed, 21 Oct 2015 07:28:00 GMT"),
        );
        assert_eq!(retry_after(&h), None);
    }

    #[test]
    fn builds_with_defaults() {
        assert!(Client::new(HttpSettings::default()).is_ok());
    }
}
