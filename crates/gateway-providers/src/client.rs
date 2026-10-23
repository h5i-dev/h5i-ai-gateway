//! The HTTP client: dispatches a request for a [`Deployment`] to the right
//! adapter, performs the upstream call, and classifies failures.
//!
//! The client is policy-free: it never retries, never picks a deployment and
//! never checks budgets. One `Client` should be shared by the whole process
//! (it wraps a pooled `reqwest::Client`).

use std::sync::Arc;
use std::time::{Duration, SystemTime};

use reqwest::header::{HeaderMap, HeaderName, HeaderValue};

use crate::ChatStream;
use crate::auth::gcp::{GcpCredentials, TokenCache};
use crate::deployment::{Deployment, Protocol};
use crate::error::{ErrorKind, ProviderError};
use crate::providers::{self, HttpRequest, StreamTranslator, anthropic, bedrock, gemini, mock, openai, vertex};
use crate::types::{ChatRequest, ChatResponse, EmbeddingRequest, EmbeddingResponse};
use crate::{eventstream, sse};

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
    /// Google OAuth2 access tokens, shared by all clones of this client.
    tokens: Arc<TokenCache>,
}

impl Client {
    /// Build a client (rustls, HTTP/1.1 + HTTP/2, connection pooling).
    pub fn new(settings: HttpSettings) -> Result<Self, ProviderError> {
        let http = reqwest::Client::builder()
            .connect_timeout(settings.connect_timeout)
            .pool_idle_timeout(settings.pool_idle_timeout)
            .user_agent(settings.user_agent.clone())
            .build()
            .map_err(|e| ProviderError::config("client", format!("cannot build HTTP client: {e}")))?;
        Ok(Self { http, settings, tokens: Arc::default() })
    }

    /// Non-streaming chat completion.
    ///
    /// The response's `model` is the upstream's model name; the server may
    /// replace it with the alias the client asked for.
    pub async fn chat(&self, dep: &Deployment, req: &ChatRequest) -> Result<ChatResponse, ProviderError> {
        if let Some(text) = mock::mock_text(dep, req) {
            return mock::chat(dep, req, text);
        }
        let req = providers::apply_request_defaults(dep, req)?;
        let http = self.chat_http(dep, &req, false).await?;
        let body = self.send(dep, http, self.timeout(dep)).await?.text().await;
        let body = body.map_err(|e| ProviderError::from_reqwest(dep.provider.name(), e))?;
        match dep.provider.protocol() {
            Protocol::Anthropic => anthropic::parse_chat(dep, &req, &body),
            Protocol::Gemini => gemini::parse_chat(dep, &body),
            Protocol::Bedrock => bedrock::parse_chat(dep, &req, &body),
            Protocol::Vertex => match vertex::family(&dep.model) {
                vertex::Family::Anthropic => anthropic::parse_chat(dep, &req, &body),
                vertex::Family::Gemini => gemini::parse_chat(dep, &body),
            },
            _ => openai::parse_chat(dep, &body),
        }
    }

    /// Build the upstream chat request (resolving Vertex AI credentials).
    async fn chat_http(&self, dep: &Deployment, req: &ChatRequest, stream: bool) -> Result<HttpRequest, ProviderError> {
        match dep.provider.protocol() {
            Protocol::OpenAi | Protocol::Azure => openai::chat_request(dep, req, stream),
            Protocol::Anthropic => anthropic::chat_request(dep, req, stream),
            Protocol::Gemini => gemini::chat_request(dep, req, stream),
            Protocol::Bedrock => bedrock::chat_request(dep, req, stream),
            Protocol::Vertex => {
                let ctx = self.vertex_context(dep).await?;
                vertex::chat_request(dep, &ctx, req, stream)
            }
            Protocol::Mock => unreachable!("mock deployments are answered before"),
        }
    }

    /// The Vertex AI project and a valid access token for `dep`.
    async fn vertex_context(&self, dep: &Deployment) -> Result<vertex::Context, ProviderError> {
        let cfg = vertex::config(dep)?;
        let token = self.tokens.access_token(&self.http, &cfg.credentials).await?;
        let project = match (&cfg.project, &cfg.credentials) {
            (Some(p), _) => p.clone(),
            (None, GcpCredentials::MetadataServer { host }) => self.tokens.metadata_project(&self.http, host).await?,
            // A fully custom api_base does not need the project.
            (None, _) => String::new(),
        };
        Ok(vertex::Context { project, token })
    }

    /// Streaming chat completion.
    ///
    /// Errors before the first byte (connection, HTTP status) are returned
    /// directly; later failures arrive as the stream's last item. When the
    /// upstream reports usage, the final item is a usage-only chunk (empty
    /// `choices`), whether or not the client set
    /// `stream_options.include_usage` (see
    /// [`ChatRequest::wants_stream_usage`]).
    pub async fn chat_stream(&self, dep: &Deployment, req: &ChatRequest) -> Result<ChatStream, ProviderError> {
        if let Some(text) = mock::mock_text(dep, req) {
            return mock::chat_stream(dep, req, text);
        }
        let req = providers::apply_request_defaults(dep, req)?;
        let provider = dep.provider.name();
        let timeout = dep.stream_timeout.or(dep.timeout).unwrap_or(self.settings.default_timeout);
        let http = self.chat_http(dep, &req, true).await?;
        // No whole-request timeout: the stream may legitimately run long.
        // Time to headers and gaps between events are bounded instead.
        let response = tokio::time::timeout(timeout, self.send(dep, http, None))
            .await
            .map_err(|_| ProviderError::new(ErrorKind::Timeout, provider, format!("no response headers within {}s", timeout.as_secs_f64())))??;
        let translator: Box<dyn StreamTranslator> = match dep.provider.protocol() {
            Protocol::Anthropic => Box::new(anthropic::AnthropicStream::new(dep, &req)),
            Protocol::Gemini => Box::new(gemini::GeminiStream::new(dep)),
            Protocol::Bedrock => Box::new(bedrock::BedrockStream::new(dep, &req)),
            Protocol::Vertex => match vertex::family(&dep.model) {
                vertex::Family::Anthropic => Box::new(anthropic::AnthropicStream::new(dep, &req)),
                vertex::Family::Gemini => Box::new(gemini::GeminiStream::new(dep)),
            },
            _ => Box::new(openai::OpenAiStream::new(provider)),
        };
        if dep.provider.protocol() == Protocol::Bedrock {
            // ConverseStream uses AWS event-stream binary framing, not SSE.
            let events = eventstream::events(provider, response.bytes_stream());
            return Ok(providers::drive(provider, events, translator, timeout));
        }
        let events = sse::events(provider, response.bytes_stream());
        Ok(providers::drive(provider, events, translator, timeout))
    }

    /// Embeddings. Supported for OpenAI-compatible providers, Azure, Gemini,
    /// Vertex AI, Bedrock (Titan and Cohere) and mock deployments.
    pub async fn embeddings(&self, dep: &Deployment, req: &EmbeddingRequest) -> Result<EmbeddingResponse, ProviderError> {
        let provider = dep.provider.name();
        let http = match dep.provider.protocol() {
            Protocol::Mock => return Ok(mock::embeddings(dep, req)),
            Protocol::OpenAi | Protocol::Azure => openai::embeddings_request(dep, req)?,
            Protocol::Gemini => gemini::embeddings_request(dep, req)?,
            Protocol::Vertex => {
                let ctx = self.vertex_context(dep).await?;
                vertex::embeddings_request(dep, &ctx, req)?
            }
            Protocol::Bedrock => return self.bedrock_embeddings(dep, req).await,
            Protocol::Anthropic => {
                return Err(ProviderError::bad_request(provider, "Anthropic does not offer an embeddings API"));
            }
        };
        let body = self.send(dep, http, self.timeout(dep)).await?.text().await;
        let body = body.map_err(|e| ProviderError::from_reqwest(provider, e))?;
        match dep.provider.protocol() {
            Protocol::Gemini => gemini::parse_embeddings(dep, req, &body),
            Protocol::Vertex => vertex::parse_embeddings(dep, &body),
            _ => openai::parse_embeddings(dep, &body),
        }
    }

    /// Bedrock InvokeModel embeddings: one call per Titan input (run
    /// concurrently), one per Cohere batch.
    async fn bedrock_embeddings(&self, dep: &Deployment, req: &EmbeddingRequest) -> Result<EmbeddingResponse, ProviderError> {
        let provider = dep.provider.name();
        let calls = bedrock::embeddings_requests(dep, req)?.into_iter().map(|http| async move {
            let response = self.send(dep, http, self.timeout(dep)).await?;
            let tokens = response.headers().get("x-amzn-bedrock-input-token-count").and_then(|v| v.to_str().ok()?.trim().parse::<u64>().ok());
            let body = response.text().await.map_err(|e| ProviderError::from_reqwest(provider, e))?;
            Ok::<_, ProviderError>((body, tokens))
        });
        let responses = futures::future::try_join_all(calls).await?;
        bedrock::parse_embeddings(dep, req, &responses)
    }

    pub(crate) fn timeout(&self, dep: &Deployment) -> Option<Duration> {
        Some(dep.timeout.unwrap_or(self.settings.default_timeout))
    }

    /// Time to response headers (and between chunks) for streamed bodies.
    pub(crate) fn stream_timeout(&self, dep: &Deployment) -> Duration {
        dep.stream_timeout.or(dep.timeout).unwrap_or(self.settings.default_timeout)
    }

    /// A POST to `url`, to be completed with a body and sent with
    /// [`Client::execute`].
    pub(crate) fn post(&self, url: &str) -> reqwest::RequestBuilder {
        self.http.post(url)
    }

    /// POST the request; non-2xx responses become classified errors.
    pub(crate) async fn send(&self, dep: &Deployment, req: HttpRequest, timeout: Option<Duration>) -> Result<reqwest::Response, ProviderError> {
        let provider = dep.provider.name();
        let body = serde_json::to_vec(&req.body).map_err(|e| ProviderError::config(provider, format!("cannot serialize request body: {e}")))?;
        let mut headers: Vec<(String, String)> = vec![("content-type".into(), "application/json".into())];
        headers.extend(req.headers.iter().cloned());
        if dep.provider.protocol() == Protocol::Bedrock {
            // SigV4 covers the exact bytes and headers sent, `extra_headers` included; sign last.
            let mut signed_over = headers.clone();
            signed_over.extend(dep.extra_headers.iter().cloned());
            let signed = bedrock::sign_headers(dep, &req.url, &signed_over, &body, SystemTime::now())?;
            headers.extend(signed);
        }
        let builder = self.http.post(&req.url).body(body);
        self.execute(dep, builder, &headers, timeout).await
    }

    /// Add the adapter's headers and then the deployment's `extra_headers`,
    /// set the timeout and send; non-2xx responses become classified errors.
    pub(crate) async fn execute(
        &self,
        dep: &Deployment,
        builder: reqwest::RequestBuilder,
        req_headers: &[(String, String)],
        timeout: Option<Duration>,
    ) -> Result<reqwest::Response, ProviderError> {
        let provider = dep.provider.name();
        let mut headers = HeaderMap::new();
        for (name, value) in req_headers.iter().chain(&dep.extra_headers) {
            let name =
                HeaderName::from_bytes(name.as_bytes()).map_err(|_| ProviderError::config(provider, format!("invalid header name '{name}'")))?;
            let mut value =
                HeaderValue::from_str(value).map_err(|_| ProviderError::config(provider, format!("invalid value for header '{name}'")))?;
            if is_credential(&name) {
                value.set_sensitive(true);
            }
            // Deployment `extra_headers` come last and override.
            headers.insert(name, value);
        }
        let mut builder = builder.headers(headers);
        if let Some(t) = timeout {
            builder = builder.timeout(t);
        }
        let response = builder.send().await.map_err(|e| ProviderError::from_reqwest(provider, e))?;
        let status = response.status();
        if status.is_success() {
            return Ok(response);
        }
        let retry_after = retry_after(response.headers());
        let body = response.text().await.unwrap_or_default();
        Err(ProviderError::from_upstream(provider, status.as_u16(), &body, retry_after))
    }
}

fn is_credential(name: &HeaderName) -> bool {
    matches!(name.as_str(), "authorization" | "api-key" | "x-api-key" | "x-goog-api-key" | "x-amz-security-token")
}

/// `retry-after-ms` (OpenAI) or `retry-after` in seconds.
fn retry_after(headers: &HeaderMap) -> Option<Duration> {
    let parse = |name: &str| headers.get(name)?.to_str().ok()?.trim().parse::<f64>().ok();
    let secs = parse("retry-after-ms").map(|ms| ms / 1000.0).or_else(|| parse("retry-after"))?;
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
        h.insert("retry-after", HeaderValue::from_static("Wed, 21 Oct 2015 07:28:00 GMT"));
        assert_eq!(retry_after(&h), None);
    }

    #[test]
    fn builds_with_defaults() {
        assert!(Client::new(HttpSettings::default()).is_ok());
    }
}
