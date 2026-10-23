//! Classified provider errors.
//!
//! Every failure surfaced by this crate is a [`ProviderError`]: an
//! [`ErrorKind`] (what went wrong, mirroring LiteLLM's exception classes), the
//! HTTP status the gateway should answer with, and the upstream message and
//! error metadata where available. [`ProviderError::is_retryable`] tells the
//! router whether to count the failure against the deployment and try another
//! one; [`ProviderError::to_openai_body`] renders the OpenAI error envelope.

use std::time::Duration;

use serde_json::Value;

use crate::types::{ErrorBody, ErrorDetail};

/// Failure category.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    /// Malformed or unsupported request (400, 413, 422, other 4xx).
    BadRequest,
    /// The prompt exceeds the model's context window (400).
    ContextWindowExceeded,
    /// Rejected by the provider's content policy / safety filter (400).
    ContentPolicy,
    /// Model or deployment not found (404).
    NotFound,
    /// Invalid or missing credentials (401).
    Authentication,
    /// Credentials valid but not allowed (403).
    PermissionDenied,
    /// Upstream rate limit or quota (429).
    RateLimited,
    /// No (complete) response within the configured timeout (408).
    Timeout,
    /// Upstream server error or overload (5xx, Anthropic 529).
    ServiceUnavailable,
    /// Could not reach the upstream (DNS, TCP, TLS, connection reset).
    Connection,
    /// The upstream answered 2xx but the body could not be understood.
    InvalidResponse,
    /// The deployment is misconfigured (unknown provider, missing api_base or
    /// key, unresolved `os.environ/` reference).
    Config,
}

impl ErrorKind {
    /// Default HTTP status for errors of this kind.
    fn default_status(self) -> u16 {
        match self {
            ErrorKind::BadRequest | ErrorKind::ContextWindowExceeded | ErrorKind::ContentPolicy => 400,
            ErrorKind::NotFound => 404,
            ErrorKind::Authentication => 401,
            ErrorKind::PermissionDenied => 403,
            ErrorKind::RateLimited => 429,
            ErrorKind::Timeout => 408,
            ErrorKind::ServiceUnavailable => 503,
            ErrorKind::Connection | ErrorKind::InvalidResponse | ErrorKind::Config => 500,
        }
    }

    /// OpenAI-style `error.type` used when the upstream supplied none.
    fn openai_type(self) -> &'static str {
        match self {
            ErrorKind::BadRequest | ErrorKind::ContextWindowExceeded | ErrorKind::ContentPolicy | ErrorKind::NotFound => "invalid_request_error",
            ErrorKind::Authentication => "authentication_error",
            ErrorKind::PermissionDenied => "permission_error",
            ErrorKind::RateLimited => "rate_limit_error",
            ErrorKind::Timeout => "timeout_error",
            ErrorKind::ServiceUnavailable | ErrorKind::Connection | ErrorKind::InvalidResponse | ErrorKind::Config => "api_error",
        }
    }
}

/// An upstream or adapter failure. Boxed so `Result<_, ProviderError>` stays
/// one pointer wide.
#[derive(Debug, Clone, thiserror::Error)]
#[error("{0}")]
pub struct ProviderError(Box<Inner>);

#[derive(Debug, Clone)]
struct Inner {
    kind: ErrorKind,
    status: u16,
    message: String,
    provider: String,
    upstream_type: Option<String>,
    param: Option<String>,
    code: Option<String>,
    retry_after: Option<Duration>,
}

impl std::fmt::Display for Inner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {:?} ({}): {}", self.provider, self.kind, self.status, self.message)
    }
}

impl ProviderError {
    /// An error of `kind` with the kind's default status.
    pub fn new(kind: ErrorKind, provider: impl Into<String>, message: impl Into<String>) -> Self {
        Self(Box::new(Inner {
            kind,
            status: kind.default_status(),
            message: message.into(),
            provider: provider.into(),
            upstream_type: None,
            param: None,
            code: None,
            retry_after: None,
        }))
    }

    pub(crate) fn bad_request(provider: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(ErrorKind::BadRequest, provider, message)
    }

    pub(crate) fn config(provider: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(ErrorKind::Config, provider, message)
    }

    pub(crate) fn invalid_response(provider: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(ErrorKind::InvalidResponse, provider, message)
    }

    /// Classify a non-2xx upstream response.
    ///
    /// `body` is parsed leniently: OpenAI/Anthropic `{"error": {...}}`,
    /// Gemini `{"error": {"code", "message", "status"}}`, a JSON array wrapping
    /// either (Gemini streaming), or plain text.
    pub fn from_upstream(provider: impl Into<String>, status: u16, body: &str, retry_after: Option<Duration>) -> Self {
        let parsed = ParsedBody::parse(body);
        let message = parsed.message.clone().unwrap_or_else(|| default_message(status, body));
        let kind = classify(status, &parsed, &message);
        // Keep the upstream status unless the classification overrides its
        // meaning (e.g. Gemini's 400 for an invalid API key).
        let status = match (kind, status) {
            (ErrorKind::Authentication, 400) => 401,
            (_, s) if (400..=599).contains(&s) => s,
            _ => kind.default_status(),
        };
        Self(Box::new(Inner {
            kind,
            status,
            message,
            provider: provider.into(),
            upstream_type: parsed.kind,
            param: parsed.param,
            code: parsed.code,
            retry_after,
        }))
    }

    /// Classify a transport-level failure from reqwest.
    /// The URL is stripped from the message: it may carry an API key
    /// (Gemini's `?key=`).
    pub(crate) fn from_reqwest(provider: &str, err: reqwest::Error) -> Self {
        let err = err.without_url();
        let kind = if err.is_timeout() {
            ErrorKind::Timeout
        } else if err.is_decode() {
            ErrorKind::InvalidResponse
        } else if err.is_builder() {
            ErrorKind::Config
        } else {
            ErrorKind::Connection
        };
        Self::new(kind, provider, error_chain(&err))
    }

    /// An error reported inside a 200 streaming response (e.g. Anthropic's
    /// `event: error`), classified by its `type` like LiteLLM does.
    pub(crate) fn from_stream_error(provider: &str, error: &Value) -> Self {
        let status = match error.get("type").and_then(Value::as_str) {
            Some("overloaded_error") => 529,
            Some("rate_limit_error") => 429,
            Some("invalid_request_error") => 400,
            Some("authentication_error") => 401,
            Some("permission_error") => 403,
            Some("not_found_error") => 404,
            Some("request_too_large") => 413,
            _ => 500,
        };
        let body = serde_json::json!({ "error": error }).to_string();
        Self::from_upstream(provider, status, &body, None)
    }

    pub fn kind(&self) -> ErrorKind {
        self.0.kind
    }

    /// HTTP status the gateway should return to its client: the upstream
    /// status when there was one, otherwise the kind's default (408 for
    /// timeouts, 500 for connection/parse/config failures).
    pub fn status_code(&self) -> u16 {
        self.0.status
    }

    /// Upstream (or adapter) error message.
    pub fn message(&self) -> &str {
        &self.0.message
    }

    /// Provider name (e.g. `"anthropic"`).
    pub fn provider(&self) -> &str {
        &self.0.provider
    }

    /// `Retry-After` advertised by the upstream, if any.
    pub fn retry_after(&self) -> Option<Duration> {
        self.0.retry_after
    }

    /// Should the router count this failure against the deployment and try
    /// another one? True for rate limits, 5xx, timeouts, connection failures,
    /// unparseable responses, authentication failures (LiteLLM cools a
    /// deployment down on 401) and misconfigured deployments. False for
    /// failures caused by the request itself.
    pub fn is_retryable(&self) -> bool {
        match self.0.kind {
            ErrorKind::RateLimited
            | ErrorKind::Timeout
            | ErrorKind::ServiceUnavailable
            | ErrorKind::Connection
            | ErrorKind::InvalidResponse
            | ErrorKind::Authentication
            | ErrorKind::Config => true,
            ErrorKind::BadRequest
            | ErrorKind::ContextWindowExceeded
            | ErrorKind::ContentPolicy
            | ErrorKind::NotFound
            | ErrorKind::PermissionDenied => false,
        }
    }

    /// The OpenAI error envelope to send to the client, with
    /// [`status_code`](Self::status_code) as the HTTP status. The upstream's
    /// `type`/`param`/`code` are kept when present; `code` defaults to the
    /// status as a string (LiteLLM convention).
    pub fn to_openai_body(&self) -> ErrorBody {
        ErrorBody {
            error: ErrorDetail {
                message: self.0.message.clone(),
                kind: Some(self.0.upstream_type.clone().unwrap_or_else(|| self.0.kind.openai_type().to_owned())),
                param: self.0.param.clone(),
                code: Some(self.0.code.clone().unwrap_or_else(|| self.0.status.to_string())),
            },
        }
    }
}

/// Fields extracted from an upstream error body.
#[derive(Debug, Default)]
struct ParsedBody {
    message: Option<String>,
    kind: Option<String>,
    param: Option<String>,
    code: Option<String>,
}

impl ParsedBody {
    fn parse(body: &str) -> Self {
        let Ok(value) = serde_json::from_str::<Value>(body) else {
            return Self::default();
        };
        // Gemini streaming errors arrive as a one-element array.
        let value = match value {
            Value::Array(mut items) if !items.is_empty() => items.swap_remove(0),
            v => v,
        };
        let err = match value.get("error") {
            Some(Value::String(s)) => {
                return Self { message: Some(s.clone()), ..Self::default() };
            }
            Some(e @ Value::Object(_)) => e,
            _ => &value,
        };
        let s = |key: &str| match err.get(key) {
            Some(Value::String(s)) => Some(s.clone()),
            Some(Value::Number(n)) => Some(n.to_string()),
            _ => None,
        };
        Self {
            message: s("message").or_else(|| s("detail")),
            // Gemini puts the symbolic code in `status`.
            kind: s("type").or_else(|| s("status")),
            param: s("param"),
            code: s("code"),
        }
    }
}

fn default_message(status: u16, body: &str) -> String {
    let body = body.trim();
    if body.is_empty() {
        format!("upstream returned HTTP {status}")
    } else {
        // Bound the size of non-JSON bodies (HTML error pages etc.).
        let mut end = body.len().min(1000);
        while !body.is_char_boundary(end) {
            end -= 1;
        }
        body[..end].to_owned()
    }
}

/// Map status + body to a kind, refining 400s like LiteLLM's
/// `exception_mapping_utils` does.
fn classify(status: u16, parsed: &ParsedBody, message: &str) -> ErrorKind {
    let lower = message.to_ascii_lowercase();
    let kind_or_code = |needle: &str| {
        parsed.kind.as_deref().is_some_and(|k| k.eq_ignore_ascii_case(needle))
            || parsed.code.as_deref().is_some_and(|c| c.eq_ignore_ascii_case(needle))
    };
    match status {
        400 | 413 | 422 => {
            if kind_or_code("context_length_exceeded") || CONTEXT_WINDOW_PHRASES.iter().any(|p| lower.contains(p)) {
                ErrorKind::ContextWindowExceeded
            } else if kind_or_code("content_filter")
                || kind_or_code("content_policy_violation")
                || CONTENT_POLICY_PHRASES.iter().any(|p| lower.contains(p))
            {
                ErrorKind::ContentPolicy
            } else if lower.contains("api key not valid") || lower.contains("invalid api key") {
                ErrorKind::Authentication
            } else {
                ErrorKind::BadRequest
            }
        }
        401 => ErrorKind::Authentication,
        403 => ErrorKind::PermissionDenied,
        404 => ErrorKind::NotFound,
        408 => ErrorKind::Timeout,
        429 => ErrorKind::RateLimited,
        500..=599 => ErrorKind::ServiceUnavailable,
        _ => ErrorKind::BadRequest,
    }
}

const CONTEXT_WINDOW_PHRASES: &[&str] = &[
    "context length",
    "context_length_exceeded",
    "context window",
    "maximum context",
    "prompt is too long",
    "input is too long",
    "too many tokens",
    "exceeds the maximum number of tokens",
    "input token count",
];

const CONTENT_POLICY_PHRASES: &[&str] =
    &["content management policy", "content_policy_violation", "content filter", "content_filter", "safety system", "responsibleaipolicyviolation"];

/// `Display` of an error and its sources, which carry the useful detail for
/// reqwest errors (e.g. "connection refused").
fn error_chain(err: &dyn std::error::Error) -> String {
    let mut out = err.to_string();
    let mut source = err.source();
    while let Some(s) = source {
        out.push_str(": ");
        out.push_str(&s.to_string());
        source = s.source();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn upstream(status: u16, body: &str) -> ProviderError {
        ProviderError::from_upstream("p", status, body, None)
    }

    #[test]
    fn status_mapping_and_retryability() {
        let cases = [
            (400, ErrorKind::BadRequest, false),
            (401, ErrorKind::Authentication, true),
            (403, ErrorKind::PermissionDenied, false),
            (404, ErrorKind::NotFound, false),
            (408, ErrorKind::Timeout, true),
            (409, ErrorKind::BadRequest, false),
            (422, ErrorKind::BadRequest, false),
            (429, ErrorKind::RateLimited, true),
            (500, ErrorKind::ServiceUnavailable, true),
            (502, ErrorKind::ServiceUnavailable, true),
            (529, ErrorKind::ServiceUnavailable, true),
        ];
        for (status, kind, retryable) in cases {
            let e = upstream(status, "");
            assert_eq!(e.kind(), kind, "status {status}");
            assert_eq!(e.is_retryable(), retryable, "status {status}");
            assert_eq!(e.status_code(), status);
        }
    }

    #[test]
    fn openai_error_body_is_preserved() {
        let e = upstream(400, r#"{"error":{"message":"bad temp","type":"invalid_request_error","param":"temperature","code":null}}"#);
        let body = e.to_openai_body();
        assert_eq!(body.error.message, "bad temp");
        assert_eq!(body.error.kind.as_deref(), Some("invalid_request_error"));
        assert_eq!(body.error.param.as_deref(), Some("temperature"));
        assert_eq!(body.error.code.as_deref(), Some("400"));
    }

    #[test]
    fn anthropic_and_gemini_bodies() {
        let e = upstream(529, r#"{"type":"error","error":{"type":"overloaded_error","message":"Overloaded"}}"#);
        assert_eq!(e.message(), "Overloaded");
        assert_eq!(e.to_openai_body().error.kind.as_deref(), Some("overloaded_error"));

        let e = upstream(400, r#"[{"error":{"code":400,"message":"API key not valid. Please pass a valid API key.","status":"INVALID_ARGUMENT"}}]"#);
        assert_eq!(e.kind(), ErrorKind::Authentication);
        assert_eq!(e.status_code(), 401);
        assert!(e.is_retryable());
    }

    #[test]
    fn refines_bad_requests() {
        let e = upstream(400, r#"{"error":{"message":"x","code":"context_length_exceeded"}}"#);
        assert_eq!(e.kind(), ErrorKind::ContextWindowExceeded);
        let e = upstream(400, r#"{"error":{"type":"invalid_request_error","message":"prompt is too long: 210000 tokens > 200000 maximum"}}"#);
        assert_eq!(e.kind(), ErrorKind::ContextWindowExceeded);
        let e = upstream(
            400,
            r#"{"error":{"message":"The response was filtered due to the prompt triggering Azure OpenAI's content management policy.","code":"content_filter"}}"#,
        );
        assert_eq!(e.kind(), ErrorKind::ContentPolicy);
        assert!(!e.is_retryable());
    }

    #[test]
    fn plain_text_and_empty_bodies() {
        assert_eq!(upstream(502, "<html>bad gateway</html>").message(), "<html>bad gateway</html>");
        assert_eq!(upstream(503, "").message(), "upstream returned HTTP 503");
        let long = "é".repeat(2000);
        assert!(upstream(500, &long).message().len() <= 1000);
    }

    #[test]
    fn stream_errors_are_classified_by_type() {
        let e = ProviderError::from_stream_error("anthropic", &serde_json::json!({"type": "overloaded_error", "message": "Overloaded"}));
        assert_eq!(e.status_code(), 529);
        assert!(e.is_retryable());
        let e = ProviderError::from_stream_error("anthropic", &serde_json::json!({"type": "api_error", "message": "x"}));
        assert_eq!(e.status_code(), 500);
    }

    #[test]
    fn local_kinds_have_default_statuses() {
        let e = ProviderError::new(ErrorKind::Timeout, "p", "slow");
        assert_eq!(e.status_code(), 408);
        assert_eq!(e.to_openai_body().error.kind.as_deref(), Some("timeout_error"));
        assert_eq!(ProviderError::config("p", "x").status_code(), 500);
        assert!(ProviderError::new(ErrorKind::Connection, "p", "refused").is_retryable());
    }
}
