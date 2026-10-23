//! Errors in OpenAI's shape, `{"error": {"message", "type", "param", "code"}}`,
//! with the status codes LiteLLM uses.

use axum::http::StatusCode;
use axum::response::{IntoResponse, Response};
use gateway_kernel::Error as Refusal;

#[derive(Debug, Clone)]
pub struct ApiError {
    pub status: StatusCode,
    pub kind: &'static str,
    pub message: String,
}

impl ApiError {
    pub fn new(status: StatusCode, kind: &'static str, message: impl Into<String>) -> Self {
        ApiError { status, kind, message: message.into() }
    }

    pub fn bad_request(message: impl Into<String>) -> Self {
        Self::new(StatusCode::BAD_REQUEST, "invalid_request_error", message)
    }

    pub fn unauthorized(message: impl Into<String>) -> Self {
        Self::new(StatusCode::UNAUTHORIZED, "auth_error", message)
    }

    pub fn not_found(message: impl Into<String>) -> Self {
        Self::new(StatusCode::NOT_FOUND, "not_found_error", message)
    }

    pub fn unavailable(message: impl Into<String>) -> Self {
        Self::new(StatusCode::SERVICE_UNAVAILABLE, "service_unavailable", message)
    }

    pub fn internal(message: impl Into<String>) -> Self {
        Self::new(StatusCode::INTERNAL_SERVER_ERROR, "internal_server_error", message)
    }

    /// The kernel's refusal, as LiteLLM reports the same condition.
    pub fn refusal(e: Refusal) -> Self {
        use StatusCode as S;
        let (status, kind, message) = match e {
            Refusal::Unauthorized => (S::UNAUTHORIZED, "auth_error", "Authentication Error, Invalid proxy server token passed."),
            Refusal::Forbidden => (S::FORBIDDEN, "auth_error", "Only an admin key can do this."),
            Refusal::NotFound => (S::NOT_FOUND, "not_found_error", "Not found."),
            Refusal::KeyBlocked => (S::UNAUTHORIZED, "auth_error", "Authentication Error - Key is blocked."),
            Refusal::KeyExpired => (S::UNAUTHORIZED, "auth_error", "Authentication Error - Expired Key."),
            Refusal::TeamBlocked => (S::UNAUTHORIZED, "auth_error", "Authentication Error - Team is blocked."),
            Refusal::ModelNotFound => (S::BAD_REQUEST, "invalid_request_error", "Invalid model name passed in model."),
            Refusal::ModelNotAllowed => (S::UNAUTHORIZED, "auth_error", "Authentication Error - key not allowed to access model."),
            Refusal::KeyRateLimited => (S::TOO_MANY_REQUESTS, "rate_limit_error", "Rate limit exceeded for this key (rpm/tpm)."),
            Refusal::TeamRateLimited => (S::TOO_MANY_REQUESTS, "rate_limit_error", "Rate limit exceeded for this team (rpm/tpm)."),
            Refusal::KeyParallelLimit => (S::TOO_MANY_REQUESTS, "rate_limit_error", "Max parallel request limit reached for this key."),
            Refusal::KeyBudgetExceeded => (S::BAD_REQUEST, "budget_exceeded", "ExceededBudget: the key's budget does not cover this request."),
            Refusal::TeamBudgetExceeded => (S::BAD_REQUEST, "budget_exceeded", "ExceededBudget: the team's budget does not cover this request."),
            Refusal::NoDeployment => (
                S::TOO_MANY_REQUESTS,
                "rate_limit_error",
                "No deployments available for selected model; all are cooling down, rate limited or failed.",
            ),
            Refusal::NotExpired => (S::CONFLICT, "invalid_request_error", "The reservation has not expired yet."),
            Refusal::InUse => (S::CONFLICT, "invalid_request_error", "The team still has keys."),
            Refusal::Overflow => (S::INTERNAL_SERVER_ERROR, "internal_server_error", "Id space exhausted."),
        };
        Self::new(status, kind, message)
    }

    pub fn body(&self) -> serde_json::Value {
        serde_json::json!({
            "error": {
                "message": self.message,
                "type": self.kind,
                "param": null,
                "code": self.status.as_u16().to_string(),
            }
        })
    }
}

impl From<crate::kernel::Unavailable> for ApiError {
    fn from(e: crate::kernel::Unavailable) -> Self {
        tracing::error!(error = %e, "engine unavailable");
        ApiError::unavailable("The gateway's database is unavailable.")
    }
}

impl IntoResponse for ApiError {
    fn into_response(self) -> Response {
        (self.status, axum::Json(self.body())).into_response()
    }
}

impl std::fmt::Display for ApiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ({}): {}", self.status, self.kind, self.message)
    }
}

impl std::error::Error for ApiError {}
