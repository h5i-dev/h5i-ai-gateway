//! Anthropic's Messages API (`/v1/messages`), translated to and from the chat path.
//!
//! A request in Anthropic's format becomes an OpenAI chat request
//! ([`gateway_providers::formats::anthropic_messages`]), goes through
//! [`run_chat`] like any chat completion (admission, budgets, rate limits,
//! routing, retries, fallbacks, settlement), and its answer is translated
//! back: a Messages response, or Anthropic's SSE events when streaming.
//! Every provider is reachable this way, as with LiteLLM's `/v1/messages`.
//! Errors use Anthropic's shape, `{"type": "error", "error": {"type",
//! "message"}}`, with the same status codes as the chat path.

// Failures are finished axum `Response`s, returned as they are.
#![allow(clippy::result_large_err)]

use crate::AppState;
use crate::proxy::{ChatOutcome, Failure, run_chat, sse_response};
use axum::Json;
use axum::Router;
use axum::extract::State;
use axum::http::{HeaderMap, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::routing::post;
use bytes::Bytes;
use futures::StreamExt;
use gateway_kernel::Principal;
use gateway_providers::formats::anthropic_messages::{self as am, MessagesRequest};
use gateway_providers::formats::{Target, adapt_to_target};
use gateway_providers::{ChatRequest, estimate_prompt_tokens};
use h5i_app_http::Authenticator;
use serde_json::json;

/// The routes of this module.
pub fn routes() -> Router<AppState> {
    Router::new()
        .route("/v1/messages", post(messages))
        .route("/anthropic/v1/messages", post(messages))
        .route("/v1/messages/count_tokens", post(count_tokens))
        .route("/anthropic/v1/messages/count_tokens", post(count_tokens))
}

/// An error in Anthropic's shape.
fn error(status: StatusCode, message: &str) -> Response {
    (status, Json(am::error_body(status.as_u16(), message))).into_response()
}

fn failure(f: Failure) -> Response {
    error(f.status(), &f.message())
}

/// Authenticate here rather than with the `Actor` extractor, so that a bad
/// key gets an Anthropic-shaped error.
fn authenticate(st: &AppState, headers: &HeaderMap) -> Result<Principal, Response> {
    st.keys.authenticate(headers).map_err(|e| error(StatusCode::UNAUTHORIZED, &e.0))
}

fn parse(body: &[u8]) -> Result<MessagesRequest, Response> {
    serde_json::from_slice(body).map_err(|e| error(StatusCode::BAD_REQUEST, &format!("invalid request body: {e}")))
}

/// What every deployment the request may reach understands: those of the
/// model group (after aliases) and of its fallback groups.
pub(crate) fn target(st: &AppState, model: &str) -> Target {
    let group = st.settings.aliases.get(model).map_or(model, String::as_str);
    let mut groups = vec![group];
    groups.extend(st.settings.fallbacks.get(group).into_iter().flatten().map(String::as_str));
    Target::all(st.registry.all().into_iter().filter(|d| groups.contains(&d.model_name.as_str())).map(|d| &d.deployment))
}

/// The chat request for a Messages request, adapted to its deployments.
fn chat_request(st: &AppState, req: &MessagesRequest) -> Result<ChatRequest, Response> {
    let mut chat = am::to_chat_request(req).map_err(|e| error(StatusCode::BAD_REQUEST, &e.message))?;
    adapt_to_target(&mut chat, target(st, &req.model));
    Ok(chat)
}

/// `POST /v1/messages`.
pub async fn messages(State(st): State<AppState>, headers: HeaderMap, body: Bytes) -> Response {
    let actor = match authenticate(&st, &headers) {
        Ok(a) => a,
        Err(r) => return r,
    };
    let req = match parse(&body) {
        Ok(r) => r,
        Err(r) => return r,
    };
    let chat = match chat_request(&st, &req) {
        Ok(c) => c,
        Err(r) => return r,
    };
    let estimate = estimate_prompt_tokens(&chat);
    match run_chat(&st, actor, chat).await {
        Ok((ChatOutcome::Complete(resp), info)) => (info.headers(), Json(am::from_chat_response(&resp, &req.model))).into_response(),
        Ok((ChatOutcome::Stream(s), info)) => {
            let encoder = am::MessagesStream::new(req.model.clone(), estimate);
            let body = futures::stream::unfold((s, encoder, false), |(mut s, mut enc, done)| async move {
                if done {
                    return None;
                }
                let (events, done) = match s.next().await {
                    Some(Ok(chunk)) => (enc.on_chunk(&chunk), false),
                    Some(Err(e)) => (enc.error(e.status_code(), e.message()), true),
                    None => (enc.finish(), true),
                };
                Some((Bytes::from(am::encode_events(&events)), (s, enc, done)))
            })
            .filter(|b| futures::future::ready(!b.is_empty()));
            sse_response(&info, body)
        }
        Err(f) => failure(f),
    }
}

/// `POST /v1/messages/count_tokens`: the gateway's prompt estimate (the
/// one admission reserves for); nothing is called or charged.
pub async fn count_tokens(State(st): State<AppState>, headers: HeaderMap, body: Bytes) -> Response {
    if let Err(r) = authenticate(&st, &headers) {
        return r;
    }
    let req = match parse(&body) {
        Ok(r) => r,
        Err(r) => return r,
    };
    match chat_request(&st, &req) {
        Ok(chat) => Json(json!({"input_tokens": estimate_prompt_tokens(&chat)})).into_response(),
        Err(r) => r,
    }
}
