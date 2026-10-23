//! The OpenAI-compatible inference routes.
//!
//! Each call is `Admit`, the provider call, then `Settle`. The kernel picks
//! the deployment and decides every limit; this module only carries bytes,
//! retries on another deployment when the kernel's choice failed in a way
//! worth retrying (excluding the ones already tried), and moves on to the
//! configured fallback groups when a group has nothing left.
//!
//! The reservation covers the estimated prompt plus `max_tokens`. When the
//! client sets no `max_tokens`, the gateway sets one (the model's output
//! limit, capped by `default_max_tokens`), so a provider that honours it
//! never returns more completion tokens than were reserved; the budget
//! theorem (`proofs/Theorems.lean`) assumes settlements stay within their
//! reservations.

// Failures are finished axum `Response`s, returned as they are.
#![allow(clippy::result_large_err)]

use crate::error::ApiError;
use crate::kernel::Gateway;
use crate::registry::Deployed;
use crate::spend::usd;
use crate::AppState;
use axum::body::Body;
use axum::extract::{Path, State};
use axum::http::{HeaderMap, HeaderValue, StatusCode, header};
use axum::response::{IntoResponse, Response};
use axum::Json;
use bytes::Bytes;
use futures::StreamExt;
use gateway_kernel::{CallStatus, Command, Error as Refusal, Principal, Reply};
use gateway_providers::types::EmbeddingInput;
use gateway_providers::{ChatChunk, ChatRequest, ChatStream, EmbeddingRequest, ProviderError, estimate_prompt_tokens};
use h5i_app_http::Actor;
use serde_json::Value;
use std::time::Duration;

/// A provider failure as the client sees it: the upstream's status and error.
fn provider_response(e: &ProviderError) -> Response {
    let status = StatusCode::from_u16(e.status_code()).unwrap_or(StatusCode::BAD_GATEWAY);
    (status, Json(serde_json::to_value(e.to_openai_body()).unwrap_or(Value::Null))).into_response()
}

/// What went wrong in the last attempt, to report if nothing succeeds.
enum Failure {
    Refusal(Refusal),
    Provider(ProviderError),
}

impl Failure {
    fn into_response(self) -> Response {
        match self {
            Failure::Refusal(e) => ApiError::refusal(e).into_response(),
            Failure::Provider(e) => provider_response(&e),
        }
    }
}

/// A call the kernel admitted.
struct Admitted<'a> {
    reservation: u64,
    deployed: &'a Deployed,
    group: String,
    retries: usize,
    fallbacks: usize,
}

/// How a request walks the deployments: the kernel's choice in each group,
/// then the next group.
struct Attempts<'a> {
    st: &'a AppState,
    actor: Principal,
    groups: Vec<String>,
    group: usize,
    exclude: Vec<u64>,
    retries: usize,
    prompt_tokens: u64,
    max_tokens: u64,
    last: Option<Failure>,
}

impl<'a> Attempts<'a> {
    fn new(st: &'a AppState, actor: Principal, model: &str, prompt_tokens: u64, max_tokens: u64) -> Self {
        let model = st.settings.aliases.get(model).cloned().unwrap_or_else(|| model.to_string());
        let mut groups = vec![model.clone()];
        groups.extend(st.settings.fallbacks.get(&model).cloned().unwrap_or_default());
        Attempts { st, actor, groups, group: 0, exclude: Vec::new(), retries: 0, prompt_tokens, max_tokens, last: None }
    }

    fn primary(&self) -> &str {
        &self.groups[0]
    }

    /// The next admitted call, or the response to give up with.
    async fn next(&mut self) -> Result<Admitted<'a>, Response> {
        while self.group < self.groups.len() {
            let group = self.groups[self.group].clone();
            let cmd = Command::Admit {
                model: group.as_bytes().to_vec(),
                prompt_tokens: self.prompt_tokens,
                max_tokens: self.max_tokens,
                exclude: self.exclude.clone(),
            };
            let reply = match self.st.backend.run(&self.actor, &cmd).await {
                Ok(r) => r,
                Err(e) => return Err(ApiError::from(e).into_response()),
            };
            match reply {
                Ok(Reply::Admitted { reservation, deployment, .. }) => match self.st.registry.get(deployment) {
                    Some(deployed) => {
                        return Ok(Admitted { reservation, deployed, group, retries: self.retries, fallbacks: self.group });
                    }
                    None => {
                        // Synced from another config: not ours to call.
                        settle(self.st, &self.actor, reservation, 0, 0, CallStatus::Failure).await;
                        self.exclude.push(deployment);
                    }
                },
                Ok(r) => return Err(ApiError::internal(format!("unexpected reply {r:?}")).into_response()),
                // Nothing left in this group: fall back.
                Err(Refusal::NoDeployment) => {
                    self.last.get_or_insert(Failure::Refusal(Refusal::NoDeployment));
                    self.next_group();
                }
                // A fallback group this key cannot use is skipped.
                Err(Refusal::ModelNotFound | Refusal::ModelNotAllowed) if self.group > 0 => self.next_group(),
                Err(e) => return Err(ApiError::refusal(e).into_response()),
            }
        }
        Err(self.last.take().unwrap_or(Failure::Refusal(Refusal::NoDeployment)).into_response())
    }

    fn next_group(&mut self) {
        self.group += 1;
        self.exclude.clear();
    }

    /// Record a failed call; whether to try again.
    async fn failed(&mut self, a: &Admitted<'_>, e: ProviderError) -> bool {
        let retryable = e.is_retryable();
        let status = if retryable { CallStatus::Retryable } else { CallStatus::Failure };
        settle(self.st, &self.actor, a.reservation, 0, 0, status).await;
        tracing::warn!(deployment = %a.deployed.config_id, error = %e, retryable, "provider call failed");
        self.last = Some(Failure::Provider(e));
        if !retryable {
            return false;
        }
        self.exclude.push(a.deployed.spec.id);
        self.retries += 1;
        if self.exclude.len() > self.st.settings.num_retries as usize {
            self.next_group();
        }
        true
    }

    fn give_up(&mut self) -> Response {
        self.last.take().unwrap_or(Failure::Refusal(Refusal::NoDeployment)).into_response()
    }
}

/// Settle a reservation, retrying while the database is unavailable. If it
/// stays unavailable the reservation is released by the sweeper later,
/// uncharged; that is logged as an error.
async fn settle(st: &AppState, actor: &Principal, reservation: u64, prompt: u64, completion: u64, status: CallStatus) -> Option<u64> {
    let cmd = Command::Settle { reservation, prompt_tokens: prompt, completion_tokens: completion, status };
    for attempt in 0..5u32 {
        match st.backend.run(actor, &cmd).await {
            Ok(Ok(Reply::Settled { cost })) => return Some(cost),
            Ok(other) => {
                tracing::error!(reservation, ?other, "settle refused");
                return None;
            }
            Err(e) => {
                tracing::warn!(reservation, attempt, error = %e, "settle failed; retrying");
                tokio::time::sleep(Duration::from_millis(100 << attempt)).await;
            }
        }
    }
    tracing::error!(reservation, prompt, completion, "could not settle; the call goes uncharged");
    None
}

fn headers(a: &Admitted<'_>, cost: Option<u64>) -> HeaderMap {
    let mut h = HeaderMap::new();
    let mut put = |name: &'static str, v: String| {
        if let Ok(v) = HeaderValue::from_str(&v) {
            h.insert(name, v);
        }
    };
    put("x-litellm-model-id", a.deployed.config_id.clone());
    put("x-litellm-model-group", a.group.clone());
    put("x-litellm-attempted-retries", a.retries.to_string());
    put("x-litellm-attempted-fallbacks", a.fallbacks.to_string());
    if let Some(c) = cost {
        put("x-litellm-response-cost", usd(c).to_string());
    }
    h
}

fn parse<T: serde::de::DeserializeOwned>(body: Value) -> Result<T, Response> {
    serde_json::from_value(body).map_err(|e| ApiError::bad_request(format!("invalid request body: {e}")).into_response())
}

// ---------------------------------------------------------------------------
// Chat completions

pub async fn chat_completions(State(st): State<AppState>, actor: Actor<Gateway>, Json(body): Json<Value>) -> Response {
    match parse::<ChatRequest>(body) {
        Ok(req) => chat(st, *actor.principal(), req).await,
        Err(r) => r,
    }
}

/// Azure OpenAI's path: the model is in the URL.
pub async fn azure_chat_completions(
    State(st): State<AppState>,
    Path(model): Path<String>,
    actor: Actor<Gateway>,
    Json(mut body): Json<Value>,
) -> Response {
    if let Some(o) = body.as_object_mut() {
        o.insert("model".into(), Value::String(model));
    }
    chat_completions(State(st), actor, Json(body)).await
}

async fn chat(st: AppState, actor: Principal, mut req: ChatRequest) -> Response {
    let prompt_tokens = estimate_prompt_tokens(&req);
    let model = req.model.clone();
    let max_tokens = match req.max_output_tokens() {
        Some(n) => n,
        None => {
            let limit = st.settings.default_max_tokens;
            let n = st.registry.max_output_tokens(st.settings.aliases.get(&model).unwrap_or(&model)).map_or(limit, |m| m.min(limit));
            req.max_completion_tokens = Some(n);
            n
        }
    };
    let stream = req.stream == Some(true);
    let mut attempts = Attempts::new(&st, actor, &model, prompt_tokens, max_tokens);
    loop {
        let a = match attempts.next().await {
            Ok(a) => a,
            Err(r) => return r,
        };
        let dep = &a.deployed.deployment;
        if stream {
            match st.client.chat_stream(dep, &req).await {
                Ok(s) => return stream_response(&st, actor, &a, s, prompt_tokens, req.wants_stream_usage()),
                Err(e) => {
                    if !attempts.failed(&a, e).await {
                        return attempts.give_up();
                    }
                }
            }
        } else {
            match st.client.chat(dep, &req).await {
                Ok(resp) => {
                    let (p, c) = match &resp.usage {
                        Some(u) => (u.prompt_tokens, u.completion_tokens),
                        None => (prompt_tokens, estimate_text(&serde_json::to_string(&resp.choices).unwrap_or_default())),
                    };
                    let cost = settle(&st, &actor, a.reservation, p, c, CallStatus::Success).await;
                    tracing::debug!(model = %attempts.primary(), deployment = %a.deployed.config_id, p, c, ?cost, "chat completion");
                    return (headers(&a, cost), Json(resp)).into_response();
                }
                Err(e) => {
                    if !attempts.failed(&a, e).await {
                        return attempts.give_up();
                    }
                }
            }
        }
    }
}

/// About four characters per token.
fn estimate_text(s: &str) -> u64 {
    (s.chars().count() as u64).div_ceil(4)
}

/// Settles a streamed call when the stream ends, fails, or the client goes away.
struct StreamSettle {
    st: AppState,
    actor: Principal,
    reservation: u64,
    prompt_estimate: u64,
    usage: Option<(u64, u64)>,
    chars: u64,
    status: CallStatus,
    settled: bool,
}

impl StreamSettle {
    fn observe(&mut self, chunk: &ChatChunk) {
        if let Some(u) = &chunk.usage {
            self.usage = Some((u.prompt_tokens, u.completion_tokens));
        }
        for c in &chunk.choices {
            self.chars += serde_json::to_string(&c.delta).map(|s| s.len() as u64).unwrap_or(0);
        }
    }

    fn finish(&mut self) {
        if self.settled {
            return;
        }
        self.settled = true;
        let (p, c) = self.usage.unwrap_or((self.prompt_estimate, self.chars.div_ceil(4)));
        let (st, actor, reservation, status) = (self.st.clone(), self.actor, self.reservation, self.status);
        if let Ok(rt) = tokio::runtime::Handle::try_current() {
            rt.spawn(async move {
                settle(&st, &actor, reservation, p, c, status).await;
            });
        }
    }
}

impl Drop for StreamSettle {
    fn drop(&mut self) {
        self.finish();
    }
}

fn sse(v: &impl serde::Serialize) -> Bytes {
    let mut b = b"data: ".to_vec();
    b.extend(serde_json::to_vec(v).unwrap_or_default());
    b.extend_from_slice(b"\n\n");
    Bytes::from(b)
}

fn stream_response(st: &AppState, actor: Principal, a: &Admitted<'_>, s: ChatStream, prompt_estimate: u64, wants_usage: bool) -> Response {
    let guard = StreamSettle {
        st: st.clone(),
        actor,
        reservation: a.reservation,
        prompt_estimate,
        usage: None,
        chars: 0,
        status: CallStatus::Success,
        settled: false,
    };
    // State: the upstream stream, the settlement, and whether `[DONE]` went out.
    let body = futures::stream::unfold((s, guard, false), move |(mut s, mut guard, done)| async move {
        if done {
            return None;
        }
        loop {
            match s.next().await {
                Some(Ok(chunk)) => {
                    guard.observe(&chunk);
                    // Usage is always requested upstream for billing; pass it on only if asked.
                    if chunk.choices.is_empty() && chunk.usage.is_some() && !wants_usage {
                        continue;
                    }
                    return Some((Ok::<_, std::convert::Infallible>(sse(&chunk)), (s, guard, false)));
                }
                Some(Err(e)) => {
                    guard.status = if e.is_retryable() { CallStatus::Retryable } else { CallStatus::Failure };
                    guard.finish();
                    return Some((Ok(sse(&e.to_openai_body())), (s, guard, true)));
                }
                None => {
                    guard.finish();
                    return Some((Ok(Bytes::from_static(b"data: [DONE]\n\n")), (s, guard, true)));
                }
            }
        }
    });
    let mut h = headers(a, None);
    h.insert(header::CONTENT_TYPE, HeaderValue::from_static("text/event-stream"));
    h.insert(header::CACHE_CONTROL, HeaderValue::from_static("no-cache"));
    (h, Body::from_stream(body)).into_response()
}

// ---------------------------------------------------------------------------
// Embeddings

pub async fn embeddings(State(st): State<AppState>, actor: Actor<Gateway>, Json(body): Json<Value>) -> Response {
    let req = match parse::<EmbeddingRequest>(body) {
        Ok(r) => r,
        Err(r) => return r,
    };
    let actor = *actor.principal();
    let prompt_tokens = match &req.input {
        EmbeddingInput::Text(s) => estimate_text(s),
        EmbeddingInput::Texts(v) => v.iter().map(|s| estimate_text(s)).sum(),
        EmbeddingInput::Tokens(t) => t.len() as u64,
        EmbeddingInput::TokenBatches(b) => b.iter().map(|t| t.len() as u64).sum(),
    };
    let mut attempts = Attempts::new(&st, actor, &req.model, prompt_tokens, 0);
    loop {
        let a = match attempts.next().await {
            Ok(a) => a,
            Err(r) => return r,
        };
        match st.client.embeddings(&a.deployed.deployment, &req).await {
            Ok(resp) => {
                let cost = settle(&st, &actor, a.reservation, resp.usage.prompt_tokens, 0, CallStatus::Success).await;
                return (headers(&a, cost), Json(resp)).into_response();
            }
            Err(e) => {
                if !attempts.failed(&a, e).await {
                    return attempts.give_up();
                }
            }
        }
    }
}
