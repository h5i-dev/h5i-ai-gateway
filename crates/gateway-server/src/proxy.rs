//! The inference path shared by every endpoint.
//!
//! Each call is `Admit`, the provider call, then `Settle`. The kernel picks
//! the deployment and decides every limit; this module only carries bytes,
//! retries on another deployment when the kernel's choice failed in a way
//! worth retrying (excluding the ones already tried), and moves on to the
//! configured fallback groups when a group has nothing left.
//!
//! Endpoints use one of three entry points:
//! - [`call`]: any non-streaming provider call, measured in the deployment's
//!   units (tokens for chat and embeddings; images, seconds or characters for
//!   media deployments, whose prices are per unit).
//! - [`run_chat`]: a chat completion, streaming or not, in OpenAI's shape;
//!   the Anthropic Messages and Responses APIs translate to and from it.
//! - [`Attempts`]: the admission loop itself, for calls that settle later.
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
use futures::{Stream, StreamExt};
use gateway_kernel::{CallStatus, Command, Error as Refusal, Principal, Reply};
use gateway_providers::types::EmbeddingInput;
use gateway_providers::{ChatChunk, ChatRequest, ChatResponse, EmbeddingRequest, ProviderError, estimate_prompt_tokens};
use h5i_app_http::Actor;
use serde_json::Value;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

/// Why a call produced no answer: the kernel refused, the provider failed,
/// or something else went wrong (bad request, database unavailable).
#[derive(Debug)]
pub enum Failure {
    Refusal(Refusal),
    Provider(ProviderError),
    Api(ApiError),
}

impl Failure {
    /// The HTTP status a client should see.
    pub fn status(&self) -> StatusCode {
        match self {
            Failure::Refusal(e) => ApiError::refusal(*e).status,
            Failure::Provider(e) => StatusCode::from_u16(e.status_code()).unwrap_or(StatusCode::BAD_GATEWAY),
            Failure::Api(e) => e.status,
        }
    }

    /// A short machine-readable kind (`rate_limit_error`, `budget_exceeded`, …).
    pub fn kind(&self) -> String {
        match self {
            Failure::Refusal(e) => ApiError::refusal(*e).kind.to_string(),
            Failure::Provider(e) => e.to_openai_body().error.kind.clone().unwrap_or_else(|| "provider_error".into()),
            Failure::Api(e) => e.kind.to_string(),
        }
    }

    pub fn message(&self) -> String {
        match self {
            Failure::Refusal(e) => ApiError::refusal(*e).message,
            Failure::Provider(e) => e.message().to_string(),
            Failure::Api(e) => e.message.clone(),
        }
    }

    /// The error in OpenAI's shape.
    pub fn into_response(self) -> Response {
        match self {
            Failure::Refusal(e) => ApiError::refusal(e).into_response(),
            Failure::Provider(e) => {
                let status = StatusCode::from_u16(e.status_code()).unwrap_or(StatusCode::BAD_GATEWAY);
                (status, Json(serde_json::to_value(e.to_openai_body()).unwrap_or(Value::Null))).into_response()
            }
            Failure::Api(e) => e.into_response(),
        }
    }
}

impl From<ApiError> for Failure {
    fn from(e: ApiError) -> Self {
        Failure::Api(e)
    }
}

/// Where a call went, for the `x-litellm-*` headers and logs.
#[derive(Debug, Clone)]
pub struct CallInfo {
    pub deployment: String,
    pub group: String,
    pub retries: usize,
    pub fallbacks: usize,
    /// Nano-dollars charged; `None` until a streamed call settles.
    pub cost: Option<u64>,
}

impl CallInfo {
    pub fn headers(&self) -> HeaderMap {
        let mut h = HeaderMap::new();
        let mut put = |name: &'static str, v: String| {
            if let Ok(v) = HeaderValue::from_str(&v) {
                h.insert(name, v);
            }
        };
        put("x-litellm-model-id", self.deployment.clone());
        put("x-litellm-model-group", self.group.clone());
        put("x-litellm-attempted-retries", self.retries.to_string());
        put("x-litellm-attempted-fallbacks", self.fallbacks.to_string());
        if let Some(c) = self.cost {
            put("x-litellm-response-cost", usd(c).to_string());
        }
        h
    }
}

/// A call the kernel admitted.
pub struct Admitted<'a> {
    pub reservation: u64,
    pub deployed: &'a Deployed,
    pub group: String,
    pub retries: usize,
    pub fallbacks: usize,
}

impl Admitted<'_> {
    pub fn info(&self, cost: Option<u64>) -> CallInfo {
        CallInfo {
            deployment: self.deployed.config_id.clone(),
            group: self.group.clone(),
            retries: self.retries,
            fallbacks: self.fallbacks,
            cost,
        }
    }
}

/// How a request walks the deployments: the kernel's choice in each group,
/// then the next group.
pub struct Attempts<'a> {
    st: &'a AppState,
    actor: Principal,
    groups: Vec<String>,
    group: usize,
    exclude: Vec<u64>,
    retries: usize,
    prompt_units: u64,
    max_units: u64,
    last: Option<Failure>,
}

impl<'a> Attempts<'a> {
    /// `prompt_units`/`max_units` are what the reservation covers: input and
    /// output tokens for chat, or the deployment's own units.
    pub fn new(st: &'a AppState, actor: Principal, model: &str, prompt_units: u64, max_units: u64) -> Self {
        let model = st.settings.aliases.get(model).cloned().unwrap_or_else(|| model.to_string());
        let mut groups = vec![model.clone()];
        groups.extend(st.settings.fallbacks.get(&model).cloned().unwrap_or_default());
        Attempts { st, actor, groups, group: 0, exclude: Vec::new(), retries: 0, prompt_units, max_units, last: None }
    }

    /// The model group the client asked for (after aliases).
    pub fn primary(&self) -> &str {
        &self.groups[0]
    }

    /// The next admitted call, or why there is none.
    pub async fn next(&mut self) -> Result<Admitted<'a>, Failure> {
        while self.group < self.groups.len() {
            let group = self.groups[self.group].clone();
            let cmd = Command::Admit {
                model: group.as_bytes().to_vec(),
                prompt_tokens: self.prompt_units,
                max_tokens: self.max_units,
                exclude: self.exclude.clone(),
            };
            let reply = self.st.backend.run(&self.actor, &cmd).await.map_err(|e| Failure::Api(e.into()))?;
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
                Ok(r) => return Err(ApiError::internal(format!("unexpected reply {r:?}")).into()),
                // Nothing left in this group: fall back.
                Err(Refusal::NoDeployment) => {
                    self.last.get_or_insert(Failure::Refusal(Refusal::NoDeployment));
                    self.next_group();
                }
                // A fallback group this key cannot use is skipped.
                Err(Refusal::ModelNotFound | Refusal::ModelNotAllowed) if self.group > 0 => self.next_group(),
                Err(e) => return Err(Failure::Refusal(e)),
            }
        }
        Err(self.last.take().unwrap_or(Failure::Refusal(Refusal::NoDeployment)))
    }

    fn next_group(&mut self) {
        self.group += 1;
        self.exclude.clear();
    }

    /// Record a failed call; whether to try again.
    pub async fn failed(&mut self, a: &Admitted<'_>, e: ProviderError) -> bool {
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

    /// The failure to report once nothing is left to try.
    pub fn give_up(&mut self) -> Failure {
        self.last.take().unwrap_or(Failure::Refusal(Refusal::NoDeployment))
    }
}

/// Settle a reservation, retrying while the database is unavailable. If it
/// stays unavailable the reservation is released by the sweeper later,
/// uncharged; that is logged as an error.
pub async fn settle(st: &AppState, actor: &Principal, reservation: u64, prompt: u64, completion: u64, status: CallStatus) -> Option<u64> {
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

/// What a provider call used, in the deployment's units.
#[derive(Debug, Clone, Copy, Default)]
pub struct Units {
    pub prompt: u64,
    pub completion: u64,
}

/// One non-streaming provider call with the full admission, retry, fallback
/// and settlement path. `f` performs the call on the deployment the kernel
/// chose and reports the units used.
pub async fn call<T, F, Fut>(st: &AppState, actor: Principal, model: &str, prompt_units: u64, max_units: u64, mut f: F) -> Result<(T, CallInfo), Failure>
where
    F: FnMut(&Deployed) -> Fut,
    Fut: Future<Output = Result<(T, Units), ProviderError>>,
{
    let mut attempts = Attempts::new(st, actor, model, prompt_units, max_units);
    loop {
        let a = attempts.next().await?;
        match f(a.deployed).await {
            Ok((out, used)) => {
                let cost = settle(st, &actor, a.reservation, used.prompt, used.completion, CallStatus::Success).await;
                return Ok((out, a.info(cost)));
            }
            Err(e) => {
                if !attempts.failed(&a, e).await {
                    return Err(attempts.give_up());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Chat completions

/// A chat completion's answer: whole, or a stream of chunks that settles
/// its reservation when it ends, fails or is dropped.
pub enum ChatOutcome {
    Complete(ChatResponse),
    Stream(SettlingStream),
}

/// About four characters per token.
pub fn estimate_text(s: &str) -> u64 {
    (s.chars().count() as u64).div_ceil(4)
}

/// Run a chat completion: reservation sizing, admission, the provider call
/// (streaming if `req.stream`), retries, fallbacks and settlement.
pub async fn run_chat(st: &AppState, actor: Principal, mut req: ChatRequest) -> Result<(ChatOutcome, CallInfo), Failure> {
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
    let mut attempts = Attempts::new(st, actor, &model, prompt_tokens, max_tokens);
    loop {
        let a = attempts.next().await?;
        let dep = &a.deployed.deployment;
        if req.stream == Some(true) {
            match st.client.chat_stream(dep, &req).await {
                Ok(s) => {
                    let guard = StreamSettle {
                        st: st.clone(),
                        actor,
                        reservation: a.reservation,
                        prompt_estimate: prompt_tokens,
                        usage: None,
                        chars: 0,
                        status: CallStatus::Success,
                        settled: false,
                    };
                    return Ok((ChatOutcome::Stream(SettlingStream { inner: s, guard }), a.info(None)));
                }
                Err(e) => {
                    if !attempts.failed(&a, e).await {
                        return Err(attempts.give_up());
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
                    let cost = settle(st, &actor, a.reservation, p, c, CallStatus::Success).await;
                    return Ok((ChatOutcome::Complete(resp), a.info(cost)));
                }
                Err(e) => {
                    if !attempts.failed(&a, e).await {
                        return Err(attempts.give_up());
                    }
                }
            }
        }
    }
}

/// Settles a streamed call when the stream ends, fails, or is dropped.
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

/// A provider's chunk stream that settles the reservation exactly once: when
/// it ends, when it fails (counting a retryable failure against the
/// deployment), or when it is dropped (the client went away). Always ends
/// with the upstream's usage-only chunk when the upstream reported usage.
pub struct SettlingStream {
    inner: gateway_providers::ChatStream,
    guard: StreamSettle,
}

impl Stream for SettlingStream {
    type Item = Result<ChatChunk, ProviderError>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        match this.inner.poll_next_unpin(cx) {
            Poll::Ready(Some(Ok(chunk))) => {
                this.guard.observe(&chunk);
                Poll::Ready(Some(Ok(chunk)))
            }
            Poll::Ready(Some(Err(e))) => {
                this.guard.status = if e.is_retryable() { CallStatus::Retryable } else { CallStatus::Failure };
                this.guard.finish();
                Poll::Ready(Some(Err(e)))
            }
            Poll::Ready(None) => {
                this.guard.finish();
                Poll::Ready(None)
            }
            Poll::Pending => Poll::Pending,
        }
    }
}

/// `data: <json>\n\n`
pub fn sse(v: &impl serde::Serialize) -> Bytes {
    let mut b = b"data: ".to_vec();
    b.extend(serde_json::to_vec(v).unwrap_or_default());
    b.extend_from_slice(b"\n\n");
    Bytes::from(b)
}

/// An SSE response with the call's headers.
pub fn sse_response(info: &CallInfo, body: impl Stream<Item = Bytes> + Send + 'static) -> Response {
    let mut h = info.headers();
    h.insert(header::CONTENT_TYPE, HeaderValue::from_static("text/event-stream"));
    h.insert(header::CACHE_CONTROL, HeaderValue::from_static("no-cache"));
    (h, Body::from_stream(body.map(Ok::<_, std::convert::Infallible>))).into_response()
}

pub fn parse<T: serde::de::DeserializeOwned>(body: Value) -> Result<T, Failure> {
    serde_json::from_value(body).map_err(|e| ApiError::bad_request(format!("invalid request body: {e}")).into())
}

pub async fn chat_completions(State(st): State<AppState>, actor: Actor<Gateway>, Json(body): Json<Value>) -> Response {
    let req = match parse::<ChatRequest>(body) {
        Ok(r) => r,
        Err(f) => return f.into_response(),
    };
    let wants_usage = req.wants_stream_usage();
    match run_chat(&st, *actor.principal(), req).await {
        Ok((ChatOutcome::Complete(resp), info)) => (info.headers(), Json(resp)).into_response(),
        Ok((ChatOutcome::Stream(s), info)) => {
            let body = s
                .filter_map(move |item| async move {
                    match item {
                        // Usage is always requested upstream for billing; pass it on only if asked.
                        Ok(c) if c.choices.is_empty() && c.usage.is_some() && !wants_usage => None,
                        Ok(c) => Some(sse(&c)),
                        Err(e) => Some(sse(&e.to_openai_body())),
                    }
                })
                .chain(futures::stream::once(async { Bytes::from_static(b"data: [DONE]\n\n") }));
            sse_response(&info, body)
        }
        Err(f) => f.into_response(),
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

// ---------------------------------------------------------------------------
// Embeddings

pub async fn embeddings(State(st): State<AppState>, actor: Actor<Gateway>, Json(body): Json<Value>) -> Response {
    let req = match parse::<EmbeddingRequest>(body) {
        Ok(r) => r,
        Err(f) => return f.into_response(),
    };
    let prompt_tokens = match &req.input {
        EmbeddingInput::Text(s) => estimate_text(s),
        EmbeddingInput::Texts(v) => v.iter().map(|s| estimate_text(s)).sum(),
        EmbeddingInput::Tokens(t) => t.len() as u64,
        EmbeddingInput::TokenBatches(b) => b.iter().map(|t| t.len() as u64).sum(),
    };
    let client = st.client.clone();
    let result = call(&st, *actor.principal(), &req.model, prompt_tokens, 0, |d| {
        let (client, dep, req) = (client.clone(), d.deployment.clone(), req.clone());
        async move {
            let resp = client.embeddings(&dep, &req).await?;
            let used = Units { prompt: resp.usage.prompt_tokens, completion: 0 };
            Ok((resp, used))
        }
    })
    .await;
    match result {
        Ok((resp, info)) => (info.headers(), Json(resp)).into_response(),
        Err(f) => f.into_response(),
    }
}
