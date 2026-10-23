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
//! `run_chat` (and so every API translated to it) and the embeddings route
//! also run the guardrails (`guardrails.rs`) and the response cache
//! (`cache.rs`): `pre_call` guardrails before admission, `during_call` ones
//! concurrently with the provider call, `post_call` ones on the response; a
//! cache hit is admitted and settled at zero tokens without a provider call
//! ([`admit_cached`]).
//!
//! The reservation covers the estimated prompt plus `max_tokens`. When the
//! client sets no `max_tokens`, the gateway sets one (the model's output
//! limit, capped by `default_max_tokens`), so a provider that honours it
//! never returns more completion tokens than were reserved; the budget
//! theorem (`proofs/Theorems.lean`) assumes settlements stay within their
//! reservations.

// Failures are finished axum `Response`s, returned as they are.
#![allow(clippy::result_large_err)]

use crate::cache::{Cache, Controls};
use crate::error::ApiError;
use crate::guardrails::{self, APPLIED_HEADER, GuardRun, GuardrailError, Mode, Segment};
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
use gateway_providers::{ChatChunk, ChatRequest, ChatResponse, EmbeddingRequest, EmbeddingResponse, ProviderError, estimate_prompt_tokens};
use h5i_app_http::Actor;
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll};
use std::time::Duration;

/// Why a call produced no answer: the kernel refused, the provider failed,
/// a guardrail blocked it, or something else went wrong (bad request,
/// database unavailable).
#[derive(Debug)]
pub enum Failure {
    Refusal(Refusal),
    Provider(ProviderError),
    Api(ApiError),
    /// A guardrail blocked the request or response (400,
    /// `guardrail_violation`), or could not run (500, `guardrail_error`).
    Guardrail(GuardrailError),
}

impl Failure {
    /// The HTTP status a client should see.
    pub fn status(&self) -> StatusCode {
        match self {
            Failure::Refusal(e) => ApiError::refusal(*e).status,
            Failure::Provider(e) => StatusCode::from_u16(e.status_code()).unwrap_or(StatusCode::BAD_GATEWAY),
            Failure::Api(e) => e.status,
            Failure::Guardrail(e) => e.status,
        }
    }

    /// A short machine-readable kind (`rate_limit_error`, `budget_exceeded`, …).
    pub fn kind(&self) -> String {
        match self {
            Failure::Refusal(e) => ApiError::refusal(*e).kind.to_string(),
            Failure::Provider(e) => e.to_openai_body().error.kind.clone().unwrap_or_else(|| "provider_error".into()),
            Failure::Api(e) => e.kind.to_string(),
            Failure::Guardrail(e) => e.kind.to_string(),
        }
    }

    pub fn message(&self) -> String {
        match self {
            Failure::Refusal(e) => ApiError::refusal(*e).message,
            Failure::Provider(e) => e.message().to_string(),
            Failure::Api(e) => e.message.clone(),
            Failure::Guardrail(e) => format!("{} (guardrail: {})", e.message, e.guardrail),
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
            Failure::Guardrail(e) => e.into_response(),
        }
    }
}

impl From<GuardrailError> for Failure {
    fn from(e: GuardrailError) -> Self {
        Failure::Guardrail(e)
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
    /// The guardrails the call ran (`x-litellm-applied-guardrails`).
    pub guardrails: Vec<String>,
    /// The response cache key (`x-litellm-cache-key`), when the call is cacheable.
    pub cache_key: Option<String>,
    /// Served from the cache (`x-litellm-cache-hit`).
    pub cache_hit: bool,
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
        if !self.guardrails.is_empty() {
            put(APPLIED_HEADER, self.guardrails.join(","));
        }
        if let Some(k) = &self.cache_key {
            put("x-litellm-cache-key", k.clone());
            put("x-litellm-cache-hit", self.cache_hit.to_string());
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
            guardrails: Vec::new(),
            cache_key: None,
            cache_hit: false,
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

/// Admit a call answered from the cache, and settle it at zero tokens at
/// once: the kernel still checks the key (blocked, expired, model access,
/// team), its RPM window, parallel limit and budget (reserving nothing), and
/// records a zero-cost spend log; nothing is charged and no tokens count
/// against TPM. Rate limits and access therefore apply to hits exactly as to
/// provider calls.
pub async fn admit_cached(st: &AppState, actor: Principal, model: &str) -> Result<CallInfo, Failure> {
    let mut attempts = Attempts::new(st, actor, model, 0, 0);
    let a = attempts.next().await?;
    let cost = settle(st, &actor, a.reservation, 0, 0, CallStatus::Success).await;
    Ok(a.info(cost))
}

/// The model group a client's model name maps to.
fn group_of(st: &AppState, model: &str) -> String {
    st.settings.aliases.get(model).cloned().unwrap_or_else(|| model.to_string())
}

/// The cache, a response is stored in at the end of a stream.
type Store = (Arc<Cache>, String, Controls);

/// Run a chat completion: guardrails, reservation sizing, the cache,
/// admission, the provider call (streaming if `req.stream`), retries,
/// fallbacks and settlement.
///
/// Order: `pre_call` guardrails (a block returns before admission, so it
/// costs nothing); then, concurrently, the `during_call` guardrails and
/// either a cache hit (admitted and settled at zero) or the provider call;
/// then the response is stored in the cache (as the provider returned it),
/// checked by the `post_call` guardrails, and Presidio's tokens are put back.
/// A `during_call` or `post_call` block comes after the provider call, which
/// is settled (charged) as usual.
pub async fn run_chat(st: &AppState, actor: Principal, mut req: ChatRequest) -> Result<(ChatOutcome, CallInfo), Failure> {
    let model = req.model.clone();
    let group = group_of(st, &model);
    let stream = req.stream == Some(true);

    let mut guard = if st.guardrails.is_empty() { st.guardrails.idle() } else { st.guardrails.start(&req.extra, &group, actor.key)? };
    let mut request_segs = Vec::new();
    if !guard.is_empty() {
        request_segs = guardrails::request_segments(&req);
        if guard.has(Mode::PreCall) {
            guard.pre_call(&mut request_segs).await?;
            guardrails::set_request_segments(&mut req, &request_segs);
        }
    }

    let prompt_tokens = estimate_prompt_tokens(&req);
    let max_tokens = match req.max_output_tokens() {
        Some(n) => n,
        None => {
            let limit = st.settings.default_max_tokens;
            let n = st.registry.max_output_tokens(&group).map_or(limit, |m| m.min(limit));
            req.max_completion_tokens = Some(n);
            n
        }
    };

    let controls = Controls::from_extra(&req.extra);
    let cache = st.cache.as_ref();
    let cache_key = cache.and_then(|c| c.chat_key(&group, &req, &controls));

    let main = async {
        if let (Some(c), Some(k)) = (cache, &cache_key)
            && let Some(v) = c.get(k, &controls).await
        {
            match serde_json::from_value::<ChatResponse>(v) {
                Ok(resp) => {
                    let info = admit_cached(st, actor, &model).await?;
                    return Ok((ChatOutcome::Complete(resp), info, true));
                }
                Err(e) => tracing::warn!(error = %e, "unreadable cache entry; ignored"),
            }
        }
        let (outcome, info) = call_chat(st, actor, &req, prompt_tokens, max_tokens).await?;
        Ok::<_, Failure>((outcome, info, false))
    };
    let during = async {
        if guard.has(Mode::DuringCall) { guard.during_call(&request_segs).await } else { Ok(()) }
    };
    let (result, during) = futures::join!(main, during);
    // A blocked call's stream, if any, is dropped here and settles.
    during?;
    guard.note_during();
    let (outcome, mut info, hit) = result?;
    info.cache_key = cache_key.clone();
    info.cache_hit = hit;

    match outcome {
        ChatOutcome::Complete(mut resp) => {
            if !hit && let (Some(c), Some(k)) = (cache, &cache_key) {
                match serde_json::to_value(&resp) {
                    Ok(v) => c.put(k, &v, &controls).await,
                    Err(e) => tracing::warn!(error = %e, "response not cached"),
                }
            }
            if guard.has(Mode::PostCall) {
                let mut out = guardrails::response_segments(&resp);
                guard.post_call(&request_segs, &mut out).await?;
                guardrails::set_response_segments(&mut resp, &out);
            }
            guard.unmask_response(&mut resp);
            info.guardrails = guard.applied.clone();
            if stream {
                // A cached answer to a streaming request: replayed as chunks.
                let chunks: Vec<Result<ChatChunk, ProviderError>> = replay_chunks(&resp).into_iter().map(Ok).collect();
                return Ok((ChatOutcome::Stream(SettlingStream::settled(Box::pin(futures::stream::iter(chunks)))), info));
            }
            Ok((ChatOutcome::Complete(resp), info))
        }
        ChatOutcome::Stream(s) => {
            for n in guard.names(Mode::PostCall) {
                if !guard.applied.contains(&n) {
                    guard.applied.push(n);
                }
            }
            info.guardrails = guard.applied.clone();
            let store: Option<Store> = match (cache, cache_key) {
                (Some(c), Some(k)) if c.writes(&controls) => Some((c.clone(), k, controls)),
                _ => None,
            };
            if !guard.has(Mode::PostCall) && !guard.unmasks() && store.is_none() {
                return Ok((ChatOutcome::Stream(s), info));
            }
            Ok((ChatOutcome::Stream(stream_tail(s, guard, request_segs, store)), info))
        }
    }
}

/// The provider call with retries and fallbacks.
async fn call_chat(st: &AppState, actor: Principal, req: &ChatRequest, prompt_tokens: u64, max_tokens: u64) -> Result<(ChatOutcome, CallInfo), Failure> {
    let mut attempts = Attempts::new(st, actor, &req.model, prompt_tokens, max_tokens);
    loop {
        let a = attempts.next().await?;
        let dep = &a.deployed.deployment;
        if req.stream == Some(true) {
            match st.client.chat_stream(dep, req).await {
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
                    return Ok((ChatOutcome::Stream(SettlingStream { inner: s, guard: Some(guard) }), a.info(None)));
                }
                Err(e) => {
                    if !attempts.failed(&a, e).await {
                        return Err(attempts.give_up());
                    }
                }
            }
        } else {
            match st.client.chat(dep, req).await {
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

/// A whole response as the chunks a stream of it would have carried: per
/// choice, the role, content, reasoning and tool calls, then the finish
/// reason; then usage.
pub fn replay_chunks(resp: &ChatResponse) -> Vec<ChatChunk> {
    let mut out = Vec::new();
    let chunk = |choices: Value, usage: Value| {
        serde_json::from_value::<ChatChunk>(json!({
            "id": resp.id, "object": "chat.completion.chunk", "created": resp.created, "model": resp.model,
            "system_fingerprint": resp.system_fingerprint, "choices": choices, "usage": usage,
        }))
        .ok()
    };
    for c in &resp.choices {
        let m = &c.message;
        let mut delta = json!({"role": "assistant"});
        if let Some(content) = &m.content {
            delta["content"] = Value::String(content.text().into_owned());
        }
        if let Some(r) = &m.reasoning_content {
            delta["reasoning_content"] = Value::String(r.clone());
        }
        if let Some(r) = &m.refusal {
            delta["refusal"] = Value::String(r.clone());
        }
        if let Some(calls) = &m.tool_calls {
            let calls: Vec<Value> = calls
                .iter()
                .enumerate()
                .map(|(i, t)| json!({"index": i, "id": t.id, "type": t.kind, "function": {"name": t.function.name, "arguments": t.function.arguments}}))
                .collect();
            delta["tool_calls"] = Value::Array(calls);
        }
        out.extend(chunk(json!([{"index": c.index, "delta": delta}]), Value::Null));
        out.extend(chunk(json!([{"index": c.index, "delta": {}, "finish_reason": c.finish_reason}]), Value::Null));
    }
    if let Some(u) = &resp.usage {
        out.extend(chunk(json!([]), serde_json::to_value(u).unwrap_or(Value::Null)));
    }
    out
}

/// Builds the whole response from a stream's chunks, for the cache and the
/// `post_call` guardrails.
#[derive(Default)]
struct Assembler {
    first: Option<ChatChunk>,
    choices: BTreeMap<u32, Assembled>,
    usage: Option<Value>,
}

/// One choice so far; tool calls by index: (id, type, name, arguments).
#[derive(Default)]
struct Assembled {
    content: Option<String>,
    reasoning: Option<String>,
    refusal: Option<String>,
    tool_calls: BTreeMap<u32, (Option<String>, Option<String>, String, String)>,
    finish_reason: Option<String>,
}

impl Assembler {
    fn observe(&mut self, chunk: &ChatChunk) {
        if self.first.is_none() && !chunk.choices.is_empty() {
            self.first = Some(chunk.clone());
        }
        if let Some(u) = &chunk.usage {
            self.usage = serde_json::to_value(u).ok();
        }
        for c in &chunk.choices {
            let a = self.choices.entry(c.index).or_default();
            let d = &c.delta;
            if let Some(t) = &d.content {
                a.content.get_or_insert_default().push_str(t);
            }
            if let Some(t) = &d.reasoning_content {
                a.reasoning.get_or_insert_default().push_str(t);
            }
            if let Some(t) = &d.refusal {
                a.refusal.get_or_insert_default().push_str(t);
            }
            for t in d.tool_calls.iter().flatten() {
                let e = a.tool_calls.entry(t.index).or_default();
                if t.id.is_some() {
                    e.0 = t.id.clone();
                }
                if t.kind.is_some() {
                    e.1 = t.kind.clone();
                }
                if let Some(f) = &t.function {
                    if let Some(n) = &f.name {
                        e.2.push_str(n);
                    }
                    if let Some(x) = &f.arguments {
                        e.3.push_str(x);
                    }
                }
            }
            if c.finish_reason.is_some() {
                a.finish_reason = c.finish_reason.clone();
            }
        }
    }

    fn texts(&self) -> Vec<Segment> {
        self.choices.values().filter_map(|a| a.content.clone()).map(|text| Segment { role: "assistant".into(), text }).collect()
    }

    fn response(&self) -> Option<ChatResponse> {
        let first = self.first.as_ref()?;
        let choices: Vec<Value> = self
            .choices
            .iter()
            .map(|(i, a)| {
                let mut m = json!({"role": "assistant", "content": a.content});
                if let Some(r) = &a.reasoning {
                    m["reasoning_content"] = Value::String(r.clone());
                }
                if let Some(r) = &a.refusal {
                    m["refusal"] = Value::String(r.clone());
                }
                if !a.tool_calls.is_empty() {
                    let calls: Vec<Value> = a
                        .tool_calls
                        .values()
                        .map(|(id, kind, name, args)| json!({"id": id, "type": kind.clone().unwrap_or_else(|| "function".into()), "function": {"name": name, "arguments": args}}))
                        .collect();
                    m["tool_calls"] = Value::Array(calls);
                }
                json!({"index": i, "message": m, "finish_reason": a.finish_reason})
            })
            .collect();
        serde_json::from_value(json!({
            "id": first.id, "object": "chat.completion", "created": first.created, "model": first.model,
            "system_fingerprint": first.system_fingerprint, "choices": choices, "usage": self.usage,
        }))
        .map_err(|e| tracing::warn!(error = %e, "could not assemble the streamed response"))
        .ok()
    }
}

/// The end of a stream: the cache entry and the `post_call` guardrails,
/// which see the accumulated text. Presidio's tokens are put back chunk by
/// chunk as they stream.
struct Tail {
    inner: SettlingStream,
    guard: GuardRun,
    request: Vec<Segment>,
    store: Option<Store>,
    acc: Assembler,
    /// Text held back per choice while a token may be incomplete.
    pending: HashMap<u32, String>,
    queue: VecDeque<Result<ChatChunk, ProviderError>>,
    done: bool,
}

fn stream_tail(inner: SettlingStream, guard: GuardRun, request: Vec<Segment>, store: Option<Store>) -> SettlingStream {
    let tail = Tail { inner, guard, request, store, acc: Assembler::default(), pending: HashMap::new(), queue: VecDeque::new(), done: false };
    let s = futures::stream::unfold(tail, |mut t| async move {
        loop {
            if let Some(item) = t.queue.pop_front() {
                return Some((item, t));
            }
            if t.done {
                return None;
            }
            match t.inner.next().await {
                Some(Ok(mut chunk)) => {
                    t.acc.observe(&chunk);
                    if t.guard.unmasks() {
                        t.unmask_chunk(&mut chunk);
                    }
                    return Some((Ok(chunk), t));
                }
                // The upstream failed: nothing is cached or checked.
                Some(Err(e)) => {
                    t.done = true;
                    return Some((Err(e), t));
                }
                None => {
                    t.done = true;
                    t.finish().await;
                }
            }
        }
    });
    SettlingStream::settled(Box::pin(s))
}

impl Tail {
    fn unmask_chunk(&mut self, chunk: &mut ChatChunk) {
        for c in &mut chunk.choices {
            let pending = self.pending.entry(c.index).or_default();
            let mut text = match c.delta.content.take() {
                Some(d) => self.guard.unmask_delta(pending, &d),
                None => String::new(),
            };
            if c.finish_reason.is_some() {
                text.push_str(&self.guard.unmask(&std::mem::take(pending)));
            }
            if !text.is_empty() {
                c.delta.content = Some(text);
            }
        }
    }

    /// The upstream ended cleanly.
    async fn finish(&mut self) {
        // Text still held back (a stream without a finish reason).
        let rest: Vec<(u32, String)> = self.pending.drain().filter(|(_, p)| !p.is_empty()).collect();
        if let Some(first) = &self.acc.first {
            for (i, p) in rest {
                let mut c = ChatChunk::new(first.id.clone(), first.model.clone(), first.created).with_delta(Default::default(), None);
                c.choices[0].index = i;
                c.choices[0].delta.content = Some(self.guard.unmask(&p));
                self.queue.push_back(Ok(c));
            }
        }
        if let Some((cache, key, controls)) = &self.store
            && let Some(resp) = self.acc.response()
            && let Ok(v) = serde_json::to_value(&resp)
        {
            cache.put(key, &v, controls).await;
        }
        if self.guard.has(Mode::PostCall) {
            let mut out = self.acc.texts();
            if let Err(e) = self.guard.post_call(&self.request, &mut out).await {
                tracing::warn!(guardrail = %e.guardrail, "post_call guardrail blocked a streamed response");
                let body = e.body().to_string();
                self.queue.push_back(Err(ProviderError::from_upstream("guardrail", e.status.as_u16(), &body, None)));
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
    /// `None` when the call is already settled (a cache hit, or a stream
    /// wrapping another `SettlingStream`).
    guard: Option<StreamSettle>,
}

impl SettlingStream {
    /// A stream whose call is already settled.
    pub fn settled(inner: gateway_providers::ChatStream) -> Self {
        SettlingStream { inner, guard: None }
    }
}

impl Stream for SettlingStream {
    type Item = Result<ChatChunk, ProviderError>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        match this.inner.poll_next_unpin(cx) {
            Poll::Ready(Some(Ok(chunk))) => {
                if let Some(g) = &mut this.guard {
                    g.observe(&chunk);
                }
                Poll::Ready(Some(Ok(chunk)))
            }
            Poll::Ready(Some(Err(e))) => {
                if let Some(g) = &mut this.guard {
                    g.status = if e.is_retryable() { CallStatus::Retryable } else { CallStatus::Failure };
                    g.finish();
                }
                Poll::Ready(Some(Err(e)))
            }
            Poll::Ready(None) => {
                if let Some(g) = &mut this.guard {
                    g.finish();
                }
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

/// Embeddings: `pre_call` guardrails on the text inputs (block or rewrite;
/// `during_call` and `post_call` do not apply), then the cache, then the call.
pub async fn embeddings(State(st): State<AppState>, actor: Actor<Gateway>, Json(body): Json<Value>) -> Response {
    let req = match parse::<EmbeddingRequest>(body) {
        Ok(r) => r,
        Err(f) => return f.into_response(),
    };
    match run_embeddings(&st, *actor.principal(), req).await {
        Ok((resp, info)) => (info.headers(), Json(resp)).into_response(),
        Err(f) => f.into_response(),
    }
}

/// An embeddings call with guardrails, the cache, admission and settlement.
pub async fn run_embeddings(st: &AppState, actor: Principal, mut req: EmbeddingRequest) -> Result<(EmbeddingResponse, CallInfo), Failure> {
    let group = group_of(st, &req.model);
    let mut applied = Vec::new();
    if !st.guardrails.is_empty() {
        let mut guard = st.guardrails.start(&req.extra, &group, actor.key)?;
        if guard.has(Mode::PreCall) {
            let mut segs = guardrails::embedding_segments(&req.input);
            guard.pre_call(&mut segs).await?;
            guardrails::set_embedding_segments(&mut req.input, &segs);
        }
        applied = guard.applied;
    }
    let controls = Controls::from_extra(&req.extra);
    let cache = st.cache.as_ref();
    let cache_key = cache.and_then(|c| c.embedding_key(&group, &req, &controls));
    if let (Some(c), Some(k)) = (cache, &cache_key)
        && let Some(v) = c.get(k, &controls).await
    {
        match serde_json::from_value::<EmbeddingResponse>(v) {
            Ok(resp) => {
                let mut info = admit_cached(st, actor, &req.model).await?;
                info.guardrails = applied;
                info.cache_key = cache_key;
                info.cache_hit = true;
                return Ok((resp, info));
            }
            Err(e) => tracing::warn!(error = %e, "unreadable cache entry; ignored"),
        }
    }
    let prompt_tokens = match &req.input {
        EmbeddingInput::Text(s) => estimate_text(s),
        EmbeddingInput::Texts(v) => v.iter().map(|s| estimate_text(s)).sum(),
        EmbeddingInput::Tokens(t) => t.len() as u64,
        EmbeddingInput::TokenBatches(b) => b.iter().map(|t| t.len() as u64).sum(),
    };
    let client = st.client.clone();
    let (resp, mut info) = call(st, actor, &req.model, prompt_tokens, 0, |d| {
        let (client, dep, req) = (client.clone(), d.deployment.clone(), req.clone());
        async move {
            let resp = client.embeddings(&dep, &req).await?;
            let used = Units { prompt: resp.usage.prompt_tokens, completion: 0 };
            Ok((resp, used))
        }
    })
    .await?;
    if let (Some(c), Some(k)) = (cache, &cache_key)
        && let Ok(v) = serde_json::to_value(&resp)
    {
        c.put(k, &v, &controls).await;
    }
    info.guardrails = applied;
    info.cache_key = cache_key;
    Ok((resp, info))
}
