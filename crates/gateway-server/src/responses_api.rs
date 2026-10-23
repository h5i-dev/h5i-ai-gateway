//! OpenAI's Responses API (`/v1/responses`), bridged to chat completions.
//!
//! A request becomes an OpenAI chat request
//! ([`gateway_providers::formats::responses`]) and goes through
//! [`run_chat`] like any chat completion, so every provider works and
//! keys, budgets and rate limits apply as usual; the answer comes back as a
//! Response object, or as the Responses streaming events.
//!
//! **Stored responses live in memory**, in this process only: they are lost
//! on restart and not shared between gateway replicas. The store keeps the
//! most recently used [`store_capacity`] responses (LRU by count;
//! `H5I_RESPONSES_STORE_SIZE`, default 1000). Each response is scoped to the
//! credential that created it (tenant, key id, master or not): another key
//! can neither read, delete nor continue it (`previous_response_id`). A
//! request with `store: false` is not kept.

use crate::AppState;
use crate::kernel::Gateway;
use crate::proxy::{ChatOutcome, parse, run_chat, sse_response};
use axum::Json;
use axum::Router;
use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use bytes::Bytes;
use futures::StreamExt;
use gateway_kernel::Principal;
use gateway_providers::formats::adapt_to_target;
use gateway_providers::formats::responses::{self as rs, ResponseId, ResponsesRequest, Translated};
use gateway_providers::{ChatMessage, estimate_prompt_tokens};
use h5i_app_http::Actor;
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap};
use std::sync::{Mutex, OnceLock};

/// The routes of this module.
pub fn routes() -> Router<AppState> {
    Router::new()
        .route("/v1/responses", post(create))
        .route("/responses", post(create))
        .route("/v1/responses/{id}", get(retrieve).delete(delete))
        .route("/responses/{id}", get(retrieve).delete(delete))
}

// ---------------------------------------------------------------------------
// The store

/// Who may see a stored response: the credential that created it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Owner {
    pub org: u64,
    pub key: u64,
    pub master: bool,
}

impl Owner {
    pub fn of(p: &Principal) -> Owner {
        Owner { org: p.org, key: p.key, master: p.master }
    }
}

/// A stored response and the conversation it ends (for `previous_response_id`).
#[derive(Debug, Clone)]
pub struct Stored {
    pub owner: Owner,
    pub response: Value,
    pub conversation: Vec<ChatMessage>,
}

#[derive(Debug, Default)]
struct Lru {
    entries: HashMap<String, (u64, Stored)>,
    /// Last use -> id.
    order: BTreeMap<u64, String>,
    clock: u64,
}

/// An in-memory LRU of stored responses, bounded by count.
#[derive(Debug)]
pub struct ResponseStore {
    capacity: usize,
    inner: Mutex<Lru>,
}

impl ResponseStore {
    pub fn new(capacity: usize) -> Self {
        ResponseStore { capacity: capacity.max(1), inner: Mutex::default() }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Lru> {
        self.inner.lock().unwrap_or_else(|e| e.into_inner())
    }

    pub fn put(&self, id: String, stored: Stored) {
        let mut l = self.lock();
        l.clock += 1;
        let tick = l.clock;
        if let Some((old, _)) = l.entries.insert(id.clone(), (tick, stored)) {
            l.order.remove(&old);
        }
        l.order.insert(tick, id);
        while l.entries.len() > self.capacity {
            let Some((_, oldest)) = l.order.pop_first() else {
                break;
            };
            l.entries.remove(&oldest);
        }
    }

    /// The response `id` if `owner` stored it; marks it as used.
    pub fn get(&self, owner: Owner, id: &str) -> Option<Stored> {
        let mut l = self.lock();
        l.clock += 1;
        let tick = l.clock;
        let Lru { entries, order, .. } = &mut *l;
        let (used, stored) = entries.get_mut(id).filter(|(_, s)| s.owner == owner)?;
        order.remove(used);
        order.insert(tick, id.to_string());
        *used = tick;
        Some(stored.clone())
    }

    /// Delete the response `id` if `owner` stored it.
    pub fn remove(&self, owner: Owner, id: &str) -> bool {
        let mut l = self.lock();
        match l.entries.get(id) {
            Some((tick, s)) if s.owner == owner => {
                let tick = *tick;
                l.order.remove(&tick);
                l.entries.remove(id);
                true
            }
            _ => false,
        }
    }

    pub fn len(&self) -> usize {
        self.lock().entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// How many responses the store keeps: `H5I_RESPONSES_STORE_SIZE`, else 1000.
pub fn store_capacity() -> usize {
    std::env::var("H5I_RESPONSES_STORE_SIZE").ok().and_then(|v| v.parse().ok()).unwrap_or(1000)
}

/// The process's response store.
pub fn store() -> &'static ResponseStore {
    static STORE: OnceLock<ResponseStore> = OnceLock::new();
    STORE.get_or_init(|| ResponseStore::new(store_capacity()))
}

// ---------------------------------------------------------------------------
// Handlers

fn error(status: StatusCode, message: &str, param: Option<&str>, code: Option<&str>) -> Response {
    let kind = if status == StatusCode::NOT_FOUND { "not_found_error" } else { "invalid_request_error" };
    (status, Json(json!({"error": {"message": message, "type": kind, "param": param, "code": code}}))).into_response()
}

fn not_found(id: &str) -> Response {
    error(StatusCode::NOT_FOUND, &format!("Response with id '{id}' not found."), None, None)
}

/// `POST /v1/responses`.
pub async fn create(State(st): State<AppState>, actor: Actor<Gateway>, Json(body): Json<Value>) -> Response {
    let req: ResponsesRequest = match parse(body) {
        Ok(r) => r,
        Err(f) => return f.into_response(),
    };
    let principal = *actor.principal();
    let owner = Owner::of(&principal);
    let history = match &req.previous_response_id {
        None => Vec::new(),
        Some(prev) => match store().get(owner, prev) {
            Some(s) => s.conversation,
            None => {
                return error(
                    StatusCode::BAD_REQUEST,
                    &format!("Previous response with id '{prev}' not found."),
                    Some("previous_response_id"),
                    Some("previous_response_not_found"),
                );
            }
        },
    };
    let Translated { mut chat, conversation } = match rs::to_chat_request(&req, &history) {
        Ok(t) => t,
        Err(e) => {
            return error(StatusCode::BAD_REQUEST, &e.message, e.param.as_deref(), None);
        }
    };
    adapt_to_target(&mut chat, crate::anthropic_api::target(&st, &req.model));
    let estimate = estimate_prompt_tokens(&chat);
    let rid = ResponseId { id: rs::new_response_id(), created_at: crate::auth::unix_now() };
    match run_chat(&st, principal, chat).await {
        Ok((ChatOutcome::Complete(resp), info)) => {
            let obj = rs::from_chat_response(&req, &rid, &resp);
            if req.stores() {
                let thinking = resp.choices.first().and_then(|c| c.message.extra.get("thinking_blocks"));
                let mut conversation = conversation;
                conversation.extend(rs::output_messages(&obj, thinking));
                store().put(rid.id.clone(), Stored { owner, response: obj.clone(), conversation });
            }
            (info.headers(), Json(obj)).into_response()
        }
        Ok((ChatOutcome::Stream(s), info)) => {
            let stores = req.stores();
            let encoder = rs::ResponsesStream::new(req, rid, estimate);
            let state = (s, encoder, Some(conversation), false);
            let body = futures::stream::unfold(state, move |(mut s, mut enc, mut conversation, done)| async move {
                if done {
                    return None;
                }
                let (events, done) = match s.next().await {
                    Some(Ok(chunk)) => (enc.on_chunk(&chunk), false),
                    Some(Err(e)) => {
                        let code = e.to_openai_body().error.kind.unwrap_or_else(|| "server_error".into());
                        (enc.error(&code, e.message()), true)
                    }
                    None => {
                        let events = enc.finish();
                        if let (true, Some(r), Some(mut conv)) = (stores, enc.final_response(), conversation.take()) {
                            conv.extend(rs::output_messages(r, None));
                            let id = r["id"].as_str().unwrap_or_default().to_string();
                            store().put(id, Stored { owner, response: r.clone(), conversation: conv });
                        }
                        (events, true)
                    }
                };
                Some((Bytes::from(rs::encode_events(&events)), (s, enc, conversation, done)))
            })
            .filter(|b| futures::future::ready(!b.is_empty()));
            sse_response(&info, body)
        }
        Err(f) => f.into_response(),
    }
}

/// `GET /v1/responses/{id}`.
pub async fn retrieve(actor: Actor<Gateway>, Path(id): Path<String>) -> Response {
    match store().get(Owner::of(actor.principal()), &id) {
        Some(s) => Json(s.response).into_response(),
        None => not_found(&id),
    }
}

/// `DELETE /v1/responses/{id}`.
pub async fn delete(actor: Actor<Gateway>, Path(id): Path<String>) -> Response {
    if store().remove(Owner::of(actor.principal()), &id) {
        Json(json!({"id": id, "object": "response", "deleted": true})).into_response()
    } else {
        not_found(&id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stored(owner: Owner, n: u64) -> Stored {
        Stored { owner, response: json!({"n": n}), conversation: Vec::new() }
    }

    const A: Owner = Owner { org: 1, key: 1, master: false };
    const B: Owner = Owner { org: 1, key: 2, master: false };

    #[test]
    fn scoped_by_owner() {
        let s = ResponseStore::new(10);
        s.put("r1".into(), stored(A, 1));
        assert!(s.get(A, "r1").is_some());
        assert!(s.get(B, "r1").is_none());
        assert!(s.get(Owner { org: 2, ..A }, "r1").is_none());
        assert!(s.get(Owner { master: true, ..A }, "r1").is_none());
        assert!(!s.remove(B, "r1"));
        assert!(s.remove(A, "r1"));
        assert!(s.get(A, "r1").is_none());
        assert!(s.is_empty());
    }

    #[test]
    fn evicts_the_least_recently_used() {
        let s = ResponseStore::new(2);
        s.put("r1".into(), stored(A, 1));
        s.put("r2".into(), stored(A, 2));
        // Using r1 makes r2 the oldest.
        assert!(s.get(A, "r1").is_some());
        s.put("r3".into(), stored(A, 3));
        assert_eq!(s.len(), 2);
        assert!(s.get(A, "r2").is_none());
        assert!(s.get(A, "r1").is_some());
        assert!(s.get(A, "r3").is_some());
        // Replacing an entry does not grow the store.
        s.put("r3".into(), stored(A, 4));
        assert_eq!(s.len(), 2);
        assert_eq!(s.get(A, "r3").unwrap().response["n"], 4);
    }
}
