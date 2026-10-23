//! A scripted local upstream for end-to-end tests: an axum server on
//! 127.0.0.1:0 that records every request and answers with canned responses
//! in order.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use axum::Router;
use axum::body::{Body, Bytes};
use axum::extract::{Request, State};
use axum::http::{HeaderMap, StatusCode};
use axum::response::Response;
use futures::StreamExt;
use serde_json::Value;

/// One recorded upstream request.
#[derive(Debug, Clone)]
pub struct Recorded {
    /// Path and query, e.g. `/v1/chat/completions`.
    pub uri: String,
    pub headers: HeaderMap,
    pub body: Value,
}

impl Recorded {
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers.get(name).and_then(|v| v.to_str().ok())
    }
}

/// A canned response.
#[derive(Debug, Clone)]
pub struct Canned {
    pub status: u16,
    pub headers: Vec<(&'static str, String)>,
    /// Body pieces, sent as separate chunks with `delay` before each.
    pub chunks: Vec<String>,
    pub delay: Duration,
}

impl Canned {
    pub fn json(status: u16, body: Value) -> Self {
        Self { status, headers: vec![("content-type", "application/json".into())], chunks: vec![body.to_string()], delay: Duration::ZERO }
    }

    pub fn text(status: u16, body: &str) -> Self {
        Self { status, headers: vec![("content-type", "text/plain".into())], chunks: vec![body.to_owned()], delay: Duration::ZERO }
    }

    /// An SSE body split into the given raw pieces.
    pub fn sse(chunks: &[&str]) -> Self {
        Self {
            status: 200,
            headers: vec![("content-type", "text/event-stream".into())],
            chunks: chunks.iter().map(|c| (*c).to_owned()).collect(),
            delay: Duration::ZERO,
        }
    }

    pub fn header(mut self, name: &'static str, value: &str) -> Self {
        self.headers.push((name, value.to_owned()));
        self
    }

    pub fn delayed(mut self, delay: Duration) -> Self {
        self.delay = delay;
        self
    }
}

#[derive(Clone, Default)]
struct Shared {
    requests: Arc<Mutex<Vec<Recorded>>>,
    responses: Arc<Mutex<VecDeque<Canned>>>,
}

pub struct Upstream {
    pub base: String,
    shared: Shared,
}

impl Upstream {
    /// Start a server answering with `responses` in order (then 500).
    pub async fn start(responses: Vec<Canned>) -> Self {
        let shared = Shared::default();
        shared.responses.lock().unwrap().extend(responses);
        let app = Router::new().fallback(handle).with_state(shared.clone());
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let base = format!("http://{}", listener.local_addr().unwrap());
        tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
        Self { base, shared }
    }

    pub fn requests(&self) -> Vec<Recorded> {
        self.shared.requests.lock().unwrap().clone()
    }

    /// The single recorded request.
    pub fn only_request(&self) -> Recorded {
        let reqs = self.requests();
        assert_eq!(reqs.len(), 1, "expected exactly one upstream request");
        reqs.into_iter().next().unwrap()
    }
}

async fn handle(State(shared): State<Shared>, req: Request) -> Response {
    let uri = req.uri().path_and_query().map(|p| p.as_str().to_owned()).unwrap_or_default();
    let headers = req.headers().clone();
    let bytes = axum::body::to_bytes(req.into_body(), usize::MAX).await.unwrap();
    let body = serde_json::from_slice(&bytes).unwrap_or(Value::Null);
    shared.requests.lock().unwrap().push(Recorded { uri, headers, body });

    let canned = shared.responses.lock().unwrap().pop_front().unwrap_or_else(|| Canned::text(500, "no canned response left"));
    let delay = canned.delay;
    let body = Body::from_stream(futures::stream::iter(canned.chunks).then(move |c| async move {
        tokio::time::sleep(delay).await;
        Ok::<_, std::convert::Infallible>(Bytes::from(c))
    }));
    let mut resp = Response::new(body);
    *resp.status_mut() = StatusCode::from_u16(canned.status).unwrap();
    for (k, v) in canned.headers {
        resp.headers_mut().insert(k, v.parse().unwrap());
    }
    resp
}
