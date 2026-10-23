//! A mock OpenAI-compatible upstream for benchmarking gateways.
//!
//! Serves `/v1/chat/completions` (non-streaming and SSE streaming, honouring
//! `stream_options.include_usage`), `/v1/embeddings` and `/v1/models`, with a
//! fixed latency before the response (or the first chunk), a configurable
//! number of stream chunks and delay between them, and responses shaped and
//! sized like OpenAI's (ids, `system_fingerprint`, `usage` with details,
//! 1536-dimensional embeddings).

use axum::Router;
use axum::body::{Body, Bytes};
use axum::extract::State;
use axum::http::{HeaderValue, StatusCode, header};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::serve::ListenerExt;
use gateway_bench::{Args, runtime};
use serde_json::{Value, json};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

const USAGE: &str = "usage: mock-upstream [--host 127.0.0.1] [--port 9000] [--threads 0]
  [--latency-ms 0]          fixed delay before a response or its first stream chunk
  [--stream-chunks 20]      content chunks per streamed completion
  [--chunk-delay-ms 0]      delay between stream chunks
  [--completion-tokens 120] completion length (tokens, ~4 characters each)
  [--embedding-dims 1536]";

struct Mock {
    latency: Duration,
    chunk_delay: Duration,
    /// Completion text split into `stream_chunks` pieces.
    pieces: Vec<String>,
    content: String,
    completion_tokens: u64,
    /// One embedding vector rendered as a JSON array.
    embedding: String,
    counter: AtomicU64,
}

fn main() {
    let a = Args::parse(USAGE, &[]);
    let host: String = a.get("host", "127.0.0.1".to_string());
    let port: u16 = a.get("port", 9000);
    let chunks: usize = a.get::<usize>("stream-chunks", 20).max(1);
    let completion_tokens: u64 = a.get("completion-tokens", 120);
    let dims: usize = a.get("embedding-dims", 1536);

    // ~4 characters per token, English-looking text.
    const WORDS: [&str; 16] = [
        "the",
        "gateway",
        "routes",
        "each",
        "request",
        "to",
        "a",
        "deployment",
        "and",
        "records",
        "its",
        "spend",
        "against",
        "the",
        "key's",
        "budget",
    ];
    let words: Vec<&str> = (0..completion_tokens as usize).map(|i| WORDS[i % WORDS.len()]).collect();
    let per = words.len().div_ceil(chunks).max(1);
    let mut pieces: Vec<String> = words.chunks(per).map(|c| format!("{} ", c.join(" "))).collect();
    while pieces.len() < chunks {
        pieces.push(" ".into());
    }
    let content = pieces.concat().trim_end().to_string();

    // Deterministic pseudo-random unit-ish floats, printed like OpenAI's.
    let mut x: u64 = 0x9E3779B97F4A7C15;
    let floats: Vec<String> = (0..dims)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let f = ((x >> 11) as f64 / (1u64 << 53) as f64 - 0.5) * 0.08;
            format!("{f:.9}")
        })
        .collect();
    let embedding = format!("[{}]", floats.join(","));

    let mock = Arc::new(Mock {
        latency: Duration::from_millis(a.get("latency-ms", 0)),
        chunk_delay: Duration::from_millis(a.get("chunk-delay-ms", 0)),
        pieces,
        content,
        completion_tokens,
        embedding,
        counter: AtomicU64::new(0),
    });
    let app = Router::new()
        .route("/v1/chat/completions", post(chat)) // h5i-allow: no-actor (the mock upstream of the benchmark)
        .route("/chat/completions", post(chat)) // h5i-allow: no-actor (the mock upstream of the benchmark)
        .route("/v1/embeddings", post(embeddings)) // h5i-allow: no-actor (the mock upstream of the benchmark)
        .route("/embeddings", post(embeddings)) // h5i-allow: no-actor (the mock upstream of the benchmark)
        .route("/v1/models", get(models))
        .route("/models", get(models))
        .route("/health", get(|| async { "ok" }))
        .with_state(mock);

    runtime(a.get("threads", 0)).block_on(async move {
        let listener = tokio::net::TcpListener::bind((host.as_str(), port)).await.expect("bind");
        eprintln!("mock-upstream listening on {host}:{port}");
        let listener = listener.tap_io(|tcp| {
            let _ = tcp.set_nodelay(true);
        });
        axum::serve(listener, app)
            .with_graceful_shutdown(async {
                let _ = tokio::signal::ctrl_c().await;
            })
            .await
            .expect("serve");
    });
}

fn now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

fn bad_request(msg: &str) -> Response {
    let body = json!({"error": {"message": msg, "type": "invalid_request_error", "code": null}});
    (StatusCode::BAD_REQUEST, axum::Json(body)).into_response()
}

fn json_response(body: String) -> Response {
    let mut r = Response::new(Body::from(body));
    r.headers_mut().insert(header::CONTENT_TYPE, HeaderValue::from_static("application/json"));
    r
}

/// Rough prompt token count: characters of message content / 4.
fn prompt_tokens(v: &Value) -> u64 {
    fn chars(v: &Value) -> usize {
        match v {
            Value::String(s) => s.len(),
            Value::Array(a) => a.iter().map(chars).sum(),
            Value::Object(o) => o.get("content").or_else(|| o.get("text")).map(chars).unwrap_or(0),
            _ => 0,
        }
    }
    let n = v.get("messages").or_else(|| v.get("input")).map(chars).unwrap_or(0);
    (n as u64).div_ceil(4).max(1)
}

async fn chat(State(m): State<Arc<Mock>>, body: Bytes) -> Response {
    let Ok(req) = serde_json::from_slice::<Value>(&body) else {
        return bad_request("invalid JSON body");
    };
    let model = req.get("model").and_then(Value::as_str).unwrap_or("gpt-4o-mini").to_string();
    let stream = req.get("stream").and_then(Value::as_bool).unwrap_or(false);
    let include_usage = req.pointer("/stream_options/include_usage").and_then(Value::as_bool).unwrap_or(false);
    let prompt = prompt_tokens(&req);
    let id = format!("chatcmpl-mock{:016x}", m.counter.fetch_add(1, Ordering::Relaxed));
    let created = now();
    let usage = json!({
        "prompt_tokens": prompt,
        "completion_tokens": m.completion_tokens,
        "total_tokens": prompt + m.completion_tokens,
        "prompt_tokens_details": {"cached_tokens": 0, "audio_tokens": 0},
        "completion_tokens_details": {"reasoning_tokens": 0, "audio_tokens": 0,
            "accepted_prediction_tokens": 0, "rejected_prediction_tokens": 0}
    });

    if !stream {
        if !m.latency.is_zero() {
            tokio::time::sleep(m.latency).await;
        }
        let body = json!({
            "id": id,
            "object": "chat.completion",
            "created": created,
            "model": model,
            "choices": [{
                "index": 0,
                "message": {"role": "assistant", "content": m.content, "refusal": null, "annotations": []},
                "logprobs": null,
                "finish_reason": "stop"
            }],
            "usage": usage,
            "service_tier": "default",
            "system_fingerprint": "fp_mock0001"
        });
        return json_response(body.to_string());
    }

    let chunk = move |delta: Value, finish: Value, usage: Option<&Value>| -> Bytes {
        let mut c = json!({
            "id": id,
            "object": "chat.completion.chunk",
            "created": created,
            "model": model,
            "service_tier": "default",
            "system_fingerprint": "fp_mock0001",
            "choices": if usage.is_some() { json!([]) } else {
                json!([{"index": 0, "delta": delta, "logprobs": null, "finish_reason": finish}])
            },
        });
        if include_usage {
            c["usage"] = usage.cloned().unwrap_or(Value::Null);
        }
        Bytes::from(format!("data: {c}\n\n"))
    };
    let (tx, rx) = tokio::sync::mpsc::channel::<Result<Bytes, std::io::Error>>(4);
    tokio::spawn(async move {
        if !m.latency.is_zero() {
            tokio::time::sleep(m.latency).await;
        }
        let first = chunk(json!({"role": "assistant", "content": "", "refusal": null}), Value::Null, None);
        if tx.send(Ok(first)).await.is_err() {
            return;
        }
        for piece in &m.pieces {
            if !m.chunk_delay.is_zero() {
                tokio::time::sleep(m.chunk_delay).await;
            }
            if tx.send(Ok(chunk(json!({"content": piece}), Value::Null, None))).await.is_err() {
                return;
            }
        }
        let _ = tx.send(Ok(chunk(json!({}), json!("stop"), None))).await;
        if include_usage {
            let _ = tx.send(Ok(chunk(Value::Null, Value::Null, Some(&usage)))).await;
        }
        let _ = tx.send(Ok(Bytes::from_static(b"data: [DONE]\n\n"))).await;
    });
    let stream = futures::stream::unfold(rx, |mut rx| async move { rx.recv().await.map(|x| (x, rx)) });
    let mut r = Response::new(Body::from_stream(stream));
    let h = r.headers_mut();
    h.insert(header::CONTENT_TYPE, HeaderValue::from_static("text/event-stream; charset=utf-8"));
    h.insert(header::CACHE_CONTROL, HeaderValue::from_static("no-cache"));
    r
}

async fn embeddings(State(m): State<Arc<Mock>>, body: Bytes) -> Response {
    let Ok(req) = serde_json::from_slice::<Value>(&body) else {
        return bad_request("invalid JSON body");
    };
    let model = req.get("model").and_then(Value::as_str).unwrap_or("text-embedding-3-small");
    let n = match req.get("input") {
        Some(Value::Array(a)) if a.first().is_some_and(|x| !x.is_number()) => a.len(),
        Some(_) => 1,
        None => return bad_request("missing input"),
    };
    let prompt = prompt_tokens(&req);
    if !m.latency.is_zero() {
        tokio::time::sleep(m.latency).await;
    }
    let mut out = String::with_capacity(64 + n * (m.embedding.len() + 64));
    out.push_str(r#"{"object":"list","data":["#);
    for i in 0..n {
        if i > 0 {
            out.push(',');
        }
        out.push_str(r#"{"object":"embedding","index":"#);
        out.push_str(&i.to_string());
        out.push_str(r#","embedding":"#);
        out.push_str(&m.embedding);
        out.push('}');
    }
    out.push_str(&format!(r#"],"model":{},"usage":{{"prompt_tokens":{prompt},"total_tokens":{prompt}}}}}"#, Value::from(model)));
    json_response(out)
}

async fn models() -> Response {
    let body = json!({"object": "list", "data": [
        {"id": "gpt-4o-mini", "object": "model", "created": 1721172741, "owned_by": "system"},
        {"id": "text-embedding-3-small", "object": "model", "created": 1705948997, "owned_by": "system"}
    ]});
    json_response(body.to_string())
}
