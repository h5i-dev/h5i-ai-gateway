//! End-to-end tests for Amazon Bedrock and Google Vertex AI: `Client`
//! against local axum servers standing in for the Bedrock runtime, the
//! Vertex AI API, Google's OAuth2 token endpoint and the GCE metadata
//! server. Everything is offline.

use std::sync::{Arc, Mutex, OnceLock};
use std::time::Duration;

use aws_lc_rs::encoding::{AsDer, Pkcs8V1Der};
use aws_lc_rs::rsa::{KeyPair, KeySize};
use axum::Router;
use axum::body::{Body, Bytes};
use axum::extract::{Request, State};
use axum::http::{HeaderMap, StatusCode};
use axum::response::Response;
use base64::Engine;
use base64::engine::general_purpose::{STANDARD, URL_SAFE_NO_PAD};
use futures::StreamExt;
use gateway_providers::eventstream::encode;
use gateway_providers::{ChatChunk, ChatRequest, Client, Deployment, EmbeddingRequest, ErrorKind, HttpSettings, ProviderError};
use serde_json::{Value, json};

// --- A scripted upstream ------------------------------------------------------

#[derive(Debug, Clone)]
struct Recorded {
    method: String,
    /// Path and query.
    uri: String,
    headers: HeaderMap,
    raw: Bytes,
}

impl Recorded {
    fn header(&self, name: &str) -> Option<&str> {
        self.headers.get(name).and_then(|v| v.to_str().ok())
    }

    fn json(&self) -> Value {
        serde_json::from_slice(&self.raw).unwrap_or(Value::Null)
    }

    fn form(&self) -> Vec<(String, String)> {
        String::from_utf8_lossy(&self.raw).split('&').filter_map(|p| p.split_once('=')).map(|(k, v)| (decode(k), decode(v))).collect()
    }
}

fn decode(s: &str) -> String {
    let b = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'%' && i + 2 < b.len() {
            out.push(u8::from_str_radix(&s[i + 1..i + 3], 16).unwrap());
            i += 3;
        } else {
            out.push(b[i]);
            i += 1;
        }
    }
    String::from_utf8(out).unwrap()
}

#[derive(Debug, Clone)]
struct Canned {
    status: u16,
    headers: Vec<(&'static str, String)>,
    chunks: Vec<Vec<u8>>,
}

impl Canned {
    fn json(status: u16, body: Value) -> Self {
        Self { status, headers: vec![("content-type", "application/json".into())], chunks: vec![body.to_string().into_bytes()] }
    }

    fn text(status: u16, body: &str) -> Self {
        Self { status, headers: vec![("content-type", "text/plain".into())], chunks: vec![body.as_bytes().to_vec()] }
    }

    fn sse(chunks: &[&str]) -> Self {
        Self {
            status: 200,
            headers: vec![("content-type", "text/event-stream".into())],
            chunks: chunks.iter().map(|c| c.as_bytes().to_vec()).collect(),
        }
    }

    /// An AWS event-stream body, re-split into pieces of `piece` bytes.
    fn event_stream(frames: &[Vec<u8>], piece: usize) -> Self {
        let all: Vec<u8> = frames.concat();
        Self {
            status: 200,
            headers: vec![("content-type", "application/vnd.amazon.eventstream".into())],
            chunks: all.chunks(piece).map(<[u8]>::to_vec).collect(),
        }
    }

    fn header(mut self, name: &'static str, value: &str) -> Self {
        self.headers.push((name, value.to_owned()));
        self
    }
}

type Handler = Arc<dyn Fn(&Recorded) -> Canned + Send + Sync>;

#[derive(Clone)]
struct Shared {
    requests: Arc<Mutex<Vec<Recorded>>>,
    handler: Handler,
}

struct Upstream {
    base: String,
    shared: Shared,
}

impl Upstream {
    async fn start(handler: impl Fn(&Recorded) -> Canned + Send + Sync + 'static) -> Self {
        let shared = Shared { requests: Arc::default(), handler: Arc::new(handler) };
        let app = Router::new().fallback(handle).with_state(shared.clone());
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let base = format!("http://{}", listener.local_addr().unwrap());
        tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
        Self { base, shared }
    }

    /// Answer with `responses` in order (then 500).
    async fn script(responses: Vec<Canned>) -> Self {
        let queue = Mutex::new(std::collections::VecDeque::from(responses));
        Self::start(move |_| queue.lock().unwrap().pop_front().unwrap_or_else(|| Canned::text(500, "no canned response left"))).await
    }

    fn host(&self) -> String {
        self.base.trim_start_matches("http://").to_owned()
    }

    fn requests(&self) -> Vec<Recorded> {
        self.shared.requests.lock().unwrap().clone()
    }

    fn requests_to(&self, path_prefix: &str) -> Vec<Recorded> {
        self.requests().into_iter().filter(|r| r.uri.starts_with(path_prefix)).collect()
    }
}

async fn handle(State(shared): State<Shared>, req: Request) -> Response {
    let method = req.method().to_string();
    let uri = req.uri().path_and_query().map(|p| p.as_str().to_owned()).unwrap_or_default();
    let headers = req.headers().clone();
    let raw = axum::body::to_bytes(req.into_body(), usize::MAX).await.unwrap();
    let rec = Recorded { method, uri, headers, raw };
    let canned = (shared.handler)(&rec);
    shared.requests.lock().unwrap().push(rec);
    let body = Body::from_stream(futures::stream::iter(canned.chunks).then(|c| async move {
        tokio::time::sleep(Duration::from_millis(1)).await;
        Ok::<_, std::convert::Infallible>(Bytes::from(c))
    }));
    let mut resp = Response::new(body);
    *resp.status_mut() = StatusCode::from_u16(canned.status).unwrap();
    for (k, v) in canned.headers {
        resp.headers_mut().insert(k, v.parse().unwrap());
    }
    resp
}

// --- helpers --------------------------------------------------------------------

fn client() -> Client {
    Client::new(HttpSettings::default()).unwrap()
}

fn deployment(params: Value) -> Deployment {
    Deployment::from_litellm_params_with_env(&params, |_| None).unwrap()
}

fn request(v: Value) -> ChatRequest {
    serde_json::from_value(v).unwrap()
}

fn hello() -> ChatRequest {
    request(json!({"model": "alias", "messages": [
        {"role": "system", "content": "Be terse."},
        {"role": "user", "content": "Hello"}
    ], "max_tokens": 50}))
}

async fn collect(client: &Client, dep: &Deployment, req: &ChatRequest) -> Vec<Result<ChatChunk, ProviderError>> {
    client.chat_stream(dep, req).await.unwrap().collect().await
}

fn ok_chunks(items: Vec<Result<ChatChunk, ProviderError>>) -> Vec<ChatChunk> {
    items.into_iter().map(Result::unwrap).collect()
}

fn text_of(chunks: &[ChatChunk]) -> String {
    chunks.iter().filter_map(|c| c.choices.first()?.delta.content.clone()).collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn sha256(data: &[u8]) -> String {
    hex(aws_lc_rs::digest::digest(&aws_lc_rs::digest::SHA256, data).as_ref())
}

fn hmac(key: &[u8], data: &[u8]) -> Vec<u8> {
    let key = aws_lc_rs::hmac::Key::new(aws_lc_rs::hmac::HMAC_SHA256, key);
    aws_lc_rs::hmac::sign(&key, data).as_ref().to_vec()
}

/// Independent SigV4 verification of a recorded Bedrock request (what the
/// AWS front end does), signed headers `content-type;host;x-amz-date[;
/// x-amz-security-token]`.
fn verify_sigv4(r: &Recorded, host: &str, secret: &str, region: &str) {
    let auth = r.header("authorization").expect("authorization header");
    let date = r.header("x-amz-date").expect("x-amz-date header");
    let token = r.header("x-amz-security-token");
    let signed = if token.is_some() { "content-type;host;x-amz-date;x-amz-security-token" } else { "content-type;host;x-amz-date" };
    let mut canonical_headers = format!("content-type:{}\nhost:{host}\nx-amz-date:{date}\n", r.header("content-type").unwrap());
    if let Some(t) = token {
        canonical_headers.push_str(&format!("x-amz-security-token:{t}\n"));
    }
    // Non-S3 services encode the (already encoded) path once more.
    let path = r.uri.split('?').next().unwrap().replace('%', "%25");
    let canonical = format!("POST\n{path}\n\n{canonical_headers}\n{signed}\n{}", sha256(&r.raw));
    let day = &date[..8];
    let scope = format!("{day}/{region}/bedrock/aws4_request");
    let to_sign = format!("AWS4-HMAC-SHA256\n{date}\n{scope}\n{}", sha256(canonical.as_bytes()));
    let k = hmac(format!("AWS4{secret}").as_bytes(), day.as_bytes());
    let k = hmac(&k, region.as_bytes());
    let k = hmac(&k, b"bedrock");
    let k = hmac(&k, b"aws4_request");
    let sig = hex(&hmac(&k, to_sign.as_bytes()));
    assert!(auth.starts_with("AWS4-HMAC-SHA256 Credential="), "{auth}");
    assert!(
        auth.ends_with(&format!("/{scope}, SignedHeaders={signed}, Signature={sig}")),
        "signature mismatch: {auth}\ncanonical request:\n{canonical}"
    );
}

// --- Bedrock --------------------------------------------------------------------

fn bedrock_sigv4(up: &Upstream) -> Deployment {
    deployment(json!({
        "model": "bedrock/anthropic.claude-3-5-sonnet-20241022-v2:0",
        "aws_access_key_id": "AKIDTEST",
        "aws_secret_access_key": "test/secret+key",
        "aws_session_token": "session-tok",
        "aws_region_name": "us-east-1",
        "aws_bedrock_runtime_endpoint": up.base,
    }))
}

#[tokio::test]
async fn bedrock_converse_with_sigv4() {
    let up = Upstream::script(vec![Canned::json(
        200,
        json!({
            "output": {"message": {"role": "assistant", "content": [
                {"text": "Checking."},
                {"toolUse": {"toolUseId": "tooluse_1", "name": "get_weather", "input": {"city": "Paris"}}}
            ]}},
            "stopReason": "tool_use",
            "usage": {"inputTokens": 20, "outputTokens": 10, "totalTokens": 30},
            "metrics": {"latencyMs": 120}
        }),
    )])
    .await;
    let dep = bedrock_sigv4(&up);
    let req = request(json!({
        "model": "claude",
        "messages": [{"role": "system", "content": "Be terse."}, {"role": "user", "content": "Weather in Paris?"}],
        "tools": [{"type": "function", "function": {"name": "get_weather",
            "parameters": {"type": "object", "properties": {"city": {"type": "string"}}}}}],
        "tool_choice": "auto", "max_tokens": 256, "temperature": 0.1
    }));
    let resp = client().chat(&dep, &req).await.unwrap();
    let choice = &resp.choices[0];
    assert_eq!(choice.finish_reason.as_deref(), Some("tool_calls"));
    assert_eq!(choice.message.text(), "Checking.");
    let call = &choice.message.tool_calls.as_ref().unwrap()[0];
    assert_eq!((call.id.as_str(), call.function.name.as_str()), ("tooluse_1", "get_weather"));
    assert_eq!(resp.usage.unwrap().total_tokens, 30);

    let reqs = up.requests();
    assert_eq!(reqs.len(), 1);
    let r = &reqs[0];
    assert_eq!(r.method, "POST");
    assert_eq!(r.uri, "/model/anthropic.claude-3-5-sonnet-20241022-v2%3A0/converse");
    assert_eq!(r.header("x-amz-security-token"), Some("session-tok"));
    verify_sigv4(r, &up.host(), "test/secret+key", "us-east-1");
    let body = r.json();
    assert_eq!(body["system"], json!([{"text": "Be terse."}]));
    assert_eq!(body["messages"], json!([{"role": "user", "content": [{"text": "Weather in Paris?"}]}]));
    assert_eq!(body["inferenceConfig"], json!({"maxTokens": 256, "temperature": 0.1}));
    assert_eq!(body["toolConfig"]["toolChoice"], json!({"auto": {}}));
    assert_eq!(body["toolConfig"]["tools"][0]["toolSpec"]["name"], "get_weather");
}

fn stream_frames() -> Vec<Vec<u8>> {
    let ev = |kind: &str, payload: Value| {
        encode(&[(":message-type", "event"), (":event-type", kind), (":content-type", "application/json")], payload.to_string().as_bytes())
    };
    vec![
        ev("messageStart", json!({"role": "assistant", "p": "abcd"})),
        ev("contentBlockDelta", json!({"contentBlockIndex": 0, "delta": {"text": "Bon"}})),
        ev("contentBlockDelta", json!({"contentBlockIndex": 0, "delta": {"text": "jour"}})),
        ev("contentBlockStop", json!({"contentBlockIndex": 0})),
        ev("contentBlockStart", json!({"contentBlockIndex": 1, "start": {"toolUse": {"toolUseId": "tu_9", "name": "lookup"}}})),
        ev("contentBlockDelta", json!({"contentBlockIndex": 1, "delta": {"toolUse": {"input": "{\"q\":"}}})),
        ev("contentBlockDelta", json!({"contentBlockIndex": 1, "delta": {"toolUse": {"input": "\"x\"}"}}})),
        ev("contentBlockStop", json!({"contentBlockIndex": 1})),
        ev("messageStop", json!({"stopReason": "tool_use"})),
        ev(
            "metadata",
            json!({"usage": {"inputTokens": 12, "outputTokens": 6, "totalTokens": 18, "cacheReadInputTokens": 0}, "metrics": {"latencyMs": 9}}),
        ),
    ]
}

#[tokio::test]
async fn bedrock_converse_stream_binary_frames() {
    // Pieces of 7 bytes split every frame mid-prelude / mid-payload.
    let up = Upstream::script(vec![Canned::event_stream(&stream_frames(), 7)]).await;
    let dep = deployment(json!({
        "model": "bedrock/converse/us.anthropic.claude-3-5-haiku-20241022-v1:0",
        "api_key": "bedrock-api-key", "api_base": up.base,
    }));
    let chunks = ok_chunks(collect(&client(), &dep, &hello()).await);
    assert_eq!(text_of(&chunks), "Bonjour");
    let calls: Vec<_> = chunks.iter().filter_map(|c| c.choices.first()?.delta.tool_calls.clone()).flatten().collect();
    assert_eq!(calls[0].id.as_deref(), Some("tu_9"));
    let args: String = calls.iter().filter_map(|c| c.function.as_ref()?.arguments.clone()).collect();
    assert_eq!(args, "{\"q\":\"x\"}");
    let finish = chunks.iter().find_map(|c| c.choices.first()?.finish_reason.clone());
    assert_eq!(finish.as_deref(), Some("tool_calls"));
    let last = chunks.last().unwrap();
    assert!(last.is_usage_only());
    let usage = last.usage.as_ref().unwrap();
    assert_eq!((usage.prompt_tokens, usage.completion_tokens), (12, 6));

    let reqs = up.requests();
    let r = &reqs[0];
    assert_eq!(r.uri, "/model/us.anthropic.claude-3-5-haiku-20241022-v1%3A0/converse-stream");
    assert_eq!(r.header("authorization"), Some("Bearer bedrock-api-key"));
    assert!(r.header("x-amz-date").is_none(), "no SigV4 with an API key");
    assert_eq!(r.json()["inferenceConfig"]["maxTokens"], 50);
}

#[tokio::test]
async fn bedrock_stream_exception_and_corruption() {
    let mut frames = stream_frames()[..2].to_vec();
    frames.push(encode(
        &[(":message-type", "exception"), (":exception-type", "throttlingException"), (":content-type", "application/json")],
        br#"{"message":"Too many tokens, please wait before trying again."}"#,
    ));
    let mut corrupt = stream_frames()[..2].to_vec();
    let last = corrupt.last_mut().unwrap();
    let n = last.len();
    last[n - 5] ^= 0xFF; // payload byte -> message CRC mismatch
    let up = Upstream::script(vec![Canned::event_stream(&frames, 64), Canned::event_stream(&corrupt, 64)]).await;
    let dep = deployment(json!({"model": "bedrock/amazon.nova-pro-v1:0", "api_key": "k", "api_base": up.base}));

    let items = collect(&client(), &dep, &hello()).await;
    let err = items.last().unwrap().as_ref().unwrap_err();
    assert_eq!(err.kind(), ErrorKind::RateLimited);
    assert!(err.is_retryable());
    assert!(err.message().contains("Too many tokens"));
    assert!(items[..items.len() - 1].iter().all(Result::is_ok));

    let items = collect(&client(), &dep, &hello()).await;
    let err = items.last().unwrap().as_ref().unwrap_err();
    assert_eq!(err.kind(), ErrorKind::InvalidResponse);
    assert!(err.message().contains("checksum"), "{}", err.message());
}

#[tokio::test]
async fn bedrock_http_errors() {
    let up = Upstream::script(vec![
        Canned::json(400, json!({"message": "Input is too long for requested model."})).header("x-amzn-errortype", "ValidationException"),
        Canned::json(429, json!({"message": "Too many requests"})),
        Canned::json(403, json!({"message": "The security token included in the request is invalid."})),
    ])
    .await;
    let dep = deployment(json!({"model": "bedrock/anthropic.claude-v2", "api_key": "k", "api_base": up.base}));
    let c = client();
    let e = c.chat(&dep, &hello()).await.unwrap_err();
    assert_eq!(e.kind(), ErrorKind::ContextWindowExceeded);
    let e = c.chat(&dep, &hello()).await.unwrap_err();
    assert_eq!(e.kind(), ErrorKind::RateLimited);
    let e = c.chat_stream(&dep, &hello()).await.err().unwrap();
    assert_eq!(e.kind(), ErrorKind::PermissionDenied);
}

#[tokio::test]
async fn bedrock_embeddings_titan_and_cohere() {
    let up = Upstream::start(|r| {
        let body = r.json();
        if r.uri.contains("titan") {
            let text = body["inputText"].as_str().unwrap_or_default();
            Canned::json(200, json!({"embedding": [text.len() as f64, 0.5], "inputTextTokenCount": text.len()}))
        } else {
            Canned::json(200, json!({"embeddings": [[1.0, 2.0], [3.0, 4.0]], "id": "e1"})).header("x-amzn-bedrock-input-token-count", "7")
        }
    })
    .await;
    let titan =
        Deployment::from_litellm_params_with_env(&json!({"model": "bedrock/amazon.titan-embed-text-v2:0", "api_base": up.base}), |n| match n {
            "AWS_ACCESS_KEY_ID" => Some("AKIDENV".into()),
            "AWS_SECRET_ACCESS_KEY" => Some("envsecret".into()),
            "AWS_REGION" => Some("eu-central-1".into()),
            _ => None,
        })
        .unwrap();
    let req: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": ["a", "bbb"], "dimensions": 512})).unwrap();
    let resp = client().embeddings(&titan, &req).await.unwrap();
    assert_eq!(resp.data.len(), 2);
    assert_eq!(serde_json::to_value(&resp.data[1].embedding).unwrap(), json!([3.0, 0.5]));
    assert_eq!(resp.usage.prompt_tokens, 4);
    let titan_reqs = up.requests_to("/model/amazon.titan");
    assert_eq!(titan_reqs.len(), 2);
    for r in &titan_reqs {
        assert_eq!(r.uri, "/model/amazon.titan-embed-text-v2%3A0/invoke");
        assert_eq!(r.json()["dimensions"], 512);
        assert!(r.header("x-amz-security-token").is_none());
        verify_sigv4(r, &up.host(), "envsecret", "eu-central-1");
    }

    let cohere = deployment(json!({"model": "bedrock/cohere.embed-english-v3", "api_key": "k", "api_base": up.base}));
    let req: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": ["x", "y"]})).unwrap();
    let resp = client().embeddings(&cohere, &req).await.unwrap();
    assert_eq!(resp.data.len(), 2);
    assert_eq!(resp.usage.prompt_tokens, 7);
    let r = &up.requests_to("/model/cohere")[0];
    assert_eq!(r.json(), json!({"texts": ["x", "y"], "input_type": "search_document"}));
}

// --- Vertex AI ------------------------------------------------------------------

/// A 2048-bit RSA key (PKCS#8 PEM) generated once per test run.
fn test_key_pem() -> &'static str {
    static PEM: OnceLock<String> = OnceLock::new();
    PEM.get_or_init(|| {
        let pair = KeyPair::generate(KeySize::Rsa2048).unwrap();
        let der = AsDer::<Pkcs8V1Der>::as_der(&pair).unwrap();
        let b64 = STANDARD.encode(der.as_ref());
        let lines: Vec<&str> = b64.as_bytes().chunks(64).map(|c| std::str::from_utf8(c).unwrap()).collect();
        format!("-----BEGIN PRIVATE KEY-----\n{}\n-----END PRIVATE KEY-----\n", lines.join("\n"))
    })
}

fn service_account(token_uri: &str) -> Value {
    json!({
        "type": "service_account",
        "project_id": "sa-project",
        "private_key_id": "key-1",
        "private_key": test_key_pem(),
        "client_email": "gw@sa-project.iam.gserviceaccount.com",
        "client_id": "1",
        "token_uri": token_uri,
    })
}

/// One server for both the token endpoint (`/token`) and the Vertex API.
async fn vertex_upstream(expires_in: u64, api: impl Fn(&Recorded) -> Canned + Send + Sync + 'static) -> Upstream {
    let counter = Mutex::new(0u32);
    Upstream::start(move |r| {
        if r.uri == "/token" {
            let mut n = counter.lock().unwrap();
            *n += 1;
            Canned::json(200, json!({"access_token": format!("ya29.token-{n}"), "expires_in": expires_in, "token_type": "Bearer"}))
        } else {
            api(r)
        }
    })
    .await
}

fn gemini_reply() -> Canned {
    Canned::json(
        200,
        json!({
            "candidates": [{"content": {"role": "model", "parts": [{"text": "Bonjour"}]}, "finishReason": "STOP", "index": 0}],
            "usageMetadata": {"promptTokenCount": 4, "candidatesTokenCount": 2, "totalTokenCount": 6},
            "modelVersion": "gemini-2.0-flash-001"
        }),
    )
}

fn vertex_gemini(up: &Upstream) -> Deployment {
    deployment(json!({
        "model": "vertex_ai/gemini-2.0-flash",
        "vertex_credentials": service_account(&format!("{}/token", up.base)).to_string(),
        "vertex_location": "europe-west4",
        "api_base": up.base,
    }))
}

#[tokio::test]
async fn vertex_gemini_with_service_account_token_exchange() {
    let up = vertex_upstream(3600, |_| gemini_reply()).await;
    let dep = vertex_gemini(&up);
    let c = client();
    let resp = c.chat(&dep, &hello()).await.unwrap();
    assert_eq!(resp.choices[0].message.text(), "Bonjour");
    assert_eq!(resp.usage.unwrap().total_tokens, 6);
    // A second call (and a clone of the client) reuses the cached token.
    c.clone().chat(&dep, &hello()).await.unwrap();

    let tokens = up.requests_to("/token");
    assert_eq!(tokens.len(), 1, "token exchanged once");
    let t = &tokens[0];
    assert_eq!(t.header("content-type"), Some("application/x-www-form-urlencoded"));
    let form = t.form();
    assert_eq!(form[0], ("grant_type".to_owned(), "urn:ietf:params:oauth:grant-type:jwt-bearer".to_owned()));
    let jwt = &form[1].1;
    let parts: Vec<&str> = jwt.split('.').collect();
    assert_eq!(parts.len(), 3);
    let claims: Value = serde_json::from_slice(&URL_SAFE_NO_PAD.decode(parts[1]).unwrap()).unwrap();
    assert_eq!(claims["iss"], "gw@sa-project.iam.gserviceaccount.com");
    assert_eq!(claims["aud"], format!("{}/token", up.base));
    assert_eq!(claims["scope"], "https://www.googleapis.com/auth/cloud-platform");

    let api = up.requests_to("/v1/");
    assert_eq!(api.len(), 2);
    assert_eq!(api[0].uri, "/v1/projects/sa-project/locations/europe-west4/publishers/google/models/gemini-2.0-flash:generateContent");
    for r in &api {
        assert_eq!(r.header("authorization"), Some("Bearer ya29.token-1"));
        assert!(r.header("x-goog-api-key").is_none());
    }
    assert_eq!(api[0].json()["systemInstruction"], json!({"parts": [{"text": "Be terse."}]}));
}

#[tokio::test]
async fn vertex_token_cache_refreshes_and_is_shared_under_concurrency() {
    // Tokens that expire within the refresh margin are re-exchanged.
    let up = vertex_upstream(60, |_| gemini_reply()).await;
    let dep = vertex_gemini(&up);
    let c = client();
    c.chat(&dep, &hello()).await.unwrap();
    c.chat(&dep, &hello()).await.unwrap();
    assert_eq!(up.requests_to("/token").len(), 2);
    let api = up.requests_to("/v1/");
    assert_eq!(api[1].header("authorization"), Some("Bearer ya29.token-2"));

    // Long-lived token: eight concurrent first calls, one exchange.
    let up = vertex_upstream(3600, |_| gemini_reply()).await;
    let dep = vertex_gemini(&up);
    let c = client();
    let req = hello();
    let calls = (0..8).map(|_| c.chat(&dep, &req));
    for r in futures::future::join_all(calls).await {
        r.unwrap();
    }
    assert_eq!(up.requests_to("/token").len(), 1);
    assert_eq!(up.requests_to("/v1/").len(), 8);
}

#[tokio::test]
async fn vertex_token_exchange_failure_is_an_auth_error() {
    let up = Upstream::start(|r| {
        if r.uri == "/token" {
            Canned::json(400, json!({"error": "invalid_grant", "error_description": "Invalid JWT Signature."}))
        } else {
            gemini_reply()
        }
    })
    .await;
    let err = client().chat(&vertex_gemini(&up), &hello()).await.unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Authentication);
    assert!(err.message().contains("Invalid JWT Signature"));
    assert!(err.is_retryable());
    assert!(up.requests_to("/v1/").is_empty());
}

#[tokio::test]
async fn vertex_gemini_stream() {
    let up = vertex_upstream(3600, |_| {
        Canned::sse(&[
            "data: {\"candidates\":[{\"content\":{\"role\":\"model\",\"parts\":[{\"text\":\"Bon\"}]},\"index\":0}]}\r\n\r\n",
            "data: {\"candidates\":[{\"content\":{\"role\":\"model\",\"parts\":[{\"text\":\"jour\"}]},\"finishReason\":\"STOP\",\"index\":0}],\"usageMetadata\":{\"promptTokenCount\":3,\"candidatesTokenCount\":2,\"totalTokenCount\":5}}\r\n\r\n",
        ])
    })
    .await;
    let dep = vertex_gemini(&up);
    let chunks = ok_chunks(collect(&client(), &dep, &hello()).await);
    assert_eq!(text_of(&chunks), "Bonjour");
    assert_eq!(chunks.last().unwrap().usage.as_ref().unwrap().total_tokens, 5);
    let r = &up.requests_to("/v1/")[0];
    assert!(r.uri.ends_with("/models/gemini-2.0-flash:streamGenerateContent?alt=sse"), "{}", r.uri);
}

fn vertex_claude(up: &Upstream) -> Deployment {
    deployment(json!({
        "model": "vertex_ai/claude-sonnet-4-5@20250929",
        "vertex_credentials": service_account(&format!("{}/token", up.base)),
        "vertex_project": "claude-proj",
        "vertex_location": "us-east5",
        "api_base": up.base,
    }))
}

#[tokio::test]
async fn vertex_anthropic_raw_predict() {
    let up = vertex_upstream(3600, |_| {
        Canned::json(
            200,
            json!({
                "id": "msg_vrtx_1", "type": "message", "role": "assistant", "model": "claude-sonnet-4-5-20250929",
                "content": [{"type": "text", "text": "Hi there"}],
                "stop_reason": "end_turn",
                "usage": {"input_tokens": 9, "output_tokens": 3}
            }),
        )
    })
    .await;
    let resp = client().chat(&vertex_claude(&up), &hello()).await.unwrap();
    assert_eq!(resp.choices[0].message.text(), "Hi there");
    assert_eq!(resp.choices[0].finish_reason.as_deref(), Some("stop"));
    assert_eq!(resp.usage.unwrap().prompt_tokens, 9);

    let r = &up.requests_to("/v1/")[0];
    assert_eq!(r.uri, "/v1/projects/claude-proj/locations/us-east5/publishers/anthropic/models/claude-sonnet-4-5@20250929:rawPredict");
    assert_eq!(r.header("authorization"), Some("Bearer ya29.token-1"));
    assert!(r.header("x-api-key").is_none());
    let body = r.json();
    assert_eq!(body["anthropic_version"], "vertex-2023-10-16");
    assert!(body.get("model").is_none());
    assert_eq!(body["max_tokens"], 50);
    assert_eq!(body["system"], json!([{"type": "text", "text": "Be terse."}]));
}

#[tokio::test]
async fn vertex_anthropic_stream_raw_predict() {
    let up = vertex_upstream(3600, |_| {
        Canned::sse(&[
            "event: message_start\ndata: {\"type\":\"message_start\",\"message\":{\"id\":\"msg_1\",\"model\":\"claude-sonnet-4-5\",\"usage\":{\"input_tokens\":11,\"output_tokens\":1}}}\n\n",
            "event: content_block_start\ndata: {\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"text\",\"text\":\"\"}}\n\n",
            "event: content_block_delta\ndata: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"Hel\"}}\n\n",
            "event: content_block_delta\ndata: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"lo\"}}\n\n",
            "event: content_block_stop\ndata: {\"type\":\"content_block_stop\",\"index\":0}\n\n",
            "event: message_delta\ndata: {\"type\":\"message_delta\",\"delta\":{\"stop_reason\":\"end_turn\"},\"usage\":{\"output_tokens\":4}}\n\n",
            "event: message_stop\ndata: {\"type\":\"message_stop\"}\n\n",
        ])
    })
    .await;
    let chunks = ok_chunks(collect(&client(), &vertex_claude(&up), &hello()).await);
    assert_eq!(text_of(&chunks), "Hello");
    let usage = chunks.last().unwrap().usage.clone().unwrap();
    assert_eq!((usage.prompt_tokens, usage.completion_tokens), (11, 4));
    let r = &up.requests_to("/v1/")[0];
    assert!(r.uri.ends_with(":streamRawPredict"), "{}", r.uri);
    assert_eq!(r.json()["stream"], true);
}

#[tokio::test]
async fn vertex_embeddings_predict() {
    let up = vertex_upstream(3600, |_| {
        Canned::json(
            200,
            json!({"predictions": [
                {"embeddings": {"values": [0.1, 0.2], "statistics": {"token_count": 2, "truncated": false}}},
                {"embeddings": {"values": [0.3, 0.4], "statistics": {"token_count": 3, "truncated": false}}}
            ]}),
        )
    })
    .await;
    let dep = deployment(json!({
        "model": "vertex_ai/text-embedding-004",
        "vertex_credentials": service_account(&format!("{}/token", up.base)),
        "api_base": up.base,
    }));
    let req: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": ["a", "b"], "dimensions": 64})).unwrap();
    let resp = client().embeddings(&dep, &req).await.unwrap();
    assert_eq!(resp.data.len(), 2);
    assert_eq!(resp.usage.prompt_tokens, 5);
    let r = &up.requests_to("/v1/")[0];
    assert_eq!(r.uri, "/v1/projects/sa-project/locations/us-central1/publishers/google/models/text-embedding-004:predict");
    assert_eq!(r.json(), json!({"instances": [{"content": "a"}, {"content": "b"}], "parameters": {"outputDimensionality": 64}}));
}

#[tokio::test]
async fn vertex_metadata_server_fallback_and_access_token() {
    let up = Upstream::start(|r| match r.uri.as_str() {
        "/computeMetadata/v1/instance/service-accounts/default/token" => {
            Canned::json(200, json!({"access_token": "ya29.metadata", "expires_in": 3599, "token_type": "Bearer"}))
        }
        "/computeMetadata/v1/project/project-id" => Canned::text(200, "gce-project"),
        _ => gemini_reply(),
    })
    .await;
    let host = up.host();
    let base = up.base.clone();
    let dep = Deployment::from_litellm_params_with_env(&json!({"model": "vertex_ai/gemini-2.0-flash", "api_base": base}), |n| {
        (n == "GCE_METADATA_HOST").then(|| host.clone())
    })
    .unwrap();
    let c = client();
    c.chat(&dep, &hello()).await.unwrap();
    c.chat(&dep, &hello()).await.unwrap();
    let md = up.requests_to("/computeMetadata/");
    assert_eq!(md.len(), 2, "token and project fetched once each");
    assert!(md.iter().all(|r| r.method == "GET" && r.header("metadata-flavor") == Some("Google")));
    let api = up.requests_to("/v1/");
    assert_eq!(api.len(), 2);
    assert!(api[0].uri.starts_with("/v1/projects/gce-project/locations/us-central1/"));
    assert_eq!(api[0].header("authorization"), Some("Bearer ya29.metadata"));

    // A pre-supplied access token needs no exchange at all.
    let up = Upstream::script(vec![gemini_reply()]).await;
    let dep = deployment(json!({
        "model": "vertex_ai/gemini-2.0-flash", "api_key": "ya29.static",
        "vertex_project": "p", "api_base": up.base
    }));
    client().chat(&dep, &hello()).await.unwrap();
    let reqs = up.requests();
    assert_eq!(reqs.len(), 1);
    assert_eq!(reqs[0].header("authorization"), Some("Bearer ya29.static"));
    assert!(!reqs[0].uri.contains("key="));
}
