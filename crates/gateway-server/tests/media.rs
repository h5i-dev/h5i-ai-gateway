//! Images and audio end to end: the router with the in-memory executor and a
//! local OpenAI/Azure-shaped upstream. Checks the upstream requests, the
//! responses passed back, and that keys are charged what the media units
//! say (and refused when the worst case does not fit their budget).

use axum::Json;
use axum::Router;
use axum::body::{Body, Bytes};
use axum::extract::{Multipart, OriginalUri, RawQuery, State};
use axum::http::{HeaderMap, Request, StatusCode, header};
use axum::response::{IntoResponse, Response};
use axum::routing::post;
use gateway_providers::media::Multipart as Form;
use gateway_server::config::Config;
use gateway_server::kernel::{Backend, MemoryExecutor};
use gateway_server::registry::Registry;
use gateway_server::{AppState, ProxySettings, auth::GatewayAuth, router, sync};
use http_body_util::BodyExt;
use serde_json::{Value, json};
use std::sync::{Arc, Mutex};
use std::time::Duration;
use tower::ServiceExt;

const MASTER: &str = "sk-master";

/// One request the upstream received.
#[derive(Debug, Clone)]
struct Seen {
    path: String,
    query: Option<String>,
    headers: HeaderMap,
    /// The JSON body, or the multipart fields (text values; files as `file:<name>:<len>`).
    body: Value,
}

type Log = Arc<Mutex<Vec<Seen>>>;

fn record(log: &Log, path: String, query: Option<String>, headers: HeaderMap, body: Value) {
    log.lock().unwrap().push(Seen { path, query, headers, body });
}

async fn form_fields(mut mp: Multipart) -> Value {
    let mut out = serde_json::Map::new();
    while let Some(f) = mp.next_field().await.unwrap() {
        let name = f.name().unwrap().to_owned();
        let file = f.file_name().map(str::to_owned);
        let data = f.bytes().await.unwrap();
        let v = match file {
            Some(file) => format!("file:{file}:{}", data.len()),
            None => String::from_utf8(data.to_vec()).unwrap(),
        };
        match out.get_mut(&name) {
            Some(Value::Array(a)) => a.push(v.into()),
            Some(old) => *old = json!([old.clone(), v]),
            None => {
                out.insert(name, v.into());
            }
        }
    }
    Value::Object(out)
}

async fn images(State(log): State<Log>, path: OriginalUri, q: RawQuery, h: HeaderMap, body: Bytes) -> Response {
    let body: Value = serde_json::from_slice(&body).unwrap();
    record(&log, path.path().to_owned(), q.0, h, body.clone());
    let n = body["n"].as_u64().unwrap_or(1);
    let data: Vec<Value> = (0..n).map(|i| json!({"url": format!("https://img.example/{i}.png"), "revised_prompt": "revised"})).collect();
    let mut resp = json!({"created": 1700000000, "data": data});
    if body["model"].as_str().unwrap_or_default().contains("gpt-image") {
        resp = json!({"created": 1700000000, "data": [{"b64_json": "QUJD"}], "size": "1024x1024", "quality": "high",
            "usage": {"input_tokens": 12, "output_tokens": 4160, "total_tokens": 4172,
                      "input_tokens_details": {"text_tokens": 12, "image_tokens": 0}}});
    }
    Json(resp).into_response()
}

async fn edits(State(log): State<Log>, path: OriginalUri, h: HeaderMap, mp: Multipart) -> Response {
    let fields = form_fields(mp).await;
    record(&log, path.path().to_owned(), None, h, fields);
    Json(json!({"created": 1, "data": [{"url": "https://img.example/edit.png"}]})).into_response()
}

async fn transcriptions(State(log): State<Log>, path: OriginalUri, q: RawQuery, h: HeaderMap, mp: Multipart) -> Response {
    let fields = form_fields(mp).await;
    record(&log, path.path().to_owned(), q.0, h, fields.clone());
    match fields["response_format"].as_str().unwrap_or("json") {
        "verbose_json" => {
            Json(json!({"task": "transcribe", "language": "english", "duration": 9.5, "text": "hello world", "segments": []}))
                .into_response()
        }
        "text" => ([(header::CONTENT_TYPE, "text/plain; charset=utf-8")], "hello world\n").into_response(),
        "srt" => ([(header::CONTENT_TYPE, "application/x-subrip")], "1\n00:00:00,000 --> 00:00:04,000\nhello world\n\n").into_response(),
        // json: no duration, as Groq answers.
        _ => Json(json!({"text": "hello world"})).into_response(),
    }
}

async fn speech(State(log): State<Log>, path: OriginalUri, h: HeaderMap, body: Bytes) -> Response {
    let body: Value = serde_json::from_slice(&body).unwrap();
    record(&log, path.path().to_owned(), None, h, body);
    let chunks = futures::stream::iter([Ok::<_, std::io::Error>(Bytes::from_static(b"ID3fake")), Ok(Bytes::from_static(b"-mp3-audio"))]);
    ([(header::CONTENT_TYPE, "audio/mpeg")], Body::from_stream(chunks)).into_response()
}

/// An OpenAI- and Azure-shaped upstream; returns its base URL and request log.
async fn upstream() -> (String, Log) {
    let log: Log = Arc::default();
    let app = Router::new()
        .route("/v1/images/generations", post(images))
        .route("/v1/images/edits", post(edits))
        .route("/v1/audio/transcriptions", post(transcriptions))
        .route("/v1/audio/translations", post(transcriptions))
        .route("/v1/audio/speech", post(speech))
        .route("/openai/deployments/{d}/images/generations", post(images))
        .route("/openai/deployments/{d}/audio/transcriptions", post(transcriptions))
        .route("/openai/deployments/{d}/audio/speech", post(speech))
        .with_state(log.clone());
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
    (format!("http://{addr}"), log)
}

async fn gateway(yaml: &str) -> Router {
    let config = Config::parse(yaml).unwrap();
    let env = |_: &str| None;
    let state = AppState {
        backend: Arc::new(Backend::Memory(MemoryExecutor::new(Box::new(|_, _| {})))),
        keys: Arc::new(GatewayAuth::new(Some(MASTER.into()), "test-secret", 1)),
        registry: Arc::new(Registry::from_config(&config, &env).unwrap()),
        client: gateway_providers::Client::new(Default::default()).unwrap(),
        settings: Arc::new(ProxySettings {
            org: 1,
            num_retries: config.num_retries(),
            fallbacks: config.fallbacks(),
            aliases: config.router_settings.model_group_alias.clone(),
            timeout: Duration::from_secs(30),
            default_max_tokens: 100,
        }),
        spend: None,
    };
    sync(&state, &config).await.unwrap();
    router(state)
}

struct Reply {
    status: StatusCode,
    headers: HeaderMap,
    bytes: Bytes,
}

impl Reply {
    fn json(&self) -> Value {
        serde_json::from_slice(&self.bytes).unwrap_or_else(|_| Value::String(String::from_utf8_lossy(&self.bytes).into()))
    }

    fn cost(&self) -> f64 {
        self.headers["x-litellm-response-cost"].to_str().unwrap().parse().unwrap()
    }
}

async fn send(app: &Router, path: &str, key: &str, content_type: &str, body: Vec<u8>) -> Reply {
    let req = Request::builder()
        .method("POST")
        .uri(path)
        .header("authorization", format!("Bearer {key}"))
        .header("content-type", content_type)
        .body(Body::from(body))
        .unwrap();
    let resp = app.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let headers = resp.headers().clone();
    let bytes = resp.into_body().collect().await.unwrap().to_bytes();
    Reply { status, headers, bytes }
}

async fn post_json(app: &Router, path: &str, key: &str, body: Value) -> Reply {
    send(app, path, key, "application/json", body.to_string().into_bytes()).await
}

async fn post_form(app: &Router, path: &str, key: &str, form: Form) -> Reply {
    let (ct, body) = form.finish();
    send(app, path, key, &ct, body).await
}

async fn new_key(app: &Router, body: Value) -> String {
    let r = post_json(app, "/key/generate", MASTER, body).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    r.json()["key"].as_str().unwrap().to_string()
}

async fn key_spend(app: &Router, key: &str) -> (f64, f64) {
    let req = Request::builder().uri("/key/info").header("authorization", format!("Bearer {key}")).body(Body::empty()).unwrap();
    let resp = app.clone().oneshot(req).await.unwrap();
    let v: Value = serde_json::from_slice(&resp.into_body().collect().await.unwrap().to_bytes()).unwrap();
    (v["info"]["spend"].as_f64().unwrap(), v["info"]["reserved_spend"].as_f64().unwrap())
}

fn close(a: f64, b: f64) -> bool {
    (a - b).abs() < 1e-6
}

/// 16 kHz, 16-bit mono PCM silence.
fn wav(seconds: f64) -> Vec<u8> {
    let data_len = (32_000.0 * seconds) as u32;
    let mut b = b"RIFF".to_vec();
    b.extend((36 + data_len).to_le_bytes());
    b.extend(b"WAVEfmt ");
    b.extend(16u32.to_le_bytes());
    b.extend(1u16.to_le_bytes());
    b.extend(1u16.to_le_bytes());
    b.extend(16_000u32.to_le_bytes());
    b.extend(32_000u32.to_le_bytes());
    b.extend(2u16.to_le_bytes());
    b.extend(16u16.to_le_bytes());
    b.extend(b"data");
    b.extend(data_len.to_le_bytes());
    b.resize(b.len() + data_len as usize, 0);
    b
}

fn config(base: &str) -> String {
    format!(
        r#"
model_list:
  - model_name: dalle
    litellm_params: {{model: openai/dall-e-3, api_key: sk-up, api_base: "{base}/v1"}}
  - model_name: gpt-image
    litellm_params: {{model: openai/gpt-image-1, api_key: sk-up, api_base: "{base}/v1"}}
  - model_name: azure-dalle
    litellm_params: {{model: azure/my-dalle, api_key: az-key, api_base: "{base}", api_version: "2024-02-01"}}
    model_info: {{base_model: dall-e-3}}
  - model_name: whisper
    litellm_params: {{model: openai/whisper-1, api_key: sk-up, api_base: "{base}/v1"}}
  - model_name: groq-whisper
    litellm_params: {{model: groq/whisper-large-v3, api_key: gsk, api_base: "{base}/v1"}}
  - model_name: azure-whisper
    litellm_params: {{model: azure/whisper, api_key: az-key, api_base: "{base}", api_version: "2024-06-01"}}
    model_info: {{base_model: whisper-1}}
  - model_name: tts
    litellm_params: {{model: openai/tts-1, api_key: sk-up, api_base: "{base}/v1"}}
  - model_name: azure-tts
    litellm_params: {{model: azure/tts, api_key: az-key, api_base: "{base}", api_version: "2024-06-01"}}
    model_info: {{base_model: tts-1-hd}}
  - model_name: chat
    litellm_params: {{model: openai/gpt-4o, api_key: sk-up, mock_response: "hi"}}
  - model_name: mock-media
    litellm_params: {{model: openai/dall-e-2, api_key: sk-up, mock_response: "https://mock.example/a.png"}}
"#
    )
}

#[tokio::test]
async fn image_generation_is_charged_per_image() {
    let (base, log) = upstream().await;
    let app = gateway(&config(&base)).await;
    let key = new_key(&app, json!({"max_budget": 1.0})).await;
    let r = post_json(
        &app,
        "/v1/images/generations",
        &key,
        json!({"model": "dalle", "prompt": "a cat", "n": 2, "size": "1024x1024", "quality": "hd", "metadata": {"x": 1}}),
    )
    .await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    let v = r.json();
    assert_eq!(v["data"].as_array().unwrap().len(), 2);
    assert_eq!(v["data"][0]["url"], "https://img.example/0.png");
    assert_eq!(v["data"][0]["revised_prompt"], "revised");
    // 2 hd 1024x1024 images at $0.08: 667 units of $0.00012 each.
    assert!(close(r.cost(), 2.0 * 667.0 * 0.00012), "{}", r.cost());
    let (spend, reserved) = key_spend(&app, &key).await;
    assert!(close(spend, r.cost()));
    assert_eq!(reserved, 0.0);
    let seen = log.lock().unwrap()[0].clone();
    assert_eq!(seen.path, "/v1/images/generations");
    assert_eq!(seen.headers["authorization"], "Bearer sk-up");
    assert_eq!(seen.body, json!({"model": "dall-e-3", "prompt": "a cat", "n": 2, "size": "1024x1024", "quality": "hd"}));
}

#[tokio::test]
async fn image_budgets_reserve_the_requested_variant() {
    let (base, _log) = upstream().await;
    let app = gateway(&config(&base)).await;
    // $0.10 covers one standard image ($0.04) but not an hd wide one ($0.12).
    let key = new_key(&app, json!({"max_budget": 0.1})).await;
    let wide = json!({"model": "dalle", "prompt": "x", "size": "1792x1024", "quality": "hd"});
    let r = post_json(&app, "/v1/images/generations", &key, wide).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(r.json()["error"]["type"], "budget_exceeded");
    let r = post_json(&app, "/images/generations", &key, json!({"model": "dalle", "prompt": "x"})).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    assert!(close(r.cost(), 334.0 * 0.00012));
    assert!(close(key_spend(&app, &key).await.0, r.cost()));
}

#[tokio::test]
async fn gpt_image_is_charged_its_token_usage() {
    let (base, log) = upstream().await;
    let app = gateway(&config(&base)).await;
    let key = new_key(&app, json!({})).await;
    let r = post_json(
        &app,
        "/v1/images/generations",
        &key,
        json!({"model": "gpt-image", "prompt": "a cat", "response_format": "b64_json", "quality": "high"}),
    )
    .await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    assert_eq!(r.json()["data"][0]["b64_json"], "QUJD");
    assert_eq!(r.json()["usage"]["output_tokens"], 4160);
    // 12 text tokens at $5/M and 4160 image tokens at $40/M.
    assert!(close(r.cost(), 12.0 * 5e-6 + 4160.0 * 4e-5), "{}", r.cost());
    // gpt-image takes no response_format.
    assert!(log.lock().unwrap()[0].body.get("response_format").is_none());
}

#[tokio::test]
async fn azure_images_use_the_deployment_url() {
    let (base, log) = upstream().await;
    let app = gateway(&config(&base)).await;
    let r = post_json(&app, "/v1/images/generations", MASTER, json!({"model": "azure-dalle", "prompt": "x", "quality": "standard"})).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    let seen = log.lock().unwrap()[0].clone();
    assert_eq!(seen.path, "/openai/deployments/my-dalle/images/generations");
    assert_eq!(seen.query.as_deref(), Some("api-version=2024-02-01"));
    assert_eq!(seen.headers["api-key"], "az-key");
    // Azure's per-pixel price for standard 1024x1024 (~$0.044), in units of
    // a thousandth of the hd 1792x1024 price.
    let cost = r.cost();
    assert!((4.19617e-08 * 1024.0 * 1024.0..0.0442).contains(&cost), "{cost}");
    // Azure's own path shape on the gateway works too.
    let r = post_json(&app, "/openai/deployments/azure-dalle/images/generations", MASTER, json!({"prompt": "x"})).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
}

#[tokio::test]
async fn image_edits_forward_the_upload() {
    let (base, log) = upstream().await;
    let app = gateway(&config(&base)).await;
    let key = new_key(&app, json!({})).await;
    let mut form = Form::new();
    form.text("model", "gpt-image")
        .text("prompt", "add a hat")
        .file("image[]", "a.png", Some("image/png"), &[1u8; 100])
        .file("image[]", "b.png", Some("image/png"), &[2u8; 50])
        .file("mask", "m.png", Some("image/png"), &[3u8; 10])
        .text("size", "1024x1024");
    let r = post_form(&app, "/v1/images/edits", &key, form).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    assert_eq!(r.json()["data"][0]["url"], "https://img.example/edit.png");
    let seen = log.lock().unwrap()[0].clone();
    assert_eq!(seen.path, "/v1/images/edits");
    assert_eq!(seen.headers["authorization"], "Bearer sk-up");
    assert_eq!(
        seen.body,
        json!({"model": "gpt-image-1", "prompt": "add a hat", "size": "1024x1024",
            "image[]": ["file:a.png:100", "file:b.png:50"], "mask": "file:m.png:10"})
    );
    // No usage reported: priced at the high 1024x1024 variant ($0.167), plus the prompt estimate.
    assert!(close(r.cost(), 0.167 + 3.0 * 5e-6), "{}", r.cost());
    assert!(close(key_spend(&app, &key).await.0, r.cost()));
    // A missing model is a client error.
    let mut form = Form::new();
    form.text("prompt", "x");
    assert_eq!(post_form(&app, "/v1/images/edits", &key, form).await.status, StatusCode::BAD_REQUEST);
}

fn audio_form(model: &str, format: Option<&str>, seconds: f64) -> Form {
    let mut form = Form::new();
    form.text("model", model).file("file", "speech.wav", Some("audio/wav"), &wav(seconds)).text("language", "en");
    if let Some(f) = format {
        form.text("response_format", f);
    }
    form.text("timestamp_granularities[]", "word").text("timestamp_granularities[]", "segment");
    form
}

#[tokio::test]
async fn transcriptions_are_charged_per_second() {
    let (base, log) = upstream().await;
    let app = gateway(&config(&base)).await;
    let key = new_key(&app, json!({"max_budget": 1.0})).await;
    // verbose_json reports 9.5 s: 10 seconds at $0.0001.
    let r = post_form(&app, "/v1/audio/transcriptions", &key, audio_form("whisper", Some("verbose_json"), 10.0)).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    assert_eq!(r.json()["text"], "hello world");
    assert!(close(r.cost(), 0.001), "{}", r.cost());
    let seen = log.lock().unwrap()[0].clone();
    assert_eq!(seen.path, "/v1/audio/transcriptions");
    assert_eq!(seen.body["model"], "whisper-1");
    assert_eq!(seen.body["language"], "en");
    assert_eq!(seen.body["timestamp_granularities[]"], json!(["word", "segment"]));
    assert_eq!(seen.body["file"], format!("file:speech.wav:{}", wav(10.0).len()));
    // Text formats pass through with their content type; the WAV header's 3 s is charged.
    let r = post_form(&app, "/v1/audio/transcriptions", &key, audio_form("whisper", Some("text"), 3.0)).await;
    assert_eq!(r.status, StatusCode::OK);
    assert_eq!(r.headers["content-type"], "text/plain; charset=utf-8");
    assert_eq!(&r.bytes[..], b"hello world\n");
    assert!(close(r.cost(), 0.0003), "{}", r.cost());
    let r = post_form(&app, "/audio/translations", &key, audio_form("whisper", Some("srt"), 4.0)).await;
    assert_eq!(r.status, StatusCode::OK);
    assert_eq!(r.headers["content-type"], "application/x-subrip");
    assert!(String::from_utf8_lossy(&r.bytes).contains("-->"));
    assert_eq!(log.lock().unwrap()[2].path, "/v1/audio/translations");
    let (spend, reserved) = key_spend(&app, &key).await;
    assert!(close(spend, 0.001 + 0.0003 + 0.0004), "{spend}");
    assert_eq!(reserved, 0.0);
}

#[tokio::test]
async fn transcription_budgets_and_providers() {
    let (base, log) = upstream().await;
    let app = gateway(&config(&base)).await;
    // 60 s of audio at $0.0001/s is $0.006: more than this key has.
    let poor = new_key(&app, json!({"max_budget": 0.005})).await;
    let r = post_form(&app, "/v1/audio/transcriptions", &poor, audio_form("whisper", None, 60.0)).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST, "{}", r.json());
    assert_eq!(r.json()["error"]["type"], "budget_exceeded");
    assert!(log.lock().unwrap().is_empty());
    // Groq, OpenAI-compatible: json without a duration charges the WAV's 20 s at $3.083e-5.
    let r = post_form(&app, "/v1/audio/transcriptions", MASTER, audio_form("groq-whisper", None, 20.0)).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    assert_eq!(r.json(), json!({"text": "hello world"}));
    assert!(close(r.cost(), 20.0 * 30_830e-9), "{}", r.cost());
    let seen = log.lock().unwrap()[0].clone();
    assert_eq!(seen.headers["authorization"], "Bearer gsk");
    assert_eq!(seen.body["model"], "whisper-large-v3");
    // Azure's URL shape.
    let r = post_form(&app, "/v1/audio/transcriptions", MASTER, audio_form("azure-whisper", Some("verbose_json"), 2.0)).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    let seen = log.lock().unwrap()[1].clone();
    assert_eq!(seen.path, "/openai/deployments/whisper/audio/transcriptions");
    assert_eq!(seen.query.as_deref(), Some("api-version=2024-06-01"));
    assert_eq!(seen.headers["api-key"], "az-key");
    // No file is a client error; so is streaming.
    let mut form = Form::new();
    form.text("model", "whisper");
    assert_eq!(post_form(&app, "/v1/audio/transcriptions", MASTER, form).await.status, StatusCode::BAD_REQUEST);
    let mut form = audio_form("whisper", None, 1.0);
    form.text("stream", "true");
    assert_eq!(post_form(&app, "/v1/audio/transcriptions", MASTER, form).await.status, StatusCode::BAD_REQUEST);
}

#[tokio::test]
async fn speech_streams_audio_and_charges_characters() {
    let (base, log) = upstream().await;
    let app = gateway(&config(&base)).await;
    let key = new_key(&app, json!({"max_budget": 1.0})).await;
    let input = "Hello there, world!";
    let r = post_json(&app, "/v1/audio/speech", &key, json!({"model": "tts", "input": input, "voice": "alloy", "speed": 1.25})).await;
    assert_eq!(r.status, StatusCode::OK);
    assert_eq!(r.headers["content-type"], "audio/mpeg");
    assert_eq!(&r.bytes[..], b"ID3fake-mp3-audio");
    assert!(close(r.cost(), input.len() as f64 * 1.5e-5), "{}", r.cost());
    assert!(close(key_spend(&app, &key).await.0, r.cost()));
    let seen = log.lock().unwrap()[0].clone();
    assert_eq!(seen.body, json!({"model": "tts-1", "input": input, "voice": "alloy", "speed": 1.25}));
    // Azure, at the base model's (tts-1-hd) price.
    let r = post_json(&app, "/v1/audio/speech", MASTER, json!({"model": "azure-tts", "input": "abc", "voice": "nova"})).await;
    assert_eq!(r.status, StatusCode::OK);
    assert!(close(r.cost(), 3.0 * 3e-5), "{}", r.cost());
    assert_eq!(log.lock().unwrap()[1].path, "/openai/deployments/tts/audio/speech");
    // A budget too small for the input is refused before the call.
    let poor = new_key(&app, json!({"max_budget": 0.0001})).await;
    let r = post_json(&app, "/v1/audio/speech", &poor, json!({"model": "tts", "input": "x".repeat(100), "voice": "alloy"})).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(log.lock().unwrap().len(), 2);
}

#[tokio::test]
async fn mock_responses_and_wrong_modes() {
    let (base, log) = upstream().await;
    let app = gateway(&config(&base)).await;
    let key = new_key(&app, json!({})).await;
    // A deployment-level mock answers without a network call, still charged per image.
    let r = post_json(&app, "/v1/images/generations", &key, json!({"model": "mock-media", "prompt": "x", "n": 2})).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.json());
    assert_eq!(r.json()["data"][1]["url"], "https://mock.example/a.png");
    assert!(close(r.cost(), 2.0 * 0.02), "{}", r.cost());
    // Request-level mocks, and LiteLLM's error triggers.
    let r =
        post_json(&app, "/v1/images/generations", &key, json!({"model": "dalle", "prompt": "x", "mock_response": "https://m/x.png"})).await;
    assert_eq!(r.json()["data"][0]["url"], "https://m/x.png");
    let r = post_json(
        &app,
        "/v1/images/generations",
        &key,
        json!({"model": "dalle", "prompt": "x", "mock_response": "litellm.RateLimitError"}),
    )
    .await;
    assert_eq!(r.status, StatusCode::TOO_MANY_REQUESTS);
    let mut form = audio_form("whisper", Some("text"), 1.0);
    form.text("mock_response", "mocked words");
    let r = post_form(&app, "/v1/audio/transcriptions", &key, form).await;
    assert_eq!(&r.bytes[..], b"mocked words");
    assert!(close(r.cost(), 0.0001));
    let r = post_json(&app, "/v1/audio/speech", &key, json!({"model": "tts", "input": "hi", "voice": "alloy", "mock_response": "x"})).await;
    assert_eq!(r.headers["content-type"], "audio/wav");
    assert!(r.bytes.starts_with(b"RIFF"));
    assert!(log.lock().unwrap().is_empty());
    // A chat model does not serve media endpoints, and is not charged for trying.
    let before = key_spend(&app, &key).await.0;
    let r = post_json(&app, "/v1/images/generations", &key, json!({"model": "chat", "prompt": "x"})).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST, "{}", r.json());
    assert!(r.json()["error"]["message"].as_str().unwrap().contains("does not support /v1/images/generations"));
    let r = post_json(&app, "/v1/audio/speech", &key, json!({"model": "whisper", "input": "x", "voice": "alloy"})).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(key_spend(&app, &key).await, (before, 0.0));
    // Unknown models and keys are refused by the kernel as usual.
    let r = post_json(&app, "/v1/images/generations", &key, json!({"model": "nope", "prompt": "x"})).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    let r = post_json(&app, "/v1/audio/speech", "sk-bad", json!({"model": "tts", "input": "x"})).await;
    assert_eq!(r.status, StatusCode::UNAUTHORIZED);
}
