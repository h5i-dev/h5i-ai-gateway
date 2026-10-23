//! Guardrails and caching end to end through the router, with the in-memory
//! executor and a local OpenAI-compatible upstream that records what it is
//! sent and counts its calls.
//!
//! The Redis test runs when `H5I_GATEWAY_TEST_REDIS_URL` is set, e.g.
//! `docker run -d --rm -p 127.0.0.1:56379:6379 redis:7` and
//! `H5I_GATEWAY_TEST_REDIS_URL=redis://127.0.0.1:56379/`.

use axum::Router;
use axum::body::Body;
use axum::http::{HeaderMap, Request, StatusCode};
use axum::response::IntoResponse;
use axum::routing::post;
use gateway_server::cache::Cache;
use gateway_server::config::Config;
use gateway_server::guardrails::Guardrails;
use gateway_server::kernel::{Backend, MemoryExecutor};
use gateway_server::registry::Registry;
use gateway_server::{AppState, ProxySettings, auth::GatewayAuth, router, sync};
use http_body_util::BodyExt;
use serde_json::{Value, json};
use std::sync::{Arc, Mutex};
use std::time::Duration;
use tower::ServiceExt;

const MASTER: &str = "sk-master";

/// What the upstream saw.
#[derive(Clone, Default)]
struct Upstream {
    url: String,
    bodies: Arc<Mutex<Vec<Value>>>,
}

impl Upstream {
    fn chats(&self) -> usize {
        self.bodies
            .lock()
            .unwrap()
            .iter()
            .filter(|b| b.get("messages").is_some())
            .count()
    }
    fn embeddings(&self) -> usize {
        self.bodies
            .lock()
            .unwrap()
            .iter()
            .filter(|b| b.get("input").is_some())
            .count()
    }
    fn last(&self) -> Value {
        self.bodies.lock().unwrap().last().cloned().unwrap()
    }
}

fn last_user_text(b: &Value) -> String {
    b["messages"]
        .as_array()
        .unwrap()
        .iter()
        .rev()
        .find(|m| m["role"] == "user")
        .and_then(|m| m["content"].as_str())
        .unwrap_or_default()
        .to_string()
}

/// An OpenAI-compatible upstream answering `echo: <last user message>`.
async fn upstream() -> Upstream {
    let up = Upstream::default();
    let bodies = up.bodies.clone();
    let chat = move |Json(b): axum::Json<Value>| {
        let bodies = bodies.clone();
        async move {
            bodies.lock().unwrap().push(b.clone());
            let text = format!("echo: {}", last_user_text(&b));
            let usage = json!({"prompt_tokens": 5, "completion_tokens": 3, "total_tokens": 8});
            if b["stream"] == true {
                // The answer in two pieces, split mid-word.
                let mid = text.char_indices().nth(text.chars().count() / 2).unwrap().0;
                let chunk = |delta: Value, finish: Value, usage: Value| {
                    let choices = if delta.is_null() {
                        json!([])
                    } else {
                        json!([{"index": 0, "delta": delta, "finish_reason": finish}])
                    };
                    format!(
                        "data: {}\n\n",
                        json!({"id": "c1", "object": "chat.completion.chunk", "created": 1, "model": "gpt-4o", "choices": choices, "usage": usage})
                    )
                };
                let body = [
                    chunk(
                        json!({"role": "assistant", "content": &text[..mid]}),
                        Value::Null,
                        Value::Null,
                    ),
                    chunk(json!({"content": &text[mid..]}), Value::Null, Value::Null),
                    chunk(json!({}), json!("stop"), Value::Null),
                    chunk(Value::Null, Value::Null, usage),
                    "data: [DONE]\n\n".to_string(),
                ]
                .concat();
                return ([("content-type", "text/event-stream")], body).into_response();
            }
            axum::Json(json!({
                "id": "c1", "object": "chat.completion", "created": 1, "model": "gpt-4o",
                "choices": [{"index": 0, "message": {"role": "assistant", "content": text}, "finish_reason": "stop"}],
                "usage": usage,
            }))
            .into_response()
        }
    };
    let bodies = up.bodies.clone();
    let embed = move |Json(b): axum::Json<Value>| {
        let bodies = bodies.clone();
        async move {
            bodies.lock().unwrap().push(b.clone());
            axum::Json(
                json!({"object": "list", "model": "text-embedding-3-small", "data": [{"object": "embedding", "index": 0, "embedding": [0.1, 0.2]}], "usage": {"prompt_tokens": 2, "total_tokens": 2}}),
            )
        }
    };
    let app = Router::new()
        .route("/v1/chat/completions", post(chat))
        .route("/v1/embeddings", post(embed));
    Upstream {
        url: serve(app).await,
        ..up
    }
}

use axum::Json;

async fn serve(app: Router) -> String {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
    format!("http://{addr}")
}

fn models(up: &Upstream) -> String {
    format!(
        r#"
model_list:
  - model_name: gpt
    litellm_params: {{model: openai/gpt-4o, api_key: fake, api_base: "{0}/v1", input_cost_per_token: 0.000001, output_cost_per_token: 0.000002}}
  - model_name: other
    litellm_params: {{model: openai/gpt-4o, api_key: fake, api_base: "{0}/v1", input_cost_per_token: 0.000001, output_cost_per_token: 0.000002}}
  - model_name: embed
    litellm_params: {{model: openai/text-embedding-3-small, api_key: fake, api_base: "{0}/v1", input_cost_per_token: 0.000001, output_cost_per_token: 0}}
"#,
        up.url
    )
}

async fn gateway(yaml: &str) -> Router {
    let config = Config::parse(yaml).unwrap();
    let env = |_: &str| None;
    let ls = &config.litellm_settings;
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
        guardrails: Arc::new(Guardrails::from_config(&config.guardrails, &env).unwrap()),
        cache: Cache::from_settings(ls.cache, &ls.cache_params, &env)
            .await
            .unwrap()
            .map(Arc::new),
    };
    sync(&state, &config).await.unwrap();
    router(state)
}

async fn call(
    app: &Router,
    method: &str,
    path: &str,
    key: &str,
    body: Option<Value>,
) -> (StatusCode, HeaderMap, Value) {
    let mut req = Request::builder()
        .method(method)
        .uri(path)
        .header("authorization", format!("Bearer {key}"));
    let body = match body {
        Some(b) => {
            req = req.header("content-type", "application/json");
            Body::from(b.to_string())
        }
        None => Body::empty(),
    };
    let resp = app.clone().oneshot(req.body(body).unwrap()).await.unwrap();
    let status = resp.status();
    let headers = resp.headers().clone();
    let bytes = resp.into_body().collect().await.unwrap().to_bytes();
    let v = serde_json::from_slice(&bytes)
        .unwrap_or_else(|_| Value::String(String::from_utf8_lossy(&bytes).into()));
    (status, headers, v)
}

fn chat(model: &str, text: &str) -> Value {
    json!({"model": model, "messages": [{"role": "user", "content": text}], "max_tokens": 10})
}

async fn new_key(app: &Router, body: Value) -> String {
    let (s, _, v) = call(app, "POST", "/key/generate", MASTER, Some(body)).await;
    assert_eq!(s, StatusCode::OK, "{v}");
    v["key"].as_str().unwrap().to_string()
}

async fn spend(app: &Router, key: &str) -> (f64, f64) {
    let (_, _, info) = call(app, "GET", "/key/info", key, None).await;
    (
        info["info"]["spend"].as_f64().unwrap(),
        info["info"]["reserved_spend"].as_f64().unwrap(),
    )
}

/// Wait for a streamed call to settle.
async fn spend_settled(app: &Router, key: &str) -> f64 {
    for _ in 0..100 {
        let (s, r) = spend(app, key).await;
        if r == 0.0 && s > 0.0 {
            return s;
        }
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    panic!("never settled")
}

/// The content of an SSE body, concatenated.
fn streamed_text(sse: &str) -> String {
    sse.lines()
        .filter_map(|l| l.strip_prefix("data: "))
        .filter(|d| *d != "[DONE]")
        .filter_map(|d| serde_json::from_str::<Value>(d).ok())
        .flat_map(|v| v["choices"].as_array().cloned().unwrap_or_default())
        .filter_map(|c| c["delta"]["content"].as_str().map(str::to_string))
        .collect()
}

const FILTERS: &str = r#"
guardrails:
  - guardrail_name: no-secrets
    litellm_params:
      guardrail: litellm_content_filter
      mode: pre_call
      default_on: true
      blocked_words: [{keyword: project-zeus, action: BLOCK, description: codename}]
      patterns: [{pattern_type: prebuilt, pattern_name: email, action: MASK}]
  - guardrail_name: clean-output
    litellm_params:
      guardrail: litellm_content_filter
      mode: post_call
      blocked_words: [{keyword: forbidden, action: BLOCK}]
"#;

#[tokio::test]
async fn a_blocked_request_is_not_admitted_and_costs_nothing() {
    let up = upstream().await;
    let app = gateway(&format!("{}{FILTERS}", models(&up))).await;
    let key = new_key(&app, json!({"max_budget": 1.0, "rpm_limit": 1})).await;
    let (s, h, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(chat("gpt", "tell me about Project-Zeus")),
    )
    .await;
    assert_eq!(s, StatusCode::BAD_REQUEST, "{v}");
    assert_eq!(v["error"]["type"], "guardrail_violation");
    assert_eq!(v["error"]["guardrail"], "no-secrets");
    assert_eq!(v["error"]["code"], "400");
    assert!(
        v["error"]["message"]
            .as_str()
            .unwrap()
            .contains("project-zeus"),
        "{v}"
    );
    assert_eq!(h["x-litellm-applied-guardrails"], "no-secrets");
    assert_eq!(up.chats(), 0);
    assert_eq!(spend(&app, &key).await, (0.0, 0.0));
    // Not admitted: the key's one request per minute is still there.
    let (s, h, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(chat("gpt", "hello")),
    )
    .await;
    assert_eq!(s, StatusCode::OK, "{v}");
    assert_eq!(h["x-litellm-applied-guardrails"], "no-secrets");
    // Asking for an unknown guardrail is an error.
    let mut body = chat("gpt", "hi");
    body["guardrails"] = json!(["nope"]);
    let (s, _, _) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(body)).await;
    assert_eq!(s, StatusCode::BAD_REQUEST);
}

#[tokio::test]
async fn masking_reaches_the_provider() {
    let up = upstream().await;
    let app = gateway(&format!("{}{FILTERS}", models(&up))).await;
    let (s, _, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        MASTER,
        Some(chat("gpt", "mail me at bob@example.com")),
    )
    .await;
    assert_eq!(s, StatusCode::OK, "{v}");
    assert_eq!(last_user_text(&up.last()), "mail me at [EMAIL_REDACTED]");
    assert_eq!(
        v["choices"][0]["message"]["content"],
        "echo: mail me at [EMAIL_REDACTED]"
    );
    // Gateway-only fields never reach the provider.
    let mut body = chat("gpt", "hi");
    body["guardrails"] = json!(["clean-output"]);
    call(&app, "POST", "/v1/chat/completions", MASTER, Some(body)).await;
    assert!(up.last().get("guardrails").is_none());
    // Embedding inputs are masked too.
    let (s, h, v) = call(
        &app,
        "POST",
        "/v1/embeddings",
        MASTER,
        Some(json!({"model": "embed", "input": ["a@b.io", "plain"]})),
    )
    .await;
    assert_eq!(s, StatusCode::OK, "{v}");
    assert_eq!(up.last()["input"], json!(["[EMAIL_REDACTED]", "plain"]));
    assert_eq!(h["x-litellm-applied-guardrails"], "no-secrets");
}

#[tokio::test]
async fn post_call_blocks_the_response_but_the_call_is_charged() {
    let up = upstream().await;
    let app = gateway(&format!("{}{FILTERS}", models(&up))).await;
    let key = new_key(&app, json!({"max_budget": 1.0})).await;
    let mut body = chat("gpt", "say forbidden");
    body["metadata"] = json!({"guardrails": ["clean-output"]});
    let (s, h, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(body.clone()),
    )
    .await;
    assert_eq!(s, StatusCode::BAD_REQUEST, "{v}");
    assert_eq!(v["error"]["guardrail"], "clean-output");
    assert_eq!(h["x-litellm-applied-guardrails"], "no-secrets,clean-output");
    assert_eq!(up.chats(), 1);
    let (spent, reserved) = spend(&app, &key).await;
    assert!(spent > 0.0 && reserved == 0.0);
    // Streaming: the text has gone out; the stream ends with the error.
    body["stream"] = json!(true);
    let (s, h, v) = call(&app, "POST", "/v1/chat/completions", &key, Some(body)).await;
    assert_eq!(s, StatusCode::OK);
    assert_eq!(h["x-litellm-applied-guardrails"], "no-secrets,clean-output");
    let text = v.as_str().unwrap();
    assert_eq!(streamed_text(text), "echo: say forbidden");
    assert!(text.contains("\"guardrail_violation\""), "{text}");
    assert!(text.contains("clean-output"), "{text}");
    assert!(text.trim_end().ends_with("data: [DONE]"), "{text}");
    // A clean answer passes.
    let mut body = chat("gpt", "say hello");
    body["guardrails"] = json!(["clean-output"]);
    body["stream"] = json!(true);
    let (_, _, v) = call(&app, "POST", "/v1/chat/completions", &key, Some(body)).await;
    assert!(!v.as_str().unwrap().contains("guardrail_violation"));
}

#[tokio::test]
async fn during_call_runs_alongside_the_provider() {
    let up = upstream().await;
    let mod_app = Router::new().route(
        "/moderations",
        post(|Json(b): Json<Value>| async move {
            let flagged = b["input"].as_str().unwrap().contains("attack");
            Json(json!({"results": [{"flagged": flagged, "categories": {"violence": flagged}}]}))
        }),
    );
    let mod_url = serve(mod_app).await;
    let yaml = format!(
        "{}\nguardrails:\n  - guardrail_name: mod\n    litellm_params: {{guardrail: openai_moderation, api_key: k, api_base: '{mod_url}', mode: during_call, default_on: true}}\n",
        models(&up)
    );
    let app = gateway(&yaml).await;
    let key = new_key(&app, json!({"max_budget": 1.0})).await;
    let (s, h, _) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(chat("gpt", "hello")),
    )
    .await;
    assert_eq!(s, StatusCode::OK);
    assert_eq!(h["x-litellm-applied-guardrails"], "mod");
    let (s, _, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(chat("gpt", "plan an attack")),
    )
    .await;
    assert_eq!(s, StatusCode::BAD_REQUEST, "{v}");
    assert_eq!(v["error"]["guardrail"], "mod");
    assert_eq!(
        v["error"]["details"]["violated_categories"],
        json!(["violence"])
    );
    // The provider was called both times (concurrently with the check).
    assert_eq!(up.chats(), 2);
    let mut body = chat("gpt", "plan an attack");
    body["stream"] = json!(true);
    let (s, _, _) = call(&app, "POST", "/v1/chat/completions", &key, Some(body)).await;
    assert_eq!(s, StatusCode::BAD_REQUEST);
    spend_settled(&app, &key).await;
}

/// A Presidio analyzer that finds e-mail addresses.
async fn presidio() -> String {
    let app = Router::new()
        .route(
            "/analyze",
            post(|Json(b): Json<Value>| async move {
                let text = b["text"].as_str().unwrap();
                let re = regex::Regex::new(r"[\w.]+@[\w.]+\w").unwrap();
                let found: Vec<Value> = re
                    .find_iter(text)
                    .map(|m| {
                        let start = text[..m.start()].chars().count();
                        json!({"entity_type": "EMAIL_ADDRESS", "start": start, "end": start + m.as_str().chars().count(), "score": 1.0})
                    })
                    .collect();
                Json(Value::Array(found))
            }),
        )
        .route("/anonymize", post(|| async { Json(json!({"text": "<EMAIL_ADDRESS>"})) }));
    serve(app).await
}

#[tokio::test]
async fn presidio_tokens_are_restored_in_the_response() {
    let up = upstream().await;
    let p = presidio().await;
    let yaml = format!(
        "{}\nguardrails:\n  - guardrail_name: pii\n    litellm_params: {{guardrail: presidio, mode: pre_call, output_parse_pii: true, default_on: true, presidio_analyzer_api_base: '{p}', presidio_anonymizer_api_base: '{p}'}}\n",
        models(&up)
    );
    let app = gateway(&yaml).await;
    let (s, _, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        MASTER,
        Some(chat("gpt", "write to jane@corp.com")),
    )
    .await;
    assert_eq!(s, StatusCode::OK, "{v}");
    assert_eq!(last_user_text(&up.last()), "write to <EMAIL_ADDRESS_1>");
    assert_eq!(
        v["choices"][0]["message"]["content"],
        "echo: write to jane@corp.com"
    );
    // Streamed, with the token split across chunks by the upstream.
    let mut body = chat("gpt", "to jane@corp.com");
    body["stream"] = json!(true);
    let (_, _, v) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(body)).await;
    assert_eq!(streamed_text(v.as_str().unwrap()), "echo: to jane@corp.com");
}

const CACHE: &str = r#"
litellm_settings:
  cache: true
  cache_params: {type: local, ttl: 60}
"#;

#[tokio::test]
async fn cache_hits_skip_the_provider_but_not_the_kernel() {
    let up = upstream().await;
    let app = gateway(&format!("{}{CACHE}", models(&up))).await;
    let key = new_key(
        &app,
        json!({"models": ["gpt"], "max_budget": 1.0, "rpm_limit": 2}),
    )
    .await;
    let (s, h1, v1) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(chat("gpt", "cache me")),
    )
    .await;
    assert_eq!(s, StatusCode::OK, "{v1}");
    assert_eq!(h1["x-litellm-cache-hit"], "false");
    let spent = spend(&app, &key).await.0;
    assert!(spent > 0.0);
    // Same request (different `user`, field order): a hit, free, no upstream call.
    let mut again = chat("gpt", "cache me");
    again["user"] = json!("someone");
    let (s, h2, v2) = call(&app, "POST", "/v1/chat/completions", &key, Some(again)).await;
    assert_eq!(s, StatusCode::OK, "{v2}");
    assert_eq!(h2["x-litellm-cache-hit"], "true");
    assert_eq!(h2["x-litellm-cache-key"], h1["x-litellm-cache-key"]);
    assert_eq!(h2["x-litellm-response-cost"], "0");
    assert_eq!(v2, v1);
    assert_eq!(up.chats(), 1);
    assert_eq!(spend(&app, &key).await, (spent, 0.0));
    // A hit still counts against the key's rate limit…
    let (s, _, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(chat("gpt", "cache me")),
    )
    .await;
    assert_eq!(s, StatusCode::TOO_MANY_REQUESTS, "{v}");
    // …and needs access to the model.
    let other = new_key(&app, json!({"models": ["other"]})).await;
    let (s, _, _) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &other,
        Some(chat("gpt", "cache me")),
    )
    .await;
    assert_eq!(s, StatusCode::UNAUTHORIZED);
    let blocked = new_key(&app, json!({})).await;
    call(
        &app,
        "POST",
        "/key/block",
        MASTER,
        Some(json!({"key": blocked})),
    )
    .await;
    let (s, _, _) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &blocked,
        Some(chat("gpt", "cache me")),
    )
    .await;
    assert_eq!(s, StatusCode::UNAUTHORIZED);
    // Another model group, another entry.
    let (_, h, _) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        MASTER,
        Some(chat("other", "cache me")),
    )
    .await;
    assert_eq!(h["x-litellm-cache-hit"], "false");
    assert_eq!(up.chats(), 2);
    // Controls: no-cache reads past the cache, no-store does not write.
    let mut body = chat("gpt", "cache me");
    body["cache"] = json!({"no-cache": true});
    let (_, h, _) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(body)).await;
    assert_eq!(h["x-litellm-cache-hit"], "false");
    assert_eq!(up.chats(), 3);
    let mut body = chat("gpt", "do not keep");
    body["cache"] = json!({"no-store": true});
    call(
        &app,
        "POST",
        "/v1/chat/completions",
        MASTER,
        Some(body.clone()),
    )
    .await;
    body["cache"] = json!({});
    let (_, h, _) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(body)).await;
    assert_eq!(h["x-litellm-cache-hit"], "false");
    assert_eq!(up.chats(), 5);
    // An entry older than s-maxage is not served.
    let mut body = chat("gpt", "cache me");
    body["cache"] = json!({"s-maxage": -1});
    let (_, h, _) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(body)).await;
    assert_eq!(h["x-litellm-cache-hit"], "false");
}

#[tokio::test]
async fn cached_answers_replay_as_streams() {
    let up = upstream().await;
    let app = gateway(&format!("{}{CACHE}", models(&up))).await;
    let key = new_key(&app, json!({})).await;
    // A streamed miss is stored when the stream ends.
    let mut body = chat("gpt", "stream me");
    body["stream"] = json!(true);
    let (_, h, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(body.clone()),
    )
    .await;
    assert_eq!(h["x-litellm-cache-hit"], "false");
    assert_eq!(streamed_text(v.as_str().unwrap()), "echo: stream me");
    spend_settled(&app, &key).await;
    // Served whole from the stored stream.
    let (s, h, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(chat("gpt", "stream me")),
    )
    .await;
    assert_eq!(s, StatusCode::OK, "{v}");
    assert_eq!(h["x-litellm-cache-hit"], "true");
    assert_eq!(v["choices"][0]["message"]["content"], "echo: stream me");
    assert_eq!(v["choices"][0]["finish_reason"], "stop");
    assert_eq!(v["usage"]["total_tokens"], 8);
    // And replayed as a stream, with usage only when asked for.
    body["stream_options"] = json!({"include_usage": true});
    let (s, h, v) = call(&app, "POST", "/v1/chat/completions", &key, Some(body)).await;
    assert_eq!(s, StatusCode::OK);
    assert_eq!(h["x-litellm-cache-hit"], "true");
    assert_eq!(h["content-type"], "text/event-stream");
    let text = v.as_str().unwrap();
    assert_eq!(streamed_text(text), "echo: stream me");
    assert!(text.contains("\"finish_reason\":\"stop\""), "{text}");
    assert!(text.contains("\"total_tokens\":8"), "{text}");
    assert!(text.trim_end().ends_with("data: [DONE]"));
    assert_eq!(up.chats(), 1);
}

#[tokio::test]
async fn embeddings_are_cached() {
    let up = upstream().await;
    let app = gateway(&format!("{}{CACHE}", models(&up))).await;
    let body = json!({"model": "embed", "input": "vectorise me"});
    let (_, h1, v1) = call(&app, "POST", "/v1/embeddings", MASTER, Some(body.clone())).await;
    let (_, h2, v2) = call(&app, "POST", "/v1/embeddings", MASTER, Some(body)).await;
    assert_eq!(
        (
            h1["x-litellm-cache-hit"].to_str().unwrap(),
            h2["x-litellm-cache-hit"].to_str().unwrap()
        ),
        ("false", "true")
    );
    assert_eq!(v1, v2);
    assert_eq!(up.embeddings(), 1);
    let (_, h, _) = call(
        &app,
        "POST",
        "/v1/embeddings",
        MASTER,
        Some(json!({"model": "embed", "input": "vectorise me", "dimensions": 2})),
    )
    .await;
    assert_eq!(h["x-litellm-cache-hit"], "false");
}

#[tokio::test]
async fn guardrails_apply_to_cache_hits() {
    let up = upstream().await;
    let app = gateway(&format!("{}{CACHE}{FILTERS}", models(&up))).await;
    // Masked before the key is computed: two addresses, one entry.
    let (_, h1, _) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        MASTER,
        Some(chat("gpt", "to a@x.io")),
    )
    .await;
    let (_, h2, v) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        MASTER,
        Some(chat("gpt", "to b@y.io")),
    )
    .await;
    assert_eq!(h2["x-litellm-cache-hit"], "true");
    assert_eq!(h1["x-litellm-cache-key"], h2["x-litellm-cache-key"]);
    assert_eq!(
        v["choices"][0]["message"]["content"],
        "echo: to [EMAIL_REDACTED]"
    );
    // A cached answer is still checked by post_call guardrails.
    let mut body = chat("gpt", "say forbidden");
    call(
        &app,
        "POST",
        "/v1/chat/completions",
        MASTER,
        Some(body.clone()),
    )
    .await;
    body["guardrails"] = json!(["clean-output"]);
    let (s, h, _) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(body)).await;
    assert_eq!(s, StatusCode::BAD_REQUEST);
    assert_eq!(h["x-litellm-applied-guardrails"], "no-secrets,clean-output");
    assert_eq!(up.chats(), 2);
}

#[tokio::test]
async fn redis_cache() {
    let Ok(url) = std::env::var("H5I_GATEWAY_TEST_REDIS_URL") else {
        eprintln!("H5I_GATEWAY_TEST_REDIS_URL not set; skipping");
        return;
    };
    let up = upstream().await;
    let ns = format!("test-{}", std::process::id());
    let yaml = format!(
        "{}\nlitellm_settings:\n  cache: true\n  cache_params: {{type: redis, url: '{url}', ttl: 30, namespace: '{ns}'}}\n",
        models(&up)
    );
    let app = gateway(&yaml).await;
    let key = new_key(&app, json!({"rpm_limit": 2})).await;
    let text = format!("redis {}", uuid::Uuid::new_v4());
    let (_, h1, v1) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(chat("gpt", &text)),
    )
    .await;
    assert_eq!(h1["x-litellm-cache-hit"], "false");
    assert!(
        h1["x-litellm-cache-key"]
            .to_str()
            .unwrap()
            .starts_with(&format!("{ns}:"))
    );
    let (_, h2, v2) = call(
        &app,
        "POST",
        "/v1/chat/completions",
        &key,
        Some(chat("gpt", &text)),
    )
    .await;
    assert_eq!(h2["x-litellm-cache-hit"], "true");
    assert_eq!(v1, v2);
    assert_eq!(up.chats(), 1);
    // The kernel still limits hits.
    assert_eq!(
        call(
            &app,
            "POST",
            "/v1/chat/completions",
            &key,
            Some(chat("gpt", &text))
        )
        .await
        .0,
        StatusCode::TOO_MANY_REQUESTS
    );
    // A second gateway sharing the Redis sees the entry.
    let app2 = gateway(&yaml).await;
    let (_, h3, _) = call(
        &app2,
        "POST",
        "/v1/chat/completions",
        MASTER,
        Some(chat("gpt", &text)),
    )
    .await;
    assert_eq!(h3["x-litellm-cache-hit"], "true");
    // The entry expires with its TTL.
    let mut body = chat("gpt", &format!("{text} short"));
    body["cache"] = json!({"ttl": 1});
    call(
        &app2,
        "POST",
        "/v1/chat/completions",
        MASTER,
        Some(body.clone()),
    )
    .await;
    tokio::time::sleep(Duration::from_millis(1200)).await;
    let (_, h, _) = call(&app2, "POST", "/v1/chat/completions", MASTER, Some(body)).await;
    assert_eq!(h["x-litellm-cache-hit"], "false");
}
