//! End to end through the router, with the in-memory executor and mock or
//! local upstreams: keys, budgets, rate limits, model access, retries,
//! cooldowns, fallbacks and streaming.

use axum::Router;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use gateway_server::config::Config;
use gateway_server::kernel::{Backend, MemoryExecutor};
use gateway_server::registry::Registry;
use gateway_server::{AppState, ProxySettings, auth::GatewayAuth, router, sync};
use http_body_util::BodyExt;
use serde_json::{Value, json};
use std::sync::Arc;
use std::time::Duration;
use tower::ServiceExt;

const MASTER: &str = "sk-master";

/// A local upstream that always answers 500.
async fn failing_upstream() -> String {
    let app = Router::new().fallback(|| async { (StatusCode::INTERNAL_SERVER_ERROR, "{\"error\":{\"message\":\"boom\"}}") });
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
    format!("http://{addr}/v1")
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
        guardrails: Default::default(),
        cache: None,
    };
    sync(&state, &config).await.unwrap();
    router(state)
}

async fn call(app: &Router, method: &str, path: &str, key: &str, body: Option<Value>) -> (StatusCode, axum::http::HeaderMap, Value) {
    let mut req = Request::builder().method(method).uri(path).header("authorization", format!("Bearer {key}"));
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
    let v = serde_json::from_slice(&bytes).unwrap_or_else(|_| Value::String(String::from_utf8_lossy(&bytes).into()));
    (status, headers, v)
}

fn chat(model: &str) -> Value {
    json!({"model": model, "messages": [{"role": "user", "content": "Say hi"}], "max_tokens": 10})
}

const MOCKS: &str = r#"
model_list:
  - model_name: gpt
    litellm_params:
      model: openai/gpt-4o
      api_key: fake
      mock_response: "hi there"
      input_cost_per_token: 0.000001
      output_cost_per_token: 0.000002
  - model_name: claude
    litellm_params:
      model: anthropic/claude-3-5-sonnet-20241022
      api_key: fake
      mock_response: "hello"
      input_cost_per_token: 0.000003
      output_cost_per_token: 0.000015
"#;

async fn new_key(app: &Router, body: Value) -> String {
    let (s, _, v) = call(app, "POST", "/key/generate", MASTER, Some(body)).await;
    assert_eq!(s, StatusCode::OK, "{v}");
    v["key"].as_str().unwrap().to_string()
}

#[tokio::test]
async fn a_key_calls_a_model_and_is_charged() {
    let app = gateway(MOCKS).await;
    let key = new_key(&app, json!({"models": ["gpt"], "max_budget": 1.0})).await;
    let (s, h, v) = call(&app, "POST", "/v1/chat/completions", &key, Some(chat("gpt"))).await;
    assert_eq!(s, StatusCode::OK, "{v}");
    assert_eq!(v["choices"][0]["message"]["content"], "hi there");
    let cost: f64 = h["x-litellm-response-cost"].to_str().unwrap().parse().unwrap();
    assert!(cost > 0.0);
    let (_, _, info) = call(&app, "GET", "/key/info", &key, None).await;
    assert_eq!(info["info"]["spend"].as_f64().unwrap(), cost);
    assert_eq!(info["info"]["reserved_spend"].as_f64().unwrap(), 0.0);
    // Not granted "claude".
    let (s, _, _) = call(&app, "POST", "/v1/chat/completions", &key, Some(chat("claude"))).await;
    assert_eq!(s, StatusCode::UNAUTHORIZED);
    let (_, _, models) = call(&app, "GET", "/v1/models", &key, None).await;
    assert_eq!(models["data"].as_array().unwrap().len(), 1);
}

#[tokio::test]
async fn credentials_are_checked() {
    let app = gateway(MOCKS).await;
    let (s, _, _) = call(&app, "POST", "/v1/chat/completions", "sk-nope", Some(chat("gpt"))).await;
    assert_eq!(s, StatusCode::UNAUTHORIZED);
    let resp = app.clone().oneshot(Request::builder().method("GET").uri("/v1/models").body(Body::empty()).unwrap()).await.unwrap();
    assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
    // The master key may call models directly.
    let (s, _, _) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(chat("claude"))).await;
    assert_eq!(s, StatusCode::OK);
}

#[tokio::test]
async fn budgets_and_rate_limits_refuse() {
    let app = gateway(MOCKS).await;
    // A worst case of ~(prompt + 10 completion tokens) at $2/M is far above $1e-9.
    let poor = new_key(&app, json!({"max_budget": 0.000000001})).await;
    let (s, _, v) = call(&app, "POST", "/v1/chat/completions", &poor, Some(chat("gpt"))).await;
    assert_eq!(s, StatusCode::BAD_REQUEST);
    assert_eq!(v["error"]["type"], "budget_exceeded");
    let slow = new_key(&app, json!({"rpm_limit": 1})).await;
    assert_eq!(call(&app, "POST", "/v1/chat/completions", &slow, Some(chat("gpt"))).await.0, StatusCode::OK);
    assert_eq!(call(&app, "POST", "/v1/chat/completions", &slow, Some(chat("gpt"))).await.0, StatusCode::TOO_MANY_REQUESTS);
}

#[tokio::test]
async fn teams_share_a_budget() {
    let app = gateway(MOCKS).await;
    let (s, _, team) = call(&app, "POST", "/team/new", MASTER, Some(json!({"max_budget": 0.000000001, "models": ["gpt"]}))).await;
    assert_eq!(s, StatusCode::OK, "{team}");
    let team_id = team["team_id"].as_str().unwrap().to_string();
    let key = new_key(&app, json!({"team_id": team_id})).await;
    let (s, _, v) = call(&app, "POST", "/v1/chat/completions", &key, Some(chat("gpt"))).await;
    assert_eq!(s, StatusCode::BAD_REQUEST, "{v}");
    assert!(v["error"]["message"].as_str().unwrap().contains("team"));
    // The team cannot be deleted while it has a key.
    let (s, _, _) = call(&app, "POST", "/team/delete", MASTER, Some(json!({"team_ids": [team_id]}))).await;
    assert_eq!(s, StatusCode::CONFLICT);
}

#[tokio::test]
async fn keys_cannot_administer() {
    let app = gateway(MOCKS).await;
    let key = new_key(&app, json!({})).await;
    let (s, _, _) = call(&app, "POST", "/key/generate", &key, Some(json!({}))).await;
    assert_eq!(s, StatusCode::FORBIDDEN);
    let (s, _, _) = call(&app, "GET", "/key/list", &key, None).await;
    assert_eq!(s, StatusCode::FORBIDDEN);
    // An admin key can.
    let admin = new_key(&app, json!({"user_role": "proxy_admin"})).await;
    let (s, _, _) = call(&app, "POST", "/key/generate", &admin, Some(json!({}))).await;
    assert_eq!(s, StatusCode::OK);
}

#[tokio::test]
async fn blocked_and_deleted_keys_stop_working() {
    let app = gateway(MOCKS).await;
    let key = new_key(&app, json!({})).await;
    let (s, _, _) = call(&app, "POST", "/key/block", MASTER, Some(json!({"key": key}))).await;
    assert_eq!(s, StatusCode::OK);
    assert_eq!(call(&app, "POST", "/v1/chat/completions", &key, Some(chat("gpt"))).await.0, StatusCode::UNAUTHORIZED);
    call(&app, "POST", "/key/unblock", MASTER, Some(json!({"key": key}))).await;
    assert_eq!(call(&app, "POST", "/v1/chat/completions", &key, Some(chat("gpt"))).await.0, StatusCode::OK);
    let (s, _, _) = call(&app, "POST", "/key/delete", MASTER, Some(json!({"keys": [key]}))).await;
    assert_eq!(s, StatusCode::OK);
    assert_eq!(call(&app, "POST", "/v1/chat/completions", &key, Some(chat("gpt"))).await.0, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn retries_cool_down_and_fall_back() {
    let bad = failing_upstream().await;
    let yaml = format!(
        r#"
model_list:
  - model_name: gpt
    litellm_params: {{model: openai/gpt-4o, api_key: fake, api_base: "{bad}", order: 1, input_cost_per_token: 0.000001, output_cost_per_token: 0.000001}}
  - model_name: gpt
    litellm_params: {{model: openai/gpt-4o, api_key: fake, mock_response: "from the backup", order: 2, input_cost_per_token: 0.000001, output_cost_per_token: 0.000001}}
  - model_name: solo
    litellm_params: {{model: openai/gpt-4o, api_key: fake, api_base: "{bad}", input_cost_per_token: 0.000001, output_cost_per_token: 0.000001}}
  - model_name: rescue
    litellm_params: {{model: openai/gpt-4o, api_key: fake, mock_response: "rescued", input_cost_per_token: 0.000001, output_cost_per_token: 0.000001}}
router_settings:
  num_retries: 1
  allowed_fails: 0
  cooldown_time: 60
  fallbacks: [{{"solo": ["rescue"]}}]
"#
    );
    let app = gateway(&yaml).await;
    // The first deployment fails; the second answers.
    let (s, h, v) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(chat("gpt"))).await;
    assert_eq!(s, StatusCode::OK, "{v}");
    assert_eq!(v["choices"][0]["message"]["content"], "from the backup");
    assert_eq!(h["x-litellm-attempted-retries"], "1");
    // With allowed_fails 0 the failed deployment now cools down: no retry needed.
    let (_, h, _) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(chat("gpt"))).await;
    assert_eq!(h["x-litellm-attempted-retries"], "0");
    let (_, _, info) = call(&app, "GET", "/model/info", MASTER, None).await;
    let cooling = info["data"].as_array().unwrap().iter().filter(|d| d["model_info"]["cooling_down"] == true).count();
    assert_eq!(cooling, 1);
    // A group with nothing left falls back.
    let (s, h, v) = call(&app, "POST", "/v1/chat/completions", MASTER, Some(chat("solo"))).await;
    assert_eq!(s, StatusCode::OK, "{v}");
    assert_eq!(v["choices"][0]["message"]["content"], "rescued");
    assert_eq!(h["x-litellm-attempted-fallbacks"], "1");
}

#[tokio::test]
async fn streams_are_settled() {
    let app = gateway(MOCKS).await;
    let key = new_key(&app, json!({})).await;
    let mut body = chat("gpt");
    body["stream"] = json!(true);
    let (s, h, v) = call(&app, "POST", "/v1/chat/completions", &key, Some(body)).await;
    assert_eq!(s, StatusCode::OK);
    assert_eq!(h["content-type"], "text/event-stream");
    let text = v.as_str().unwrap();
    assert!(text.trim_end().ends_with("data: [DONE]"), "{text}");
    // No usage chunk unless asked for.
    assert!(!text.contains("\"choices\":[]"), "{text}");
    // Settlement runs when the stream ends.
    for _ in 0..50 {
        let (_, _, info) = call(&app, "GET", "/key/info", &key, None).await;
        if info["info"]["spend"].as_f64().unwrap() > 0.0 {
            assert_eq!(info["info"]["reserved_spend"].as_f64().unwrap(), 0.0);
            return;
        }
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    panic!("the stream was never settled");
}
