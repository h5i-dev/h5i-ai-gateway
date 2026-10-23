//! The admin UI at `/ui` (page, assets, caching, SPA fallback) and the
//! spend log filters it uses, through the router with the in-memory executor.

use axum::Router;
use axum::body::Body;
use axum::http::{HeaderMap, Request, StatusCode};
use gateway_server::config::Config;
use gateway_server::kernel::{Backend, MemoryExecutor};
use gateway_server::registry::Registry;
use gateway_server::spend::SpendReader;
use gateway_server::{AppState, ProxySettings, auth::GatewayAuth, router, sync, ui};
use http_body_util::BodyExt;
use serde_json::{Value, json};
use std::sync::Arc;
use std::time::Duration;
use tower::ServiceExt;

const MASTER: &str = "sk-master";

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

async fn gateway() -> Router {
    let config = Config::parse(MOCKS).unwrap();
    let env = |_: &str| None;
    let reader = Arc::new(SpendReader::memory(100));
    let recorder = reader.clone();
    let state = AppState {
        backend: Arc::new(Backend::Memory(MemoryExecutor::new(Box::new(move |t, log| recorder.record(t, log))))),
        keys: Arc::new(GatewayAuth::new(Some(MASTER.into()), "test-secret", 1)),
        registry: Arc::new(Registry::from_config(&config, &env).unwrap()),
        client: gateway_providers::Client::new(Default::default()).unwrap(),
        settings: Arc::new(ProxySettings {
            org: 1,
            num_retries: 0,
            fallbacks: Default::default(),
            aliases: Default::default(),
            timeout: Duration::from_secs(30),
            default_max_tokens: 100,
        }),
        spend: Some(reader),
        guardrails: Default::default(),
        cache: None,
    };
    sync(&state, &config).await.unwrap();
    router(state)
}

/// A request without credentials: the UI's files are public.
async fn get(app: &Router, path: &str) -> (StatusCode, HeaderMap, Vec<u8>) {
    let resp = app.clone().oneshot(Request::builder().uri(path).body(Body::empty()).unwrap()).await.unwrap();
    let status = resp.status();
    let headers = resp.headers().clone();
    (status, headers, resp.into_body().collect().await.unwrap().to_bytes().to_vec())
}

async fn call(app: &Router, method: &str, path: &str, key: &str, body: Option<Value>) -> (StatusCode, Value) {
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
    let bytes = resp.into_body().collect().await.unwrap().to_bytes();
    (status, serde_json::from_slice(&bytes).unwrap_or(Value::Null))
}

fn header<'a>(h: &'a HeaderMap, name: &str) -> &'a str {
    h.get(name).map(|v| v.to_str().unwrap()).unwrap_or("")
}

fn assert_page(status: StatusCode, h: &HeaderMap, body: &[u8]) {
    assert_eq!(status, StatusCode::OK);
    assert_eq!(header(h, "content-type"), "text/html; charset=utf-8");
    assert_eq!(header(h, "cache-control"), "no-cache");
    assert!(header(h, "content-security-policy").contains("default-src 'none'"));
    assert!(header(h, "content-security-policy").contains("script-src 'self'"));
    assert_eq!(header(h, "x-content-type-options"), "nosniff");
    let html = std::str::from_utf8(body).unwrap();
    assert!(html.contains(&format!("/ui/assets/{}/js/main.js", ui::version())), "{html}");
    assert!(!html.contains("{{"));
}

#[tokio::test]
async fn the_page_is_served_at_ui_and_ui_slash() {
    let app = gateway().await;
    for path in ["/ui", "/ui/"] {
        let (s, h, body) = get(&app, path).await;
        assert_page(s, &h, &body);
    }
}

#[tokio::test]
async fn unknown_ui_paths_fall_back_to_the_page() {
    let app = gateway().await;
    for path in ["/ui/keys", "/ui/spend", "/ui/teams/42/edit", "/ui/assets", "/ui/spend?range=7d&model=gpt"] {
        let (s, h, body) = get(&app, path).await;
        assert_page(s, &h, &body);
    }
}

#[tokio::test]
async fn every_asset_is_served_with_its_type_and_cached_for_good() {
    let app = gateway().await;
    let mut n = 0;
    for (path, mime) in ui::assets() {
        let (s, h, body) = get(&app, &format!("/ui/assets/{}/{path}", ui::version())).await;
        assert_eq!(s, StatusCode::OK, "{path}");
        assert_eq!(header(&h, "content-type"), mime, "{path}");
        let expected = match path.rsplit('.').next().unwrap() {
            "js" => "text/javascript; charset=utf-8",
            "css" => "text/css; charset=utf-8",
            "svg" => "image/svg+xml",
            other => panic!("unexpected asset type {other}"),
        };
        assert_eq!(mime, expected, "{path}");
        assert_eq!(header(&h, "cache-control"), "public, max-age=31536000, immutable", "{path}");
        assert_eq!(header(&h, "x-content-type-options"), "nosniff");
        assert!(!body.is_empty(), "{path}");
        n += 1;
    }
    assert!(n >= 10);
}

#[tokio::test]
async fn an_outdated_asset_version_is_served_uncached_and_unknown_assets_are_404() {
    let app = gateway().await;
    let (s, h, _) = get(&app, "/ui/assets/000000000000/app.css").await;
    assert_eq!(s, StatusCode::OK);
    assert_eq!(header(&h, "content-type"), "text/css; charset=utf-8");
    assert_eq!(header(&h, "cache-control"), "no-cache");
    for path in ["/ui/assets/v/nope.js", "/ui/assets/v/js/../app.css.map", "/ui/assets/v/js"] {
        let (s, _, _) = get(&app, path).await;
        assert_eq!(s, StatusCode::NOT_FOUND, "{path}");
    }
}

#[tokio::test]
async fn ui_routes_do_not_shadow_the_api() {
    let app = gateway().await;
    let (s, _, _) = get(&app, "/key/list").await;
    assert_eq!(s, StatusCode::UNAUTHORIZED);
    let (s, _, _) = get(&app, "/health/liveliness").await;
    assert_eq!(s, StatusCode::OK);
}

fn chat(model: &str) -> Value {
    json!({"model": model, "messages": [{"role": "user", "content": "Say hi"}], "max_tokens": 10})
}

async fn new_key(app: &Router, body: Value) -> (String, String) {
    let (s, v) = call(app, "POST", "/key/generate", MASTER, Some(body)).await;
    assert_eq!(s, StatusCode::OK, "{v}");
    (v["key"].as_str().unwrap().to_string(), v["token_id"].as_str().unwrap().to_string())
}

async fn logs(app: &Router, query: &str) -> Vec<Value> {
    let (s, v) = call(app, "GET", &format!("/spend/logs?{query}"), MASTER, None).await;
    assert_eq!(s, StatusCode::OK, "{query}: {v}");
    v.as_array().unwrap().clone()
}

#[tokio::test]
async fn spend_logs_without_a_database_filter_and_name_their_model_group() {
    let app = gateway().await;
    let (s, team) = call(&app, "POST", "/team/new", MASTER, Some(json!({}))).await;
    assert_eq!(s, StatusCode::OK);
    let team = team["team_id"].as_str().unwrap().to_string();
    let (a, a_id) = new_key(&app, json!({})).await;
    let (b, b_id) = new_key(&app, json!({"team_id": team})).await;
    for (key, model) in [(&a, "gpt"), (&a, "claude"), (&b, "gpt"), (&a, "gpt")] {
        let (s, v) = call(&app, "POST", "/v1/chat/completions", key, Some(chat(model))).await;
        assert_eq!(s, StatusCode::OK, "{v}");
    }

    let all = logs(&app, "").await;
    assert_eq!(all.len(), 4);
    // Newest first, with the model group's name and the deployment's model.
    assert_eq!(all[0]["api_key"], a_id.as_str());
    assert_eq!(all[0]["model_group"], "gpt");
    assert_eq!(all[0]["model"], "openai/gpt-4o");
    assert!(all.iter().all(|l| l["status"] == "success" && l["spend"].as_f64().unwrap() > 0.0));

    assert_eq!(logs(&app, &format!("api_key={a_id}")).await.len(), 3);
    // A virtual key works as well as its id.
    assert_eq!(logs(&app, &format!("api_key={b}")).await.len(), 1);
    assert_eq!(logs(&app, &format!("team_id={team}")).await[0]["api_key"], b_id.as_str());
    assert_eq!(logs(&app, "model=claude").await.len(), 1);
    assert_eq!(logs(&app, &format!("model=gpt&api_key={a_id}")).await.len(), 2);
    assert!(logs(&app, "model=no-such-model").await.is_empty());
    assert!(logs(&app, "status=failure").await.is_empty());
    assert_eq!(logs(&app, "status=success&limit=2").await.len(), 2);
    // Empty parameters are no filter.
    assert_eq!(logs(&app, "api_key=&team_id=&model=&status=&start_date=").await.len(), 4);
    // Time bounds: Unix seconds or whole UTC days.
    assert_eq!(logs(&app, "start_date=0").await.len(), 4);
    assert!(logs(&app, "start_date=4102444800").await.is_empty());
    assert_eq!(logs(&app, "start_date=2000-01-01&end_date=2099-12-31").await.len(), 4);
    assert!(logs(&app, "end_date=2000-01-01").await.is_empty());
    let (s, v) = call(&app, "GET", "/spend/logs?start_date=yesterday", MASTER, None).await;
    assert_eq!(s, StatusCode::BAD_REQUEST, "{v}");
    assert!(v["error"]["message"].as_str().unwrap().contains("start_date"));
}

#[tokio::test]
async fn spend_logs_are_for_admins_only() {
    let app = gateway().await;
    let (user, _) = new_key(&app, json!({})).await;
    let (s, v) = call(&app, "GET", "/spend/logs", &user, None).await;
    assert_eq!(s, StatusCode::FORBIDDEN, "{v}");
    assert_eq!(v["error"]["type"], "auth_error");
    let (admin, _) = new_key(&app, json!({"user_role": "proxy_admin"})).await;
    let (s, _) = call(&app, "GET", "/spend/logs", &admin, None).await;
    assert_eq!(s, StatusCode::OK);
}

#[tokio::test]
async fn readiness_reports_no_database_in_memory() {
    let app = gateway().await;
    let (s, v) = call(&app, "GET", "/health/readiness", MASTER, None).await;
    assert_eq!(s, StatusCode::OK);
    assert_eq!(v["db"], "Not connected");
}
