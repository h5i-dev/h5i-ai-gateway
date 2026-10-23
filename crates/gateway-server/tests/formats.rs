//! End to end through the router for the Anthropic Messages API
//! (`/v1/messages`) and the OpenAI Responses API (`/v1/responses`): both are
//! translated to the chat path, so keys, budgets and rate limits apply and
//! the spend is settled. Upstreams are `mock_response` deployments and a
//! local fake OpenAI server that records what it was sent.

use axum::Router;
use axum::body::Body;
use axum::http::{HeaderMap, Request, StatusCode};
use axum::response::IntoResponse;
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

type Seen = Arc<Mutex<Vec<Value>>>;

/// A fake OpenAI upstream: answers with a tool call when the request has
/// tools and its last message is not a tool result, else with text;
/// streams when asked. Records every request body.
async fn fake_openai() -> (String, Seen) {
    let seen: Seen = Arc::default();
    let log = seen.clone();
    let app = Router::new().fallback(move |body: axum::body::Bytes| {
        let log = log.clone();
        async move {
            let req: Value = serde_json::from_slice(&body).unwrap();
            log.lock().unwrap().push(req.clone());
            let last_is_tool = req["messages"].as_array().and_then(|m| m.last()).is_some_and(|m| m["role"] == "tool");
            let tool = req.get("tools").is_some() && !last_is_tool;
            let usage = json!({"prompt_tokens": 20, "completion_tokens": 5, "total_tokens": 25});
            if req["stream"] == true {
                let mut chunks = vec![json!({"id": "chatcmpl-f", "object": "chat.completion.chunk", "created": 1, "model": "gpt-4o",
                    "choices": [{"index": 0, "delta": {"role": "assistant", "content": ""}, "finish_reason": null}]})];
                let delta = |d: Value, f: Value| json!({"id": "chatcmpl-f", "object": "chat.completion.chunk", "created": 1, "model": "gpt-4o",
                    "choices": [{"index": 0, "delta": d, "finish_reason": f}]});
                if tool {
                    chunks.push(delta(json!({"tool_calls": [{"index": 0, "id": "call_w", "type": "function", "function": {"name": "get_weather", "arguments": ""}}]}), Value::Null));
                    chunks.push(delta(json!({"tool_calls": [{"index": 0, "function": {"arguments": "{\"city\":"}}]}), Value::Null));
                    chunks.push(delta(json!({"tool_calls": [{"index": 0, "function": {"arguments": "\"Paris\"}"}}]}), Value::Null));
                    chunks.push(delta(json!({}), json!("tool_calls")));
                } else {
                    chunks.push(delta(json!({"content": "fake "}), Value::Null));
                    chunks.push(delta(json!({"content": "answer"}), Value::Null));
                    chunks.push(delta(json!({}), json!("stop")));
                }
                chunks.push(json!({"id": "chatcmpl-f", "object": "chat.completion.chunk", "created": 1, "model": "gpt-4o", "choices": [], "usage": usage}));
                let mut body: String = chunks.iter().map(|c| format!("data: {c}\n\n")).collect();
                body.push_str("data: [DONE]\n\n");
                return ([("content-type", "text/event-stream")], body).into_response();
            }
            let message = if tool {
                json!({"role": "assistant", "content": null, "tool_calls": [{"id": "call_w", "type": "function", "function": {"name": "get_weather", "arguments": "{\"city\":\"Paris\"}"}}]})
            } else {
                json!({"role": "assistant", "content": "fake answer"})
            };
            let finish = if tool { "tool_calls" } else { "stop" };
            axum::Json(json!({"id": "chatcmpl-f", "object": "chat.completion", "created": 1, "model": "gpt-4o",
                "choices": [{"index": 0, "message": message, "finish_reason": finish}], "usage": usage}))
            .into_response()
        }
    });
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
    (format!("http://{addr}/v1"), seen)
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

/// Mock deployments plus `fake`, served by the fake upstream at `base`.
fn config(base: &str) -> String {
    format!(
        r#"
model_list:
  - model_name: gpt
    litellm_params: {{model: openai/gpt-4o, api_key: fake, mock_response: "hi there", input_cost_per_token: 0.000001, output_cost_per_token: 0.000002}}
  - model_name: claude
    litellm_params: {{model: anthropic/claude-3-5-sonnet-20241022, api_key: fake, mock_response: "hello from claude", input_cost_per_token: 0.000003, output_cost_per_token: 0.000015}}
  - model_name: fake
    litellm_params: {{model: openai/gpt-4o, api_key: fake, api_base: "{base}", input_cost_per_token: 0.000001, output_cost_per_token: 0.000002}}
"#
    )
}

struct Reply {
    status: StatusCode,
    headers: HeaderMap,
    body: Value,
    text: String,
}

async fn send(
    app: &Router,
    method: &str,
    path: &str,
    headers: &[(&str, &str)],
    body: Option<Value>,
) -> Reply {
    let mut req = Request::builder().method(method).uri(path);
    for (k, v) in headers {
        req = req.header(*k, *v);
    }
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
    let text = String::from_utf8_lossy(&bytes).into_owned();
    let body = serde_json::from_str(&text).unwrap_or(Value::Null);
    Reply {
        status,
        headers,
        body,
        text,
    }
}

/// Anthropic's SDK: `x-api-key` and `anthropic-version`.
async fn messages(app: &Router, key: &str, body: Value) -> Reply {
    send(
        app,
        "POST",
        "/v1/messages",
        &[("x-api-key", key), ("anthropic-version", "2023-06-01")],
        Some(body),
    )
    .await
}

async fn responses(app: &Router, key: &str, body: Value) -> Reply {
    let auth = format!("Bearer {key}");
    send(
        app,
        "POST",
        "/v1/responses",
        &[("authorization", &auth)],
        Some(body),
    )
    .await
}

async fn bearer(app: &Router, method: &str, path: &str, key: &str, body: Option<Value>) -> Reply {
    let auth = format!("Bearer {key}");
    send(app, method, path, &[("authorization", &auth)], body).await
}

async fn new_key(app: &Router, body: Value) -> String {
    let r = bearer(app, "POST", "/key/generate", MASTER, Some(body)).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    r.body["key"].as_str().unwrap().to_string()
}

async fn spend(app: &Router, key: &str) -> (f64, f64) {
    let r = bearer(app, "GET", "/key/info", key, None).await;
    (
        r.body["info"]["spend"].as_f64().unwrap(),
        r.body["info"]["reserved_spend"].as_f64().unwrap(),
    )
}

/// Wait for a streamed call to settle: spend above zero, nothing reserved.
async fn settled(app: &Router, key: &str) -> f64 {
    for _ in 0..100 {
        let (spent, reserved) = spend(app, key).await;
        if spent > 0.0 && reserved == 0.0 {
            return spent;
        }
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    panic!("the stream was never settled");
}

/// SSE events as `(event name, data)`.
fn events(text: &str) -> Vec<(String, Value)> {
    text.split("\n\n")
        .filter(|e| !e.trim().is_empty())
        .map(|e| {
            let mut name = String::new();
            let mut data = Value::Null;
            for line in e.lines() {
                if let Some(n) = line.strip_prefix("event: ") {
                    name = n.to_string();
                } else if let Some(d) = line.strip_prefix("data: ") {
                    data = serde_json::from_str(d).unwrap();
                }
            }
            (name, data)
        })
        .collect()
}

fn names(evs: &[(String, Value)]) -> Vec<&str> {
    evs.iter().map(|(n, _)| n.as_str()).collect()
}

fn hello() -> Value {
    json!({"model": "gpt", "max_tokens": 10, "messages": [{"role": "user", "content": "Say hi"}]})
}

// ---------------------------------------------------------------------------
// Anthropic Messages API

#[tokio::test]
async fn messages_through_an_openai_deployment_are_charged() {
    let app = gateway(&config("http://unused")).await;
    let key = new_key(
        &app,
        json!({"models": ["gpt", "claude"], "max_budget": 1.0}),
    )
    .await;
    let r = messages(&app, &key, hello()).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    assert_eq!(r.body["type"], "message");
    assert_eq!(r.body["role"], "assistant");
    assert_eq!(r.body["model"], "gpt");
    assert!(r.body["id"].as_str().unwrap().starts_with("msg_"));
    assert_eq!(
        r.body["content"],
        json!([{"type": "text", "text": "hi there"}])
    );
    assert_eq!(r.body["stop_reason"], "end_turn");
    assert!(r.body["usage"]["input_tokens"].as_u64().unwrap() > 0);
    assert!(r.body["usage"]["output_tokens"].as_u64().unwrap() > 0);
    let cost: f64 = r.headers["x-litellm-response-cost"]
        .to_str()
        .unwrap()
        .parse()
        .unwrap();
    assert!(cost > 0.0);
    assert_eq!(spend(&app, &key).await, (cost, 0.0));

    // The Anthropic-prefixed path and an Anthropic deployment, with `Authorization` too.
    let auth = format!("Bearer {key}");
    let mut body = hello();
    body["model"] = json!("claude");
    body["system"] =
        json!([{"type": "text", "text": "Be nice", "cache_control": {"type": "ephemeral"}}]);
    body["thinking"] = json!({"type": "enabled", "budget_tokens": 1024});
    let r = send(
        &app,
        "POST",
        "/anthropic/v1/messages",
        &[("authorization", &auth)],
        Some(body),
    )
    .await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    assert_eq!(r.body["content"][0]["text"], "hello from claude");
    assert!(spend(&app, &key).await.0 > cost);
}

#[tokio::test]
async fn messages_stream_in_anthropic_events_and_settle() {
    let app = gateway(&config("http://unused")).await;
    let key = new_key(&app, json!({})).await;
    let mut body = hello();
    body["stream"] = json!(true);
    let r = messages(&app, &key, body).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    assert_eq!(r.headers["content-type"], "text/event-stream");
    let evs = events(&r.text);
    let n = names(&evs);
    assert_eq!(&n[..3], ["message_start", "ping", "content_block_start"]);
    assert_eq!(
        &n[n.len() - 3..],
        ["content_block_stop", "message_delta", "message_stop"]
    );
    assert!(
        n[3..n.len() - 3]
            .iter()
            .all(|e| *e == "content_block_delta"),
        "{n:?}"
    );
    for (name, data) in &evs {
        assert_eq!(data["type"], name.as_str());
    }
    let text: String = evs
        .iter()
        .filter_map(|(_, d)| d["delta"]["text"].as_str())
        .collect();
    assert_eq!(text, "hi there");
    let delta = &evs[evs.len() - 2].1;
    assert_eq!(delta["delta"]["stop_reason"], "end_turn");
    assert!(delta["usage"]["output_tokens"].as_u64().unwrap() > 0);
    assert!(!r.text.contains("[DONE]"));
    settled(&app, &key).await;
}

#[tokio::test]
async fn messages_with_tools_through_an_openai_upstream() {
    let (base, seen) = fake_openai().await;
    let app = gateway(&config(&base)).await;
    let tools = json!([{"name": "get_weather", "description": "Weather", "input_schema": {"type": "object", "properties": {"city": {"type": "string"}}}}]);
    let body = json!({
        "model": "fake", "max_tokens": 50, "tools": tools, "tool_choice": {"type": "any"},
        "thinking": {"type": "enabled", "budget_tokens": 2048}, "top_k": 3,
        "metadata": {"user_id": "u-1"}, "stop_sequences": ["STOP"],
        "system": [{"type": "text", "text": "sys", "cache_control": {"type": "ephemeral"}}],
        "messages": [{"role": "user", "content": [
            {"type": "text", "text": "Weather in Paris?"},
            {"type": "image", "source": {"type": "base64", "media_type": "image/png", "data": "iVBO"}}
        ]}]
    });
    let r = messages(&app, MASTER, body.clone()).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    assert_eq!(r.body["stop_reason"], "tool_use");
    assert_eq!(
        r.body["content"],
        json!([{"type": "tool_use", "id": "call_w", "name": "get_weather", "input": {"city": "Paris"}}])
    );
    assert_eq!(
        r.body["usage"],
        json!({"input_tokens": 20, "output_tokens": 5, "cache_creation_input_tokens": 0, "cache_read_input_tokens": 0})
    );
    // What OpenAI received: chat completions, without Anthropic-only fields.
    let sent = seen.lock().unwrap().last().cloned().unwrap();
    assert_eq!(sent["tools"][0]["function"]["name"], "get_weather");
    assert_eq!(sent["tool_choice"], "required");
    assert_eq!(sent["reasoning_effort"], "medium");
    assert_eq!(sent["user"], "u-1");
    assert_eq!(sent["stop"], json!(["STOP"]));
    assert_eq!(sent["max_completion_tokens"], 50);
    assert_eq!(
        sent["messages"][0],
        json!({"role": "system", "content": [{"type": "text", "text": "sys"}]})
    );
    assert_eq!(
        sent["messages"][1]["content"][1]["image_url"]["url"],
        "data:image/png;base64,iVBO"
    );
    for field in ["thinking", "top_k", "metadata"] {
        assert!(sent.get(field).is_none(), "{field} was forwarded: {sent}");
    }

    // The tool result comes back; the model answers.
    let mut next = body.clone();
    next["messages"] = json!([
        {"role": "user", "content": "Weather in Paris?"},
        {"role": "assistant", "content": r.body["content"]},
        {"role": "user", "content": [{"type": "tool_result", "tool_use_id": "call_w", "content": "18C"}]}
    ]);
    let r = messages(&app, MASTER, next).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    assert_eq!(r.body["content"][0]["text"], "fake answer");
    let sent = seen.lock().unwrap().last().cloned().unwrap();
    assert_eq!(sent["messages"][2]["tool_calls"][0]["id"], "call_w");
    assert_eq!(
        sent["messages"][3],
        json!({"role": "tool", "content": "18C", "tool_call_id": "call_w"})
    );

    // Streaming a tool call: input_json_delta events.
    let mut streamed = body;
    streamed["stream"] = json!(true);
    let r = messages(&app, MASTER, streamed).await;
    let evs = events(&r.text);
    let start = evs
        .iter()
        .find(|(n, _)| n == "content_block_start")
        .unwrap();
    assert_eq!(
        start.1["content_block"],
        json!({"type": "tool_use", "id": "call_w", "name": "get_weather", "input": {}})
    );
    let args: String = evs
        .iter()
        .filter_map(|(_, d)| d["delta"]["partial_json"].as_str())
        .collect();
    assert_eq!(args, "{\"city\":\"Paris\"}");
    let delta = evs.iter().find(|(n, _)| n == "message_delta").unwrap();
    assert_eq!(delta.1["delta"]["stop_reason"], "tool_use");
    assert_eq!(delta.1["usage"]["input_tokens"], 20);
}

#[tokio::test]
async fn messages_errors_are_in_anthropics_shape() {
    let app = gateway(&config("http://unused")).await;
    let r = messages(&app, "sk-nope", hello()).await;
    assert_eq!(r.status, StatusCode::UNAUTHORIZED);
    assert_eq!(r.body["type"], "error");
    assert_eq!(r.body["error"]["type"], "authentication_error");
    let r = send(&app, "POST", "/v1/messages", &[], Some(hello())).await;
    assert_eq!(r.status, StatusCode::UNAUTHORIZED);
    assert_eq!(r.body["error"]["type"], "authentication_error");

    let key = new_key(&app, json!({"models": ["claude"]})).await;
    let r = messages(&app, &key, hello()).await;
    assert_eq!(r.status, StatusCode::UNAUTHORIZED, "{}", r.text);
    assert_eq!(r.body["error"]["type"], "authentication_error");

    let poor = new_key(&app, json!({"max_budget": 0.000000001})).await;
    let r = messages(&app, &poor, hello()).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(r.body["error"]["type"], "invalid_request_error");
    assert!(
        r.body["error"]["message"]
            .as_str()
            .unwrap()
            .contains("ExceededBudget")
    );

    let slow = new_key(&app, json!({"rpm_limit": 1})).await;
    assert_eq!(messages(&app, &slow, hello()).await.status, StatusCode::OK);
    let r = messages(&app, &slow, hello()).await;
    assert_eq!(r.status, StatusCode::TOO_MANY_REQUESTS);
    assert_eq!(r.body["error"]["type"], "rate_limit_error");

    let r = messages(
        &app,
        MASTER,
        json!({"model": "gpt", "messages": [{"role": "robot", "content": "x"}]}),
    )
    .await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(r.body["error"]["type"], "invalid_request_error");
    let r = messages(&app, MASTER, json!({"messages": []})).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(r.body["type"], "error");
    let r = messages(
        &app,
        MASTER,
        json!({"model": "nope", "max_tokens": 5, "messages": [{"role": "user", "content": "x"}]}),
    )
    .await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(r.body["error"]["type"], "invalid_request_error");

    // A provider failure keeps its status.
    let mut body = hello();
    body["mock_response"] = json!("litellm.RateLimitError");
    let r = messages(&app, MASTER, body).await;
    assert_eq!(r.status, StatusCode::TOO_MANY_REQUESTS, "{}", r.text);
    assert_eq!(r.body["error"]["type"], "rate_limit_error");
}

#[tokio::test]
async fn count_tokens_charges_nothing() {
    let app = gateway(&config("http://unused")).await;
    let key = new_key(&app, json!({})).await;
    let r = send(
        &app,
        "POST",
        "/v1/messages/count_tokens",
        &[("x-api-key", &key)],
        Some(hello()),
    )
    .await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    assert!(r.body["input_tokens"].as_u64().unwrap() > 0);
    assert_eq!(spend(&app, &key).await, (0.0, 0.0));
    let r = send(
        &app,
        "POST",
        "/v1/messages/count_tokens",
        &[("x-api-key", "bad")],
        Some(hello()),
    )
    .await;
    assert_eq!(r.status, StatusCode::UNAUTHORIZED);
    assert_eq!(r.body["error"]["type"], "authentication_error");
}

// ---------------------------------------------------------------------------
// Responses API

#[tokio::test]
async fn responses_are_charged_stored_and_scoped() {
    let app = gateway(&config("http://unused")).await;
    let key = new_key(&app, json!({"max_budget": 1.0})).await;
    let other = new_key(&app, json!({})).await;
    let r = responses(&app, &key, json!({"model": "gpt", "input": "Say hi", "instructions": "Be brief.", "max_output_tokens": 10})).await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    let id = r.body["id"].as_str().unwrap().to_string();
    assert!(id.starts_with("resp_"));
    assert_eq!(r.body["object"], "response");
    assert_eq!(r.body["status"], "completed");
    assert_eq!(r.body["model"], "gpt");
    assert_eq!(r.body["instructions"], "Be brief.");
    assert_eq!(r.body["output"][0]["type"], "message");
    assert_eq!(
        r.body["output"][0]["content"][0],
        json!({"type": "output_text", "text": "hi there", "annotations": []})
    );
    assert!(r.body["usage"]["input_tokens"].as_u64().unwrap() > 0);
    assert!(r.body["usage"]["output_tokens"].as_u64().unwrap() > 0);
    let cost: f64 = r.headers["x-litellm-response-cost"]
        .to_str()
        .unwrap()
        .parse()
        .unwrap();
    assert_eq!(spend(&app, &key).await, (cost, 0.0));

    // Stored for this key only.
    let path = format!("/v1/responses/{id}");
    let got = bearer(&app, "GET", &path, &key, None).await;
    assert_eq!(got.status, StatusCode::OK);
    assert_eq!(got.body, r.body);
    assert_eq!(
        bearer(&app, "GET", &path, &other, None).await.status,
        StatusCode::NOT_FOUND
    );
    assert_eq!(
        bearer(&app, "GET", &path, MASTER, None).await.status,
        StatusCode::NOT_FOUND
    );
    assert_eq!(
        bearer(&app, "DELETE", &path, &other, None).await.status,
        StatusCode::NOT_FOUND
    );
    let r2 = responses(
        &app,
        &other,
        json!({"model": "gpt", "input": "more", "previous_response_id": id}),
    )
    .await;
    assert_eq!(r2.status, StatusCode::BAD_REQUEST);
    assert_eq!(r2.body["error"]["code"], "previous_response_not_found");
    let del = bearer(&app, "DELETE", &path, &key, None).await;
    assert_eq!(del.status, StatusCode::OK);
    assert_eq!(
        del.body,
        json!({"id": id, "object": "response", "deleted": true})
    );
    assert_eq!(
        bearer(&app, "GET", &path, &key, None).await.status,
        StatusCode::NOT_FOUND
    );

    // `store: false` keeps nothing.
    let r = responses(
        &app,
        &key,
        json!({"model": "gpt", "input": "x", "store": false}),
    )
    .await;
    assert_eq!(r.body["store"], false);
    let path = format!("/v1/responses/{}", r.body["id"].as_str().unwrap());
    assert_eq!(
        bearer(&app, "GET", &path, &key, None).await.status,
        StatusCode::NOT_FOUND
    );
}

#[tokio::test]
async fn previous_response_id_continues_the_conversation() {
    let (base, seen) = fake_openai().await;
    let app = gateway(&config(&base)).await;
    let tools = json!([{"type": "function", "name": "get_weather", "parameters": {"type": "object", "properties": {"city": {"type": "string"}}}}]);
    let r = responses(
        &app,
        MASTER,
        json!({
            "model": "fake", "instructions": "sys", "tools": tools, "tool_choice": "auto",
            "reasoning": {"effort": "low"}, "temperature": 0.1,
            "text": {"format": {"type": "json_schema", "name": "w", "schema": {"type": "object"}}},
            "input": [{"role": "user", "content": [
                {"type": "input_text", "text": "Weather in Paris?"},
                {"type": "input_image", "image_url": "https://x/p.png"}
            ]}]
        }),
    )
    .await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    let call = &r.body["output"][0];
    assert_eq!(call["type"], "function_call");
    assert_eq!(call["call_id"], "call_w");
    assert_eq!(call["name"], "get_weather");
    assert_eq!(call["arguments"], "{\"city\":\"Paris\"}");
    let sent = seen.lock().unwrap().last().cloned().unwrap();
    assert_eq!(
        sent["messages"][0],
        json!({"role": "system", "content": "sys"})
    );
    assert_eq!(
        sent["messages"][1]["content"][1],
        json!({"type": "image_url", "image_url": {"url": "https://x/p.png"}})
    );
    assert_eq!(sent["tools"][0]["function"]["name"], "get_weather");
    assert_eq!(sent["reasoning_effort"], "low");
    assert_eq!(sent["response_format"]["type"], "json_schema");

    // The tool output, continuing from the stored response.
    let id = r.body["id"].as_str().unwrap();
    let r = responses(
        &app,
        MASTER,
        json!({
            "model": "fake", "tools": tools, "previous_response_id": id,
            "input": [{"type": "function_call_output", "call_id": "call_w", "output": "18C"}]
        }),
    )
    .await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    assert_eq!(r.body["previous_response_id"], id);
    assert_eq!(r.body["output"][0]["content"][0]["text"], "fake answer");
    let sent = seen.lock().unwrap().last().cloned().unwrap();
    let msgs = sent["messages"].as_array().unwrap();
    // Instructions are not carried over; the history is.
    assert_eq!(msgs.len(), 3, "{sent}");
    assert_eq!(msgs[0]["role"], "user");
    assert_eq!(msgs[1]["tool_calls"][0]["id"], "call_w");
    assert_eq!(
        msgs[2],
        json!({"role": "tool", "content": "18C", "tool_call_id": "call_w"})
    );

    let r = responses(
        &app,
        MASTER,
        json!({"model": "fake", "input": "x", "previous_response_id": "resp_missing"}),
    )
    .await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(r.body["error"]["param"], "previous_response_id");
}

#[tokio::test]
async fn responses_stream_events_settle_and_are_stored() {
    let app = gateway(&config("http://unused")).await;
    let key = new_key(&app, json!({})).await;
    let r = responses(
        &app,
        &key,
        json!({"model": "gpt", "input": "Say hi", "stream": true}),
    )
    .await;
    assert_eq!(r.status, StatusCode::OK, "{}", r.text);
    assert_eq!(r.headers["content-type"], "text/event-stream");
    let evs = events(&r.text);
    let n = names(&evs);
    assert_eq!(
        &n[..4],
        [
            "response.created",
            "response.in_progress",
            "response.output_item.added",
            "response.content_part.added"
        ]
    );
    assert_eq!(
        &n[n.len() - 4..],
        [
            "response.output_text.done",
            "response.content_part.done",
            "response.output_item.done",
            "response.completed"
        ]
    );
    for (i, (name, data)) in evs.iter().enumerate() {
        assert_eq!(data["type"], name.as_str());
        assert_eq!(data["sequence_number"], i as u64);
    }
    let text: String = evs
        .iter()
        .filter(|(n, _)| n == "response.output_text.delta")
        .filter_map(|(_, d)| d["delta"].as_str())
        .collect();
    assert_eq!(text, "hi there");
    let done = &evs.last().unwrap().1["response"];
    assert_eq!(done["status"], "completed");
    assert!(done["usage"]["output_tokens"].as_u64().unwrap() > 0);
    settled(&app, &key).await;
    // Stored once the stream ended.
    let got = bearer(
        &app,
        "GET",
        &format!("/v1/responses/{}", done["id"].as_str().unwrap()),
        &key,
        None,
    )
    .await;
    assert_eq!(got.status, StatusCode::OK);
    assert_eq!(&got.body, done);
}

#[tokio::test]
async fn responses_stream_function_calls() {
    let (base, _) = fake_openai().await;
    let app = gateway(&config(&base)).await;
    let r = responses(
        &app,
        MASTER,
        json!({"model": "fake", "input": "Weather?", "stream": true,
        "tools": [{"type": "function", "name": "get_weather", "parameters": {"type": "object"}}]}),
    )
    .await;
    let evs = events(&r.text);
    let added = evs
        .iter()
        .find(|(n, _)| n == "response.output_item.added")
        .unwrap();
    assert_eq!(added.1["item"]["type"], "function_call");
    assert_eq!(added.1["item"]["call_id"], "call_w");
    let args: String = evs
        .iter()
        .filter(|(n, _)| n == "response.function_call_arguments.delta")
        .filter_map(|(_, d)| d["delta"].as_str())
        .collect();
    assert_eq!(args, "{\"city\":\"Paris\"}");
    let done = evs
        .iter()
        .find(|(n, _)| n == "response.function_call_arguments.done")
        .unwrap();
    assert_eq!(done.1["arguments"], args);
    assert_eq!(
        evs.last().unwrap().1["response"]["usage"]["input_tokens"],
        20
    );
}

#[tokio::test]
async fn responses_refusals_and_bad_requests() {
    let app = gateway(&config("http://unused")).await;
    let poor = new_key(&app, json!({"max_budget": 0.000000001})).await;
    let r = responses(&app, &poor, json!({"model": "gpt", "input": "x"})).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(r.body["error"]["type"], "budget_exceeded");
    let limited = new_key(&app, json!({"models": ["claude"]})).await;
    assert_eq!(
        responses(&app, &limited, json!({"model": "gpt", "input": "x"}))
            .await
            .status,
        StatusCode::UNAUTHORIZED
    );
    assert_eq!(
        responses(&app, "sk-bad", json!({"model": "gpt", "input": "x"}))
            .await
            .status,
        StatusCode::UNAUTHORIZED
    );
    let r = responses(
        &app,
        MASTER,
        json!({"model": "gpt", "input": "x", "tools": [{"type": "web_search_preview"}]}),
    )
    .await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    assert_eq!(r.body["error"]["param"], "tools.0.type");
    let r = responses(&app, MASTER, json!({"input": "x"})).await;
    assert_eq!(r.status, StatusCode::BAD_REQUEST);
    // A provider failure mid-way becomes an error response, nothing stored or charged beyond it.
    let r = responses(
        &app,
        MASTER,
        json!({"model": "gpt", "input": "x", "mock_response": "litellm.RateLimitError"}),
    )
    .await;
    assert_eq!(r.status, StatusCode::TOO_MANY_REQUESTS, "{}", r.text);
    assert!(r.body["error"]["message"].is_string());
}
