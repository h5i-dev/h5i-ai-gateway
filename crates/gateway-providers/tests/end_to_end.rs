//! End-to-end tests: `Client` against a scripted local upstream.

mod common;

use std::time::Duration;

use common::{Canned, Upstream};
use futures::StreamExt;
use gateway_providers::{ChatChunk, ChatRequest, Client, Deployment, EmbeddingRequest, ErrorKind, HttpSettings, ProviderError};
use serde_json::{Value, json};

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
    request(json!({"model": "alias", "messages": [{"role": "user", "content": "Hello"}]}))
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

// --- OpenAI-compatible -----------------------------------------------------

#[tokio::test]
async fn openai_chat() {
    let up = Upstream::start(vec![Canned::json(
        200,
        json!({
            "id": "chatcmpl-1", "object": "chat.completion", "created": 1, "model": "gpt-4o-2024-08-06",
            "choices": [{"index": 0, "message": {"role": "assistant", "content": "Hi!"}, "finish_reason": "stop"}],
            "usage": {"prompt_tokens": 9, "completion_tokens": 3, "total_tokens": 12}
        }),
    )])
    .await;
    let dep = deployment(json!({
        "model": "openai/gpt-4o", "api_key": "sk-test", "api_base": format!("{}/v1", up.base),
        "extra_headers": {"x-team": "blue"}, "temperature": 0.25
    }));
    let mut req = hello();
    req.extra.insert("metadata".into(), json!({"tag": "x"}));
    let resp = client().chat(&dep, &req).await.unwrap();
    assert_eq!(resp.choices[0].message.text(), "Hi!");
    assert_eq!(resp.usage.unwrap().total_tokens, 12);

    let r = up.only_request();
    assert_eq!(r.uri, "/v1/chat/completions");
    assert_eq!(r.header("authorization"), Some("Bearer sk-test"));
    assert_eq!(r.header("x-team"), Some("blue"));
    assert_eq!(r.body["model"], "gpt-4o");
    assert_eq!(r.body["temperature"], 0.25, "deployment default applied");
    assert!(r.body.get("metadata").is_none());
    assert!(r.body.get("stream").is_none());
}

#[tokio::test]
async fn openai_stream_with_usage() {
    let up = Upstream::start(vec![Canned::sse(&[
        "data: {\"id\":\"c\",\"object\":\"chat.completion.chunk\",\"created\":1,\"model\":\"gpt-4o\",\"choices\":[{\"index\":0,\"delta\":{\"role\":\"assistant\",\"content\":\"\"},\"finish_reason\":null}]}\r\n\r\n",
        ": keep-alive\r\n\r\ndata: {\"id\":\"c\",\"object\":\"chat.completion.chunk\",\"created\":1,\"model\":\"gpt-4o\",\"choices\":[{\"index\":0,\"delta\":{\"content\":\"Hel",
        "lo\"},\"finish_reason\":null}]}\r\n\r\ndata: {\"id\":\"c\",\"object\":\"chat.completion.chunk\",\"created\":1,\"model\":\"gpt-4o\",\"choices\":[{\"index\":0,\"delta\":{},\"finish_reason\":\"stop\"}]}\n\n",
        "data: {\"id\":\"c\",\"object\":\"chat.completion.chunk\",\"created\":1,\"model\":\"gpt-4o\",\"choices\":[],\"usage\":{\"prompt_tokens\":5,\"completion_tokens\":1,\"total_tokens\":6}}\n\ndata: [DONE]\n\n",
    ])])
    .await;
    let dep = deployment(json!({"model": "openai/gpt-4o", "api_key": "k", "api_base": up.base}));
    let chunks = ok_chunks(collect(&client(), &dep, &hello()).await);
    assert_eq!(text_of(&chunks), "Hello");
    let last = chunks.last().unwrap();
    assert!(last.is_usage_only());
    assert_eq!(last.usage.as_ref().unwrap().total_tokens, 6);
    assert_eq!(chunks.iter().filter(|c| c.usage.is_some()).count(), 1);

    let r = up.only_request();
    assert_eq!(r.uri, "/chat/completions");
    assert_eq!(r.body["stream"], true);
    assert_eq!(r.body["stream_options"]["include_usage"], true);
}

#[tokio::test]
async fn azure_url_shape() {
    let up = Upstream::start(vec![Canned::json(
        200,
        json!({
            "id": "x", "object": "chat.completion", "created": 1, "model": "gpt-4o",
            "choices": [{"index": 0, "message": {"role": "assistant", "content": "ok"}, "finish_reason": "stop"}]
        }),
    )])
    .await;
    let dep = deployment(json!({
        "model": "azure/my-deployment", "api_key": "az-key", "api_base": up.base, "api_version": "2024-10-21"
    }));
    client().chat(&dep, &hello()).await.unwrap();
    let r = up.only_request();
    assert_eq!(r.uri, "/openai/deployments/my-deployment/chat/completions?api-version=2024-10-21");
    assert_eq!(r.header("api-key"), Some("az-key"));
    assert_eq!(r.header("authorization"), None);
}

#[tokio::test]
async fn openai_embeddings() {
    let up = Upstream::start(vec![Canned::json(
        200,
        json!({
            "object": "list", "model": "text-embedding-3-small",
            "data": [{"object": "embedding", "index": 0, "embedding": [0.1, 0.2]}],
            "usage": {"prompt_tokens": 2, "total_tokens": 2}
        }),
    )])
    .await;
    let dep = deployment(json!({"model": "openai/text-embedding-3-small", "api_key": "k", "api_base": up.base}));
    let req: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": "hi"})).unwrap();
    let resp = client().embeddings(&dep, &req).await.unwrap();
    assert_eq!(resp.usage.prompt_tokens, 2);
    let r = up.only_request();
    assert_eq!((r.uri.as_str(), r.body["model"].as_str()), ("/embeddings", Some("text-embedding-3-small")));
}

// --- Anthropic ---------------------------------------------------------------

fn anthropic(up: &Upstream) -> Deployment {
    deployment(json!({"model": "anthropic/claude-3-5-sonnet-20241022", "api_key": "sk-ant", "api_base": up.base}))
}

fn weather_request(stream: bool) -> ChatRequest {
    request(json!({
        "model": "claude", "stream": stream,
        "messages": [
            {"role": "system", "content": "You are terse."},
            {"role": "user", "content": "Weather in Paris?"}
        ],
        "tools": [{"type": "function", "function": {
            "name": "get_weather", "parameters": {"type": "object", "properties": {"city": {"type": "string"}}}
        }}],
        "tool_choice": "auto",
        "max_tokens": 256
    }))
}

#[tokio::test]
async fn anthropic_chat_with_tool_calls() {
    let up = Upstream::start(vec![Canned::json(
        200,
        json!({
            "id": "msg_1", "type": "message", "role": "assistant", "model": "claude-3-5-sonnet-20241022",
            "content": [
                {"type": "text", "text": "Checking."},
                {"type": "tool_use", "id": "toolu_1", "name": "get_weather", "input": {"city": "Paris"}}
            ],
            "stop_reason": "tool_use",
            "usage": {"input_tokens": 20, "output_tokens": 10, "cache_read_input_tokens": 5}
        }),
    )])
    .await;
    let resp = client().chat(&anthropic(&up), &weather_request(false)).await.unwrap();
    let choice = &resp.choices[0];
    assert_eq!(choice.finish_reason.as_deref(), Some("tool_calls"));
    let call = &choice.message.tool_calls.as_ref().unwrap()[0];
    assert_eq!((call.id.as_str(), call.function.name.as_str()), ("toolu_1", "get_weather"));
    assert_eq!(serde_json::from_str::<Value>(&call.function.arguments).unwrap(), json!({"city": "Paris"}));
    let usage = resp.usage.unwrap();
    assert_eq!((usage.prompt_tokens, usage.completion_tokens), (25, 10));

    let r = up.only_request();
    assert_eq!(r.uri, "/v1/messages");
    assert_eq!(r.header("x-api-key"), Some("sk-ant"));
    assert_eq!(r.header("anthropic-version"), Some("2023-06-01"));
    assert_eq!(r.body["system"], json!([{"type": "text", "text": "You are terse."}]));
    assert_eq!(r.body["max_tokens"], 256);
    assert_eq!(r.body["tools"][0]["name"], "get_weather");
    assert_eq!(r.body["tool_choice"], json!({"type": "auto"}));
}

#[tokio::test]
async fn anthropic_stream_with_tool_calls() {
    let up = Upstream::start(vec![Canned::sse(&[
        "event: message_start\ndata: {\"type\":\"message_start\",\"message\":{\"id\":\"msg_s\",\"type\":\"message\",\"role\":\"assistant\",\"model\":\"claude-3-5-sonnet-20241022\",\"content\":[],\"usage\":{\"input_tokens\":30,\"output_tokens\":1}}}\n\n",
        "event: content_block_start\ndata: {\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"text\",\"text\":\"\"}}\n\nevent: ping\ndata: {\"type\":\"ping\"}\n\n",
        "event: content_block_delta\ndata: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"Let me check.\"}}\n\n",
        "event: content_block_stop\ndata: {\"type\":\"content_block_stop\",\"index\":0}\n\n",
        "event: content_block_start\ndata: {\"type\":\"content_block_start\",\"index\":1,\"content_block\":{\"type\":\"tool_use\",\"id\":\"toolu_9\",\"name\":\"get_weather\",\"input\":{}}}\n\n",
        "event: content_block_delta\ndata: {\"type\":\"content_block_delta\",\"index\":1,\"delta\":{\"type\":\"input_json_delta\",\"partial_json\":\"{\\\"ci\"}}\n\nevent: content_block_delta\ndata: {\"type\":\"content_block_delta\",\"index\":1,\"delta\":{\"type\":\"input_json_delta\",\"partial_json\":\"ty\\\": \\\"Paris\\\"}\"}}\n\n",
        "event: content_block_stop\ndata: {\"type\":\"content_block_stop\",\"index\":1}\n\n",
        "event: message_delta\ndata: {\"type\":\"message_delta\",\"delta\":{\"stop_reason\":\"tool_use\",\"stop_sequence\":null},\"usage\":{\"output_tokens\":42}}\n\n",
        "event: message_stop\ndata: {\"type\":\"message_stop\"}\n\n",
    ])])
    .await;
    let chunks = ok_chunks(collect(&client(), &anthropic(&up), &weather_request(true)).await);
    assert_eq!(text_of(&chunks), "Let me check.");
    let args: String = chunks
        .iter()
        .filter_map(|c| c.choices.first()?.delta.tool_calls.as_ref())
        .flatten()
        .filter_map(|d| d.function.as_ref()?.arguments.clone())
        .collect();
    assert_eq!(serde_json::from_str::<Value>(&args).unwrap(), json!({"city": "Paris"}));
    let finish = chunks.iter().find_map(|c| c.choices.first()?.finish_reason.clone());
    assert_eq!(finish.as_deref(), Some("tool_calls"));
    let usage = chunks.last().unwrap().usage.clone().unwrap();
    assert_eq!((usage.prompt_tokens, usage.completion_tokens, usage.total_tokens), (30, 42, 72));
    assert!(chunks.iter().all(|c| c.id == "msg_s"));
    assert_eq!(up.only_request().body["stream"], true);
}

#[tokio::test]
async fn anthropic_stream_error_event() {
    let up = Upstream::start(vec![Canned::sse(&[
        "event: message_start\ndata: {\"type\":\"message_start\",\"message\":{\"id\":\"m\",\"model\":\"c\",\"usage\":{\"input_tokens\":3}}}\n\n",
        "event: error\ndata: {\"type\":\"error\",\"error\":{\"type\":\"overloaded_error\",\"message\":\"Overloaded\"}}\n\n",
    ])])
    .await;
    let items = collect(&client(), &anthropic(&up), &hello()).await;
    assert_eq!(items.len(), 2);
    let err = items.into_iter().last().unwrap().unwrap_err();
    assert_eq!((err.status_code(), err.message()), (529, "Overloaded"));
    assert!(err.is_retryable());
}

// --- Gemini ------------------------------------------------------------------

fn gemini(up: &Upstream) -> Deployment {
    deployment(json!({"model": "gemini/gemini-1.5-pro", "api_key": "g-key", "api_base": up.base}))
}

#[tokio::test]
async fn gemini_chat() {
    let up = Upstream::start(vec![Canned::json(
        200,
        json!({
            "candidates": [{"content": {"role": "model", "parts": [{"text": "Bonjour"}]}, "finishReason": "STOP", "index": 0}],
            "usageMetadata": {"promptTokenCount": 4, "candidatesTokenCount": 2, "totalTokenCount": 6},
            "modelVersion": "gemini-1.5-pro-002"
        }),
    )])
    .await;
    let req = request(json!({"model": "g", "messages": [
        {"role": "system", "content": "French only"}, {"role": "user", "content": "Hello"}
    ], "max_tokens": 20}));
    let resp = client().chat(&gemini(&up), &req).await.unwrap();
    assert_eq!(resp.choices[0].message.text(), "Bonjour");
    assert_eq!(resp.choices[0].finish_reason.as_deref(), Some("stop"));
    assert_eq!(resp.usage.unwrap().total_tokens, 6);
    let r = up.only_request();
    assert_eq!(r.uri, "/v1beta/models/gemini-1.5-pro:generateContent?key=g-key");
    assert_eq!(r.body["systemInstruction"], json!({"parts": [{"text": "French only"}]}));
    assert_eq!(r.body["generationConfig"]["maxOutputTokens"], 20);
}

#[tokio::test]
async fn gemini_stream() {
    let up = Upstream::start(vec![Canned::sse(&[
        "data: {\"candidates\": [{\"content\": {\"role\": \"model\", \"parts\": [{\"text\": \"Bon\"}]}, \"index\": 0}], \"usageMetadata\": {\"promptTokenCount\": 4, \"totalTokenCount\": 4}, \"responseId\": \"r\"}\r\n\r\n",
        "data: {\"candidates\": [{\"content\": {\"role\": \"model\", \"parts\": [{\"text\": \"jour\"}]}, \"finishReason\": \"STOP\", \"index\": 0}], \"usageMetadata\": {\"promptTokenCount\": 4, \"candidatesTokenCount\": 2, \"totalTokenCount\": 6}, \"responseId\": \"r\"}\r\n\r\n",
    ])])
    .await;
    let chunks = ok_chunks(collect(&client(), &gemini(&up), &hello()).await);
    assert_eq!(text_of(&chunks), "Bonjour");
    let last = chunks.last().unwrap();
    assert!(last.is_usage_only());
    assert_eq!(last.usage.as_ref().unwrap().completion_tokens, 2);
    assert_eq!(up.only_request().uri, "/v1beta/models/gemini-1.5-pro:streamGenerateContent?alt=sse&key=g-key");
}

#[tokio::test]
async fn gemini_embeddings() {
    let up = Upstream::start(vec![Canned::json(200, json!({"embeddings": [{"values": [0.5, 0.25]}]}))]).await;
    let dep = deployment(json!({"model": "gemini/text-embedding-004", "api_key": "g", "api_base": up.base}));
    let req: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": ["hello"]})).unwrap();
    let resp = client().embeddings(&dep, &req).await.unwrap();
    assert_eq!(resp.data.len(), 1);
    assert_eq!(up.only_request().uri, "/v1beta/models/text-embedding-004:batchEmbedContents?key=g");
}

// --- Errors ------------------------------------------------------------------

async fn chat_error(canned: Canned, params: impl Fn(&Upstream) -> Deployment) -> ProviderError {
    let up = Upstream::start(vec![canned]).await;
    client().chat(&params(&up), &hello()).await.unwrap_err()
}

fn openai(up: &Upstream) -> Deployment {
    deployment(json!({"model": "openai/gpt-4o", "api_key": "k", "api_base": up.base}))
}

#[tokio::test]
async fn error_classification() {
    let e = chat_error(
        Canned::json(429, json!({"error": {"message": "Rate limit reached", "type": "requests", "code": "rate_limit_exceeded"}}))
            .header("retry-after", "3"),
        openai,
    )
    .await;
    assert_eq!((e.kind(), e.status_code()), (ErrorKind::RateLimited, 429));
    assert!(e.is_retryable());
    assert_eq!(e.retry_after(), Some(Duration::from_secs(3)));
    let body = e.to_openai_body();
    assert_eq!(body.error.message, "Rate limit reached");
    assert_eq!(body.error.code.as_deref(), Some("rate_limit_exceeded"));

    let e = chat_error(
        Canned::json(400, json!({"error": {"message": "Invalid 'messages'", "type": "invalid_request_error", "param": "messages"}})),
        openai,
    )
    .await;
    assert_eq!((e.kind(), e.status_code(), e.is_retryable()), (ErrorKind::BadRequest, 400, false));

    let e = chat_error(Canned::json(401, json!({"error": {"message": "bad key"}})), openai).await;
    assert_eq!((e.kind(), e.is_retryable()), (ErrorKind::Authentication, true));

    let e = chat_error(Canned::json(404, json!({"error": {"message": "no such model"}})), openai).await;
    assert_eq!((e.kind(), e.is_retryable()), (ErrorKind::NotFound, false));

    let e = chat_error(Canned::text(502, "<html>Bad Gateway</html>"), openai).await;
    assert_eq!((e.kind(), e.status_code(), e.is_retryable()), (ErrorKind::ServiceUnavailable, 502, true));

    let e = chat_error(Canned::json(529, json!({"type": "error", "error": {"type": "overloaded_error", "message": "Overloaded"}})), anthropic).await;
    assert_eq!((e.kind(), e.status_code(), e.is_retryable()), (ErrorKind::ServiceUnavailable, 529, true));

    let e = chat_error(
        Canned::json(
            400,
            json!({"error": {"code": 400, "message": "API key not valid. Please pass a valid API key.", "status": "INVALID_ARGUMENT"}}),
        ),
        gemini,
    )
    .await;
    assert_eq!((e.kind(), e.status_code()), (ErrorKind::Authentication, 401));
    assert!(!e.message().contains("g-key"));

    let e = chat_error(Canned::text(200, "not json"), openai).await;
    assert_eq!((e.kind(), e.is_retryable()), (ErrorKind::InvalidResponse, true));

    // Errors before the stream starts are returned from chat_stream itself.
    let up = Upstream::start(vec![Canned::json(503, json!({"error": {"message": "busy"}}))]).await;
    let Err(e) = client().chat_stream(&openai(&up), &hello()).await else { panic!("expected error") };
    assert_eq!(e.status_code(), 503);
}

#[tokio::test]
async fn connection_refused() {
    let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    drop(listener);
    let dep = deployment(json!({"model": "openai/gpt-4o", "api_key": "k", "api_base": format!("http://{addr}")}));
    let e = client().chat(&dep, &hello()).await.unwrap_err();
    assert_eq!((e.kind(), e.is_retryable()), (ErrorKind::Connection, true));
}

#[tokio::test]
async fn timeouts() {
    let slow = Canned::json(200, json!({})).delayed(Duration::from_millis(500));
    let e = chat_error(slow, |up| deployment(json!({"model": "openai/gpt-4o", "api_key": "k", "api_base": up.base, "timeout": 0.1}))).await;
    assert_eq!((e.kind(), e.status_code(), e.is_retryable()), (ErrorKind::Timeout, 408, true));

    // Stream stalls between events.
    let stall = Canned::sse(&["data: {\"id\":\"c\",\"choices\":[{\"index\":0,\"delta\":{\"content\":\"a\"}}]}\n\n", "data: [DONE]\n\n"])
        .delayed(Duration::from_millis(300));
    let up = Upstream::start(vec![stall]).await;
    let dep = deployment(json!({"model": "openai/gpt-4o", "api_key": "k", "api_base": up.base, "stream_timeout": 0.1}));
    let items = collect(&client(), &dep, &hello()).await;
    let err = items.into_iter().find_map(Result::err).expect("stream must time out");
    assert_eq!(err.kind(), ErrorKind::Timeout);
}

// --- Mock --------------------------------------------------------------------

#[tokio::test]
async fn mock_response_skips_the_network() {
    // api_base points nowhere: any network access would fail.
    let dep = deployment(json!({"model": "openai/gpt-4o", "api_key": "k", "api_base": "http://127.0.0.1:1"}));
    let mut req = hello();
    req.mock_response = Some("canned answer".into());
    let resp = client().chat(&dep, &req).await.unwrap();
    assert_eq!(resp.choices[0].message.text(), "canned answer");
    assert!(resp.usage.unwrap().completion_tokens > 0);

    let chunks = ok_chunks(collect(&client(), &dep, &req).await);
    assert_eq!(text_of(&chunks), "canned answer");
    assert!(chunks.last().unwrap().is_usage_only());

    let fake = deployment(json!({"model": "fake/test-model"}));
    let resp = client().chat(&fake, &hello()).await.unwrap();
    assert_eq!(resp.model, "test-model");
    let e = client().chat(&deployment(json!({"model": "mock/m", "mock_response": "litellm.RateLimitError"})), &hello()).await.unwrap_err();
    assert!(e.is_retryable());
    let ereq: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": "x"})).unwrap();
    assert_eq!(client().embeddings(&fake, &ereq).await.unwrap().data.len(), 1);
}

#[tokio::test]
async fn anthropic_has_no_embeddings() {
    let dep = deployment(json!({"model": "anthropic/claude-3-5-sonnet-20241022", "api_key": "k"}));
    let ereq: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": "x"})).unwrap();
    let e = client().embeddings(&dep, &ereq).await.unwrap_err();
    assert_eq!(e.kind(), ErrorKind::BadRequest);
}
