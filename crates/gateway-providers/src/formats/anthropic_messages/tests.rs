use super::*;
use crate::Deployment;
use crate::formats::{Target, adapt_to_target};
use crate::types::{Delta, FunctionCallDelta, PromptTokensDetails, ToolCallDelta};

fn req(v: Value) -> MessagesRequest {
    serde_json::from_value(v).unwrap()
}

fn chat(v: Value) -> Value {
    serde_json::to_value(to_chat_request(&req(v)).unwrap()).unwrap()
}

fn err(v: Value) -> FormatError {
    to_chat_request(&req(v)).unwrap_err()
}

#[test]
fn basics() {
    let c = chat(json!({
        "model": "claude", "max_tokens": 100, "system": "Be brief.",
        "messages": [{"role": "user", "content": "Hi"}],
        "temperature": 0.5, "top_p": 0.9, "top_k": 4, "stop_sequences": ["END"],
        "metadata": {"user_id": "u-7"}
    }));
    assert_eq!(
        c,
        json!({
            "model": "claude",
            "messages": [{"role": "system", "content": "Be brief."}, {"role": "user", "content": "Hi"}],
            "temperature": 0.5, "top_p": 0.9, "stop": ["END"], "max_completion_tokens": 100,
            "user": "u-7", "top_k": 4
        })
    );
}

#[test]
fn system_blocks_keep_cache_control() {
    let c = chat(json!({
        "model": "m",
        "system": [{"type": "text", "text": "A"}, {"type": "text", "text": "B", "cache_control": {"type": "ephemeral"}}],
        "messages": [{"role": "user", "content": [{"type": "text", "text": "q", "cache_control": {"type": "ephemeral"}}]}]
    }));
    assert_eq!(
        c["messages"][0]["content"],
        json!([{"type": "text", "text": "A"}, {"type": "text", "text": "B", "cache_control": {"type": "ephemeral"}}])
    );
    assert_eq!(
        c["messages"][1]["content"][0]["cache_control"]["type"],
        "ephemeral"
    );
    // One plain block becomes a string.
    let c = chat(json!({"model": "m", "system": [{"type": "text", "text": "A"}], "messages": []}));
    assert_eq!(c["messages"][0], json!({"role": "system", "content": "A"}));
}

#[test]
fn images_and_documents() {
    let c = chat(
        json!({"model": "m", "messages": [{"role": "user", "content": [
            {"type": "image", "source": {"type": "base64", "media_type": "image/png", "data": "iVBO"}},
            {"type": "image", "source": {"type": "url", "url": "https://x/cat.jpg"}},
            {"type": "document", "title": "spec.pdf", "source": {"type": "base64", "media_type": "application/pdf", "data": "JVBE"}},
            {"type": "document", "title": "Notes", "source": {"type": "text", "media_type": "text/plain", "data": "hello"}},
            {"type": "document", "source": {"type": "file", "file_id": "file_1"}},
            {"type": "document", "source": {"type": "url", "url": "https://x/a.pdf"}},
            {"type": "text", "text": "Describe"}
        ]}]}),
    );
    let parts = &c["messages"][0]["content"];
    assert_eq!(
        parts[0],
        json!({"type": "image_url", "image_url": {"url": "data:image/png;base64,iVBO"}})
    );
    assert_eq!(
        parts[1],
        json!({"type": "image_url", "image_url": {"url": "https://x/cat.jpg"}})
    );
    assert_eq!(
        parts[2],
        json!({"type": "file", "file": {"file_data": "data:application/pdf;base64,JVBE", "filename": "spec.pdf"}})
    );
    assert_eq!(parts[3], json!({"type": "text", "text": "Notes\n\nhello"}));
    assert_eq!(
        parts[4],
        json!({"type": "file", "file": {"file_id": "file_1"}})
    );
    // URL documents pass through natively.
    assert_eq!(
        parts[5],
        json!({"type": "document", "source": {"type": "url", "url": "https://x/a.pdf"}})
    );
    assert_eq!(parts[6], json!({"type": "text", "text": "Describe"}));
}

#[test]
fn tool_use_conversation() {
    let c = chat(json!({"model": "m", "messages": [
        {"role": "user", "content": "Weather in Paris?"},
        {"role": "assistant", "content": [
            {"type": "thinking", "thinking": "need tool", "signature": "sig"},
            {"type": "text", "text": "Checking."},
            {"type": "tool_use", "id": "toolu_1", "name": "get_weather", "input": {"city": "Paris"}}
        ]},
        {"role": "user", "content": [
            {"type": "text", "text": "Here:"},
            {"type": "tool_result", "tool_use_id": "toolu_1", "content": [{"type": "text", "text": "18C"}, {"type": "text", "text": "sunny"}]},
            {"type": "tool_result", "tool_use_id": "toolu_2", "content": "err", "is_error": true}
        ]}
    ]}));
    let m = c["messages"].as_array().unwrap();
    assert_eq!(m.len(), 5);
    assert_eq!(m[1]["role"], "assistant");
    assert_eq!(m[1]["content"], "Checking.");
    assert_eq!(
        m[1]["tool_calls"],
        json!([{"id": "toolu_1", "type": "function", "function": {"name": "get_weather", "arguments": "{\"city\":\"Paris\"}"}}])
    );
    assert_eq!(m[1]["thinking_blocks"][0]["signature"], "sig");
    // Tool results first, then the rest of the user turn.
    assert_eq!(
        m[2],
        json!({"role": "tool", "content": "18C\nsunny", "tool_call_id": "toolu_1"})
    );
    assert_eq!(
        m[3],
        json!({"role": "tool", "content": "err", "tool_call_id": "toolu_2"})
    );
    assert_eq!(m[4], json!({"role": "user", "content": "Here:"}));
}

#[test]
fn tool_result_with_image_keeps_parts() {
    let c = chat(
        json!({"model": "m", "messages": [{"role": "user", "content": [
            {"type": "tool_result", "tool_use_id": "t", "content": [
                {"type": "text", "text": "chart"},
                {"type": "image", "source": {"type": "base64", "media_type": "image/png", "data": "AA"}}
            ]}
        ]}]}),
    );
    assert_eq!(
        c["messages"][0]["content"][1]["image_url"]["url"],
        "data:image/png;base64,AA"
    );
}

#[test]
fn tools_and_tool_choice() {
    let c = chat(
        json!({"model": "m", "messages": [{"role": "user", "content": "x"}],
        "tools": [
            {"name": "get_weather", "description": "Weather", "input_schema": {"type": "object", "properties": {"city": {"type": "string"}}}, "cache_control": {"type": "ephemeral"}},
            {"type": "web_search_20250305", "name": "web_search", "max_uses": 3}
        ],
        "tool_choice": {"type": "any", "disable_parallel_tool_use": true}}),
    );
    assert_eq!(
        c["tools"][0],
        json!({"type": "function", "function": {"name": "get_weather", "description": "Weather",
               "parameters": {"type": "object", "properties": {"city": {"type": "string"}}}},
               "cache_control": {"type": "ephemeral"}})
    );
    assert_eq!(
        c["tools"][1],
        json!({"type": "web_search_20250305", "name": "web_search", "max_uses": 3})
    );
    assert_eq!(c["tool_choice"], "required");
    assert_eq!(c["parallel_tool_calls"], false);
    let tc = |v: Value| {
        chat(json!({"model": "m", "messages": [], "tool_choice": v}))["tool_choice"].clone()
    };
    assert_eq!(tc(json!({"type": "auto"})), "auto");
    assert_eq!(tc(json!({"type": "none"})), "none");
    assert_eq!(
        tc(json!({"type": "tool", "name": "f"})),
        json!({"type": "function", "function": {"name": "f"}})
    );
}

#[test]
fn thinking_and_streaming_options() {
    let c = chat(json!({"model": "m", "messages": [], "stream": true,
        "thinking": {"type": "enabled", "budget_tokens": 5000}, "service_tier": "auto", "unknown_field": 1}));
    assert_eq!(c["reasoning_effort"], "high");
    assert_eq!(
        c["thinking"],
        json!({"type": "enabled", "budget_tokens": 5000})
    );
    assert_eq!(c["stream"], true);
    assert_eq!(c["stream_options"], json!({"include_usage": true}));
    assert_eq!(c["service_tier"], "auto");
    assert!(c.get("unknown_field").is_none());
    assert_eq!(effort_for_budget(1024), "low");
    assert_eq!(effort_for_budget(2048), "medium");
    let c = chat(json!({"model": "m", "messages": [], "thinking": {"type": "disabled"}}));
    assert!(c.get("reasoning_effort").is_none());
}

#[test]
fn invalid_requests() {
    let e = err(json!({"model": "m", "messages": [{"role": "system", "content": "x"}]}));
    assert_eq!(e.param.as_deref(), Some("messages.0.role"));
    let e = err(json!({"model": "m", "messages": [{"role": "user", "content": 5}]}));
    assert!(e.message.contains("messages.0.content"), "{e}");
    let e = err(
        json!({"model": "m", "messages": [{"role": "user", "content": [{"text": "no type"}]}]}),
    );
    assert!(e.message.contains("type"), "{e}");
    let e = err(
        json!({"model": "m", "messages": [{"role": "user", "content": [{"type": "tool_result", "content": "x"}]}]}),
    );
    assert_eq!(e.param.as_deref(), Some("messages.0.content.0.tool_use_id"));
    let e = err(json!({"model": "m", "messages": [], "tool_choice": {"type": "sometimes"}}));
    assert_eq!(e.param.as_deref(), Some("tool_choice"));
    let e = err(json!({"model": "m", "messages": [], "tools": [{"description": "nameless"}]}));
    assert_eq!(e.param.as_deref(), Some("tools.0.name"));
    let e = err(
        json!({"model": "m", "messages": [{"role": "user", "content": [{"type": "image", "source": {"type": "base64"}}]}]}),
    );
    assert!(e.message.contains("media_type"), "{e}");
    assert!(serde_json::from_value::<MessagesRequest>(json!({"messages": []})).is_err());
}

#[test]
fn count_tokens_estimates_the_prompt() {
    let small = count_tokens(&req(
        json!({"model": "m", "messages": [{"role": "user", "content": "Hi"}]}),
    ))
    .unwrap();
    let big = count_tokens(&req(
        json!({"model": "m", "messages": [{"role": "user", "content": "Hi ".repeat(400)}]}),
    ))
    .unwrap();
    assert!(small > 0 && big > small + 250, "{small} {big}");
}

/// What the Anthropic adapter sends upstream is the client's request again.
#[test]
fn native_fields_survive_the_anthropic_adapter() {
    let dep = Deployment::from_litellm_params_with_env(
        &json!({"model": "anthropic/claude-sonnet-4-5", "api_key": "k"}),
        |_| None,
    )
    .unwrap();
    let original = json!({
        "model": "claude", "max_tokens": 3000,
        "system": [{"type": "text", "text": "S", "cache_control": {"type": "ephemeral"}}],
        "messages": [
            {"role": "user", "content": [{"type": "text", "text": "Weather?"}]},
            {"role": "assistant", "content": [
                {"type": "thinking", "thinking": "hmm", "signature": "sig"},
                {"type": "tool_use", "id": "toolu_1", "name": "w", "input": {"c": "P"}}
            ]},
            {"role": "user", "content": [{"type": "tool_result", "tool_use_id": "toolu_1", "content": "18C"}]}
        ],
        "tools": [{"name": "w", "input_schema": {"type": "object"}}],
        "thinking": {"type": "enabled", "budget_tokens": 2000},
        "top_k": 5
    });
    let mut c = to_chat_request(&req(original.clone())).unwrap();
    adapt_to_target(&mut c, Target::of(&dep));
    let body = crate::providers::anthropic::chat_request(&dep, &c, false)
        .unwrap()
        .body;
    assert_eq!(body["system"], original["system"]);
    assert_eq!(body["messages"], original["messages"]);
    assert_eq!(body["thinking"], original["thinking"]);
    assert_eq!(body["top_k"], 5);
    assert_eq!(body["max_tokens"], 3000);
    assert_eq!(
        body["tools"],
        json!([{"name": "w", "input_schema": {"type": "object"}}])
    );
}

fn response(v: Value) -> ChatResponse {
    serde_json::from_value(v).unwrap()
}

#[test]
fn text_response() {
    let r = response(json!({"id": "chatcmpl-abc", "model": "gpt-4o", "choices": [
        {"index": 0, "message": {"role": "assistant", "content": "Hello!"}, "finish_reason": "stop"}],
        "usage": {"prompt_tokens": 12, "completion_tokens": 3, "total_tokens": 15}}));
    assert_eq!(
        from_chat_response(&r, "claude"),
        json!({
            "id": "msg_abc", "type": "message", "role": "assistant", "model": "claude",
            "content": [{"type": "text", "text": "Hello!"}],
            "stop_reason": "end_turn", "stop_sequence": null,
            "usage": {"input_tokens": 12, "output_tokens": 3, "cache_creation_input_tokens": 0, "cache_read_input_tokens": 0}
        })
    );
}

#[test]
fn tool_and_thinking_response() {
    let r = response(
        json!({"id": "x", "model": "m", "choices": [{"index": 0, "message": {
        "role": "assistant", "content": null, "reasoning_content": "think",
        "tool_calls": [{"id": "call_1", "type": "function", "function": {"name": "f", "arguments": "{\"a\":1}"}},
                       {"id": "call_2", "type": "function", "function": {"name": "g", "arguments": ""}}]},
        "finish_reason": "tool_calls"}]}),
    );
    let m = from_chat_response(&r, "m");
    assert_eq!(
        m["content"],
        json!([
            {"type": "thinking", "thinking": "think", "signature": ""},
            {"type": "tool_use", "id": "call_1", "name": "f", "input": {"a": 1}},
            {"type": "tool_use", "id": "call_2", "name": "g", "input": {}}
        ])
    );
    assert_eq!(m["stop_reason"], "tool_use");
    // Thinking blocks from Anthropic come back with their signatures.
    let r = response(
        json!({"id": "msg_1", "model": "m", "choices": [{"index": 0, "message": {
        "role": "assistant", "content": "ok", "reasoning_content": "t",
        "thinking_blocks": [{"type": "thinking", "thinking": "t", "signature": "s"}]}, "finish_reason": "length"}]}),
    );
    let m = from_chat_response(&r, "m");
    assert_eq!(m["id"], "msg_1");
    assert_eq!(m["content"][0]["signature"], "s");
    assert_eq!(m["stop_reason"], "max_tokens");
}

#[test]
fn usage_excludes_cache() {
    let u = Usage {
        cache_read_input_tokens: Some(30),
        prompt_tokens_details: Some(PromptTokensDetails {
            cache_creation_tokens: Some(10),
            ..Default::default()
        }),
        ..Usage::new(100, 7)
    };
    assert_eq!(
        usage(&u),
        json!({"input_tokens": 60, "output_tokens": 7, "cache_creation_input_tokens": 10, "cache_read_input_tokens": 30})
    );
    assert_eq!(stop_reason(Some("content_filter")), "refusal");
    assert_eq!(stop_reason(None), "end_turn");
}

#[test]
fn errors() {
    assert_eq!(
        error_body(429, "slow down"),
        json!({"type": "error", "error": {"type": "rate_limit_error", "message": "slow down"}})
    );
    for (s, t) in [
        (400, "invalid_request_error"),
        (401, "authentication_error"),
        (403, "permission_error"),
        (404, "not_found_error"),
        (413, "request_too_large"),
        (500, "api_error"),
        (529, "overloaded_error"),
        (503, "overloaded_error"),
    ] {
        assert_eq!(error_type(s), t);
    }
}

fn chunk(delta: Delta, finish: Option<&str>) -> ChatChunk {
    ChatChunk::new("chatcmpl-1", "up", 0).with_delta(delta, finish.map(str::to_owned))
}

fn text(t: &str) -> Delta {
    Delta {
        content: Some(t.into()),
        ..Delta::default()
    }
}

fn types(events: &[Value]) -> Vec<String> {
    events
        .iter()
        .map(|e| match e["type"].as_str().unwrap() {
            "content_block_delta" => format!("delta:{}", e["delta"]["type"].as_str().unwrap()),
            t => t.to_owned(),
        })
        .collect()
}

fn run(chunks: &[ChatChunk]) -> Vec<Value> {
    let mut s = MessagesStream::new("claude", 9);
    let mut events: Vec<Value> = chunks.iter().flat_map(|c| s.on_chunk(c)).collect();
    events.extend(s.finish());
    events
}

#[test]
fn text_stream() {
    let events = run(&[
        chunk(
            Delta {
                role: Some(crate::types::Role::Assistant),
                content: Some(String::new()),
                ..Delta::default()
            },
            None,
        ),
        chunk(text("Hel"), None),
        chunk(text("lo"), None),
        chunk(Delta::default(), Some("stop")),
        ChatChunk::new("chatcmpl-1", "up", 0).with_usage(Usage::new(11, 2)),
    ]);
    assert_eq!(
        types(&events),
        [
            "message_start",
            "ping",
            "content_block_start",
            "delta:text_delta",
            "delta:text_delta",
            "content_block_stop",
            "message_delta",
            "message_stop"
        ]
    );
    assert_eq!(events[0]["message"]["id"], "msg_1");
    assert_eq!(events[0]["message"]["model"], "claude");
    assert_eq!(events[0]["message"]["usage"]["input_tokens"], 9);
    assert_eq!(
        events[2]["content_block"],
        json!({"type": "text", "text": ""})
    );
    assert_eq!(events[3]["delta"]["text"], "Hel");
    assert_eq!(events[6]["delta"]["stop_reason"], "end_turn");
    assert_eq!(events[6]["usage"]["input_tokens"], 11);
    assert_eq!(events[6]["usage"]["output_tokens"], 2);
}

fn tool_delta(index: u32, id: Option<&str>, name: Option<&str>, args: &str) -> Delta {
    Delta {
        tool_calls: Some(vec![ToolCallDelta {
            index,
            id: id.map(str::to_owned),
            kind: id.map(|_| "function".to_owned()),
            function: Some(FunctionCallDelta {
                name: name.map(str::to_owned),
                arguments: Some(args.into()),
            }),
        }]),
        ..Delta::default()
    }
}

#[test]
fn thinking_text_and_tool_stream() {
    let events = run(&[
        chunk(
            Delta {
                reasoning_content: Some("Let me".into()),
                ..Delta::default()
            },
            None,
        ),
        chunk(
            Delta {
                reasoning_content: Some(" think".into()),
                ..Delta::default()
            },
            None,
        ),
        chunk(text("Calling."), None),
        chunk(tool_delta(0, Some("call_a"), Some("f"), ""), None),
        chunk(tool_delta(0, None, None, "{\"x\":"), None),
        chunk(tool_delta(0, None, None, "1}"), None),
        chunk(tool_delta(1, Some("call_b"), Some("g"), "{}"), None),
        chunk(Delta::default(), Some("tool_calls")),
    ]);
    assert_eq!(
        types(&events),
        [
            "message_start",
            "ping",
            "content_block_start",
            "delta:thinking_delta",
            "delta:thinking_delta",
            "content_block_stop",
            "content_block_start",
            "delta:text_delta",
            "content_block_stop",
            "content_block_start",
            "delta:input_json_delta",
            "delta:input_json_delta",
            "content_block_stop",
            "content_block_start",
            "delta:input_json_delta",
            "content_block_stop",
            "message_delta",
            "message_stop"
        ]
    );
    let starts: Vec<&Value> = events
        .iter()
        .filter(|e| e["type"] == "content_block_start")
        .collect();
    assert_eq!(starts[0]["content_block"]["type"], "thinking");
    assert_eq!(
        starts[2]["content_block"],
        json!({"type": "tool_use", "id": "call_a", "name": "f", "input": {}})
    );
    assert_eq!(starts[3]["index"], 3);
    assert_eq!(events[10]["delta"]["partial_json"], "{\"x\":");
    assert_eq!(events[10]["index"], 2);
    assert_eq!(events[16]["delta"]["stop_reason"], "tool_use");
    // No usage from upstream: estimated.
    assert_eq!(events[16]["usage"]["input_tokens"], 9);
    assert!(events[16]["usage"]["output_tokens"].as_u64().unwrap() > 0);
}

#[test]
fn empty_and_failed_streams() {
    let events = run(&[]);
    assert_eq!(
        types(&events),
        ["message_start", "ping", "message_delta", "message_stop"]
    );
    let mut s = MessagesStream::new("m", 1);
    let mut events = s.on_chunk(&chunk(text("partial"), None));
    events.extend(s.error(529, "overloaded"));
    events.extend(s.finish());
    assert_eq!(
        types(&events),
        [
            "message_start",
            "ping",
            "content_block_start",
            "delta:text_delta",
            "error"
        ]
    );
    assert_eq!(
        events[4]["error"],
        json!({"type": "overloaded_error", "message": "overloaded"})
    );
}

#[test]
fn length_stop_and_sse_encoding() {
    let events = run(&[
        chunk(text("a"), None),
        chunk(Delta::default(), Some("length")),
    ]);
    assert_eq!(
        events[events.len() - 2]["delta"]["stop_reason"],
        "max_tokens"
    );
    let sse = encode_events(&events[..2]);
    assert!(sse.starts_with("event: message_start\ndata: {"), "{sse}");
    assert!(
        sse.ends_with("event: ping\ndata: {\"type\":\"ping\"}\n\n"),
        "{sse}"
    );
}
