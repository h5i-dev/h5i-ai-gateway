use super::*;
use crate::types::{
    CompletionTokensDetails, Delta, FunctionCallDelta, PromptTokensDetails, ToolCallDelta,
};

fn req(v: Value) -> ResponsesRequest {
    serde_json::from_value(v).unwrap()
}

fn chat(v: Value) -> Value {
    serde_json::to_value(to_chat_request(&req(v), &[]).unwrap().chat).unwrap()
}

fn err(v: Value) -> FormatError {
    to_chat_request(&req(v), &[]).unwrap_err()
}

fn rid() -> ResponseId {
    ResponseId {
        id: "resp_1".into(),
        created_at: 42,
    }
}

#[test]
fn string_input_and_parameters() {
    let c = chat(json!({
        "model": "gpt", "input": "Hi", "instructions": "Be brief.", "max_output_tokens": 50,
        "temperature": 0.2, "top_p": 0.8, "reasoning": {"effort": "low"}, "parallel_tool_calls": false,
        "user": "u", "store": false, "metadata": {"k": "v"}
    }));
    assert_eq!(
        c,
        json!({
            "model": "gpt",
            "messages": [{"role": "system", "content": "Be brief."}, {"role": "user", "content": "Hi"}],
            "temperature": 0.2, "top_p": 0.8, "max_completion_tokens": 50, "user": "u",
            "parallel_tool_calls": false, "reasoning_effort": "low"
        })
    );
}

#[test]
fn item_input_with_parts_and_tools() {
    let c = chat(json!({"model": "m", "input": [
        {"role": "developer", "content": "dev"},
        {"type": "message", "role": "user", "content": [
            {"type": "input_text", "text": "What is this?"},
            {"type": "input_image", "image_url": "data:image/png;base64,AA", "detail": "low"},
            {"type": "input_image", "image_url": "https://x/y.png", "detail": "auto"},
            {"type": "input_file", "filename": "a.pdf", "file_data": "data:application/pdf;base64,JV"},
            {"type": "input_file", "file_id": "file-1"}
        ]},
        {"type": "message", "role": "assistant", "content": [{"type": "output_text", "text": "Let me check."}]},
        {"type": "function_call", "call_id": "call_1", "name": "lookup", "arguments": "{\"q\":1}"},
        {"type": "function_call", "call_id": "call_2", "name": "lookup", "arguments": "{\"q\":2}"},
        {"type": "reasoning", "id": "rs_1", "summary": []},
        {"type": "function_call_output", "call_id": "call_1", "output": "one"},
        {"type": "function_call_output", "call_id": "call_2", "output": [{"type": "input_text", "text": "two"}]}
    ]}));
    let m = c["messages"].as_array().unwrap();
    assert_eq!(m.len(), 5);
    assert_eq!(m[0], json!({"role": "developer", "content": "dev"}));
    assert_eq!(
        m[1]["content"],
        json!([
            {"type": "text", "text": "What is this?"},
            {"type": "image_url", "image_url": {"url": "data:image/png;base64,AA", "detail": "low"}},
            {"type": "image_url", "image_url": {"url": "https://x/y.png"}},
            {"type": "file", "file": {"file_data": "data:application/pdf;base64,JV", "filename": "a.pdf"}},
            {"type": "file", "file": {"file_id": "file-1"}}
        ])
    );
    // Calls join the assistant turn before them.
    assert_eq!(m[2]["content"], "Let me check.");
    assert_eq!(m[2]["tool_calls"].as_array().unwrap().len(), 2);
    assert_eq!(
        m[2]["tool_calls"][1]["function"],
        json!({"name": "lookup", "arguments": "{\"q\":2}"})
    );
    assert_eq!(
        m[3],
        json!({"role": "tool", "content": "one", "tool_call_id": "call_1"})
    );
    assert_eq!(
        m[4],
        json!({"role": "tool", "content": "two", "tool_call_id": "call_2"})
    );
}

#[test]
fn a_call_without_a_preceding_message_opens_an_assistant_turn() {
    let c = chat(json!({"model": "m", "input": [
        {"role": "user", "content": "x"},
        {"type": "function_call", "call_id": "c", "name": "f", "arguments": "{}"}
    ]}));
    assert_eq!(
        c["messages"][1],
        json!({"role": "assistant", "tool_calls": [{"id": "c", "type": "function", "function": {"name": "f", "arguments": "{}"}}]})
    );
}

#[test]
fn tools_choice_and_formats() {
    let c = chat(json!({"model": "m", "input": "x",
        "tools": [{"type": "function", "name": "f", "description": "d", "parameters": {"type": "object"}, "strict": true}],
        "tool_choice": {"type": "function", "name": "f"},
        "text": {"format": {"type": "json_schema", "name": "out", "schema": {"type": "object"}, "strict": true}}}));
    assert_eq!(
        c["tools"],
        json!([{"type": "function", "function": {"name": "f", "description": "d", "parameters": {"type": "object"}, "strict": true}}])
    );
    assert_eq!(
        c["tool_choice"],
        json!({"type": "function", "function": {"name": "f"}})
    );
    assert_eq!(
        c["response_format"],
        json!({"type": "json_schema", "json_schema": {"name": "out", "schema": {"type": "object"}, "strict": true}})
    );
    let c = chat(
        json!({"model": "m", "input": "x", "tool_choice": "required", "text": {"format": {"type": "json_object"}}}),
    );
    assert_eq!(c["tool_choice"], "required");
    assert_eq!(c["response_format"], json!({"type": "json_object"}));
    let c = chat(
        json!({"model": "m", "input": "x", "text": {"format": {"type": "text"}}, "stream": true}),
    );
    assert!(c.get("response_format").is_none());
    assert_eq!(c["stream_options"], json!({"include_usage": true}));
}

#[test]
fn history_goes_before_the_input_and_instructions_are_not_kept() {
    let history = vec![ChatMessage::user("first"), ChatMessage::assistant("answer")];
    let t = to_chat_request(
        &req(json!({"model": "m", "input": "second", "instructions": "sys"})),
        &history,
    )
    .unwrap();
    let roles: Vec<Role> = t.chat.messages.iter().map(|m| m.role).collect();
    assert_eq!(
        roles,
        [Role::System, Role::User, Role::Assistant, Role::User]
    );
    assert_eq!(t.conversation.len(), 3);
    assert!(t.conversation.iter().all(|m| m.role != Role::System));
}

#[test]
fn invalid_requests() {
    assert_eq!(
        err(json!({"model": "m", "input": "x", "tools": [{"type": "web_search_preview"}]}))
            .param
            .as_deref(),
        Some("tools.0.type")
    );
    assert_eq!(
        err(json!({"model": "m", "input": 5})).param.as_deref(),
        Some("input")
    );
    assert_eq!(
        err(json!({"model": "m", "input": [{"type": "item_reference", "id": "x"}]}))
            .param
            .as_deref(),
        Some("input.0.type")
    );
    assert_eq!(
        err(json!({"model": "m", "input": [{"type": "function_call_output", "output": "x"}]}))
            .param
            .as_deref(),
        Some("input.0.call_id")
    );
    assert_eq!(
        err(json!({"model": "m", "input": [{"role": "tool", "content": "x"}]}))
            .param
            .as_deref(),
        Some("input.0.role")
    );
    assert_eq!(err(json!({"model": "m", "input": [{"role": "user", "content": [{"type": "input_file", "file_url": "https://x"}]}]})).param.as_deref(), Some("input.0.content.0.file_url"));
    assert_eq!(
        err(
            json!({"model": "m", "input": [{"role": "user", "content": [{"type": "input_image"}]}]})
        )
        .param
        .as_deref(),
        Some("input.0.content.0.image_url")
    );
    assert_eq!(
        err(json!({"model": "m", "input": "x", "tool_choice": {"type": "file_search"}}))
            .param
            .as_deref(),
        Some("tool_choice")
    );
    assert_eq!(
        err(json!({"model": "m", "input": "x", "text": {"format": {"type": "yaml"}}}))
            .param
            .as_deref(),
        Some("text.format.type")
    );
    assert_eq!(
        err(json!({"model": "m", "input": "x", "background": true}))
            .param
            .as_deref(),
        Some("background")
    );
}

fn response(v: Value) -> ChatResponse {
    serde_json::from_value(v).unwrap()
}

#[test]
fn text_response() {
    let r =
        req(json!({"model": "gpt", "input": "Hi", "instructions": "sys", "max_output_tokens": 9}));
    let resp = response(
        json!({"id": "c", "model": "up", "choices": [{"index": 0, "message": {"role": "assistant", "content": "Hello"}, "finish_reason": "stop"}],
        "usage": {"prompt_tokens": 10, "completion_tokens": 2, "total_tokens": 12}}),
    );
    let o = from_chat_response(&r, &rid(), &resp);
    assert_eq!(o["id"], "resp_1");
    assert_eq!(o["object"], "response");
    assert_eq!(o["created_at"], 42);
    assert_eq!(o["status"], "completed");
    assert_eq!(o["model"], "gpt");
    assert_eq!(o["instructions"], "sys");
    assert_eq!(o["max_output_tokens"], 9);
    assert_eq!(o["store"], true);
    assert_eq!(o["incomplete_details"], Value::Null);
    let out = o["output"].as_array().unwrap();
    assert_eq!(out.len(), 1);
    assert_eq!(out[0]["type"], "message");
    assert_eq!(out[0]["role"], "assistant");
    assert_eq!(out[0]["status"], "completed");
    assert!(out[0]["id"].as_str().unwrap().starts_with("msg_"));
    assert_eq!(
        out[0]["content"],
        json!([{"type": "output_text", "text": "Hello", "annotations": []}])
    );
    assert_eq!(
        o["usage"],
        json!({"input_tokens": 10, "input_tokens_details": {"cached_tokens": 0}, "output_tokens": 2,
               "output_tokens_details": {"reasoning_tokens": 0}, "total_tokens": 12})
    );
}

#[test]
fn tool_reasoning_and_incomplete_responses() {
    let r = req(json!({"model": "m", "input": "x"}));
    let resp = response(
        json!({"id": "c", "model": "up", "choices": [{"index": 0, "message": {"role": "assistant", "content": null,
        "reasoning_content": "thought", "tool_calls": [{"id": "call_9", "type": "function", "function": {"name": "f", "arguments": "{\"a\":1}"}}]},
        "finish_reason": "tool_calls"}]}),
    );
    let o = from_chat_response(&r, &rid(), &resp);
    let out = o["output"].as_array().unwrap();
    assert_eq!(out[0]["type"], "reasoning");
    assert_eq!(
        out[0]["summary"],
        json!([{"type": "summary_text", "text": "thought"}])
    );
    assert_eq!(out[1]["type"], "function_call");
    assert_eq!(out[1]["call_id"], "call_9");
    assert_eq!(out[1]["arguments"], "{\"a\":1}");
    assert_eq!(out[1]["status"], "completed");
    assert_eq!(o["usage"], Value::Null);
    let resp = response(
        json!({"id": "c", "model": "up", "choices": [{"index": 0, "message": {"role": "assistant", "content": "trunc"}, "finish_reason": "length"}]}),
    );
    let o = from_chat_response(&r, &rid(), &resp);
    assert_eq!(o["status"], "incomplete");
    assert_eq!(
        o["incomplete_details"],
        json!({"reason": "max_output_tokens"})
    );
}

#[test]
fn usage_details() {
    let u = Usage {
        prompt_tokens_details: Some(PromptTokensDetails {
            cached_tokens: Some(4),
            ..Default::default()
        }),
        completion_tokens_details: Some(CompletionTokensDetails {
            reasoning_tokens: Some(3),
            ..Default::default()
        }),
        ..Usage::new(10, 5)
    };
    let v = usage(&u);
    assert_eq!(v["input_tokens_details"]["cached_tokens"], 4);
    assert_eq!(v["output_tokens_details"]["reasoning_tokens"], 3);
    assert_eq!(v["total_tokens"], 15);
}

#[test]
fn output_becomes_the_next_turns_history() {
    let r = req(json!({"model": "m", "input": "x"}));
    let resp = response(
        json!({"id": "c", "model": "up", "choices": [{"index": 0, "message": {"role": "assistant", "content": "calling",
        "tool_calls": [{"id": "call_1", "type": "function", "function": {"name": "f", "arguments": "{}"}}]}, "finish_reason": "tool_calls"}]}),
    );
    let o = from_chat_response(&r, &rid(), &resp);
    let blocks = json!([{"type": "thinking", "thinking": "t", "signature": "s"}]);
    let msgs = output_messages(&o, Some(&blocks));
    assert_eq!(msgs.len(), 1);
    assert_eq!(msgs[0].role, Role::Assistant);
    assert_eq!(msgs[0].text(), "calling");
    assert_eq!(msgs[0].tool_calls.as_ref().unwrap()[0].id, "call_1");
    assert_eq!(msgs[0].extra["thinking_blocks"], blocks);
    // The next turn answers the call.
    let next = req(
        json!({"model": "m", "input": [{"type": "function_call_output", "call_id": "call_1", "output": "42"}]}),
    );
    let t = to_chat_request(&next, &msgs).unwrap();
    assert_eq!(t.chat.messages.len(), 2);
    assert_eq!(t.chat.messages[1].role, Role::Tool);
}

fn chunk(delta: Delta, finish: Option<&str>) -> ChatChunk {
    ChatChunk::new("c", "up", 0).with_delta(delta, finish.map(str::to_owned))
}

fn text(t: &str) -> Delta {
    Delta {
        content: Some(t.into()),
        ..Delta::default()
    }
}

fn run(r: ResponsesRequest, chunks: &[ChatChunk]) -> (Vec<Value>, ResponsesStream) {
    let mut s = ResponsesStream::new(r, rid(), 7);
    let mut events: Vec<Value> = chunks.iter().flat_map(|c| s.on_chunk(c)).collect();
    events.extend(s.finish());
    (events, s)
}

fn types(events: &[Value]) -> Vec<&str> {
    events.iter().map(|e| e["type"].as_str().unwrap()).collect()
}

fn assert_sequenced(events: &[Value]) {
    for (i, e) in events.iter().enumerate() {
        assert_eq!(e["sequence_number"], i as u64, "{e}");
    }
}

#[test]
fn text_stream() {
    let (events, s) = run(
        req(json!({"model": "gpt", "input": "Hi"})),
        &[
            chunk(
                Delta {
                    role: Some(Role::Assistant),
                    content: Some(String::new()),
                    ..Delta::default()
                },
                None,
            ),
            chunk(text("Hel"), None),
            chunk(text("lo"), None),
            chunk(Delta::default(), Some("stop")),
            ChatChunk::new("c", "up", 0).with_usage(Usage::new(5, 2)),
        ],
    );
    assert_eq!(
        types(&events),
        [
            "response.created",
            "response.in_progress",
            "response.output_item.added",
            "response.content_part.added",
            "response.output_text.delta",
            "response.output_text.delta",
            "response.output_text.done",
            "response.content_part.done",
            "response.output_item.done",
            "response.completed"
        ]
    );
    assert_sequenced(&events);
    assert_eq!(events[0]["response"]["status"], "in_progress");
    assert_eq!(events[0]["response"]["id"], "resp_1");
    assert_eq!(events[2]["item"]["content"], json!([]));
    assert_eq!(events[2]["item"]["status"], "in_progress");
    let item_id = events[2]["item"]["id"].clone();
    assert_eq!(events[4]["item_id"], item_id);
    assert_eq!(events[4]["delta"], "Hel");
    assert_eq!(events[6]["text"], "Hello");
    assert_eq!(events[8]["item"]["status"], "completed");
    assert_eq!(events[8]["item"]["content"][0]["text"], "Hello");
    let done = &events[9]["response"];
    assert_eq!(done["status"], "completed");
    assert_eq!(done["usage"]["input_tokens"], 5);
    assert_eq!(done["output"][0]["content"][0]["text"], "Hello");
    assert_eq!(s.final_response(), Some(done));
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
fn reasoning_and_tool_stream() {
    let (events, s) = run(
        req(json!({"model": "m", "input": "x"})),
        &[
            chunk(
                Delta {
                    reasoning_content: Some("hmm".into()),
                    ..Delta::default()
                },
                None,
            ),
            chunk(tool_delta(0, Some("call_1"), Some("f"), ""), None),
            chunk(tool_delta(0, None, None, "{\"a\":"), None),
            chunk(tool_delta(0, None, None, "1}"), None),
            chunk(tool_delta(1, Some("call_2"), Some("g"), "{}"), None),
            chunk(Delta::default(), Some("tool_calls")),
        ],
    );
    assert_eq!(
        types(&events),
        [
            "response.created",
            "response.in_progress",
            "response.output_item.added",
            "response.reasoning_summary_part.added",
            "response.reasoning_summary_text.delta",
            "response.reasoning_summary_text.done",
            "response.reasoning_summary_part.done",
            "response.output_item.done",
            "response.output_item.added",
            "response.function_call_arguments.delta",
            "response.function_call_arguments.delta",
            "response.function_call_arguments.done",
            "response.output_item.done",
            "response.output_item.added",
            "response.function_call_arguments.delta",
            "response.function_call_arguments.done",
            "response.output_item.done",
            "response.completed"
        ]
    );
    assert_sequenced(&events);
    assert_eq!(events[7]["item"]["summary"][0]["text"], "hmm");
    assert_eq!(events[8]["item"]["call_id"], "call_1");
    assert_eq!(events[8]["item"]["name"], "f");
    assert_eq!(events[8]["output_index"], 1);
    assert_eq!(events[11]["arguments"], "{\"a\":1}");
    assert_eq!(events[13]["output_index"], 2);
    let done = s.final_response().unwrap();
    assert_eq!(done["output"][1]["arguments"], "{\"a\":1}");
    assert_eq!(done["output"][2]["status"], "completed");
    // Usage estimated without an upstream count.
    assert_eq!(done["usage"]["input_tokens"], 7);
}

#[test]
fn incomplete_and_failed_streams() {
    let (events, _) = run(
        req(json!({"model": "m", "input": "x"})),
        &[
            chunk(text("a"), None),
            chunk(Delta::default(), Some("length")),
        ],
    );
    let last = events.last().unwrap();
    assert_eq!(last["type"], "response.incomplete");
    assert_eq!(
        last["response"]["incomplete_details"]["reason"],
        "max_output_tokens"
    );

    let mut s = ResponsesStream::new(req(json!({"model": "m", "input": "x"})), rid(), 1);
    let mut events = s.on_chunk(&chunk(text("a"), None));
    events.extend(s.error("rate_limit_error", "slow down"));
    events.extend(s.finish());
    assert_sequenced(&events);
    let t = types(&events);
    assert_eq!(&t[t.len() - 2..], ["error", "response.failed"]);
    assert_eq!(events[events.len() - 2]["message"], "slow down");
    assert_eq!(events[events.len() - 1]["response"]["status"], "failed");
    assert_eq!(
        events[events.len() - 1]["response"]["error"]["code"],
        "rate_limit_error"
    );
    assert!(s.final_response().is_none());

    let (events, _) = run(req(json!({"model": "m", "input": "x"})), &[]);
    assert_eq!(
        types(&events),
        [
            "response.created",
            "response.in_progress",
            "response.completed"
        ]
    );
    let sse = encode_events(&events[..1]);
    assert!(sse.starts_with("event: response.created\ndata: {"), "{sse}");
}
