//! Cheap, deterministic prompt-size estimate used before an upstream call
//! (rate limiting, budget pre-checks). No tokenizer: roughly one token per
//! four UTF-8 bytes, plus fixed costs for message framing and media.
//!
//! The estimate leans high for typical English and code (real BPE tokenizers
//! average slightly more than four characters per token) and counts
//! multi-byte scripts by bytes, so it is a reasonable upper-ish bound. Exact
//! usage always comes back from the provider.

use crate::types::{ChatMessage, ChatRequest, ContentPart, MessageContent, part_type};

/// Framing tokens per message (role, separators), as in OpenAI's cookbook.
const PER_MESSAGE: u64 = 4;
/// Tokens priming the assistant reply.
const REPLY_PRIMING: u64 = 3;
/// Per tool definition / tool call framing.
const PER_TOOL: u64 = 8;
/// A high-detail 1024x1024 image on OpenAI (85 base + 4 tiles x 170).
const IMAGE_HIGH: u64 = 765;
const IMAGE_LOW: u64 = 85;
/// Flat cost for audio and file parts, whose token count depends on
/// duration / page count rather than encoded size.
const AUDIO_PART: u64 = 500;
const FILE_PART: u64 = 1_000;

/// Estimate the prompt tokens of a chat request.
pub fn estimate_prompt_tokens(req: &ChatRequest) -> u64 {
    let messages: u64 = req.messages.iter().map(message_tokens).sum();
    let tools: u64 = req.tools.iter().flatten().map(|t| PER_TOOL + json_tokens(t)).sum();
    let schema = req.response_format.as_ref().and_then(|f| f.json_schema.as_ref()).map_or(0, json_tokens);
    messages + tools + schema + REPLY_PRIMING
}

/// `ceil(bytes / 4)`.
pub(crate) fn text_tokens(text: &str) -> u64 {
    (text.len() as u64).div_ceil(4)
}

fn json_tokens<T: serde::Serialize>(value: &T) -> u64 {
    serde_json::to_string(value).map_or(0, |s| text_tokens(&s))
}

fn message_tokens(m: &ChatMessage) -> u64 {
    let content = match &m.content {
        None => 0,
        Some(MessageContent::Text(s)) => text_tokens(s),
        Some(MessageContent::Parts(parts)) => parts.iter().map(part_tokens).sum(),
    };
    let name = m.name.as_deref().map_or(0, |n| 1 + text_tokens(n));
    let calls: u64 = m.tool_calls.iter().flatten().map(|c| PER_TOOL + text_tokens(&c.function.name) + text_tokens(&c.function.arguments)).sum();
    let legacy_call = m.function_call.as_ref().map_or(0, |c| PER_TOOL + text_tokens(&c.name) + text_tokens(&c.arguments));
    PER_MESSAGE + content + name + calls + legacy_call
}

fn part_tokens(p: &ContentPart) -> u64 {
    match p.kind.as_str() {
        part_type::TEXT => p.text.as_deref().map_or(0, text_tokens),
        part_type::IMAGE_URL => match p.image_url.as_ref().and_then(|i| i.detail.as_deref()) {
            Some("low") => IMAGE_LOW,
            _ => IMAGE_HIGH,
        },
        part_type::INPUT_AUDIO => AUDIO_PART,
        part_type::FILE => FILE_PART,
        // Unknown part: count its serialized size.
        _ => json_tokens(p),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{ResponseFormat, Tool, ToolCall};
    use serde_json::json;

    fn req(messages: Vec<ChatMessage>) -> ChatRequest {
        ChatRequest { model: "m".into(), messages, ..ChatRequest::default() }
    }

    #[test]
    fn text_messages() {
        // 4 + ceil(11/4)=3, + 3 priming
        assert_eq!(estimate_prompt_tokens(&req(vec![ChatMessage::user("hello world")])), 10);
        assert_eq!(estimate_prompt_tokens(&req(vec![])), 3);
        assert_eq!(text_tokens(""), 0);
        assert_eq!(text_tokens("日本"), 2); // 6 bytes
    }

    #[test]
    fn media_tools_and_schema() {
        let mut image = ContentPart::image_url("https://x/y.png");
        let mut m = ChatMessage::user("");
        m.content = Some(MessageContent::Parts(vec![ContentPart::text("abcd"), image.clone()]));
        let high = estimate_prompt_tokens(&req(vec![m.clone()]));
        assert_eq!(high, 4 + 1 + IMAGE_HIGH + 3);
        image.image_url.as_mut().unwrap().detail = Some("low".into());
        m.content = Some(MessageContent::Parts(vec![image]));
        assert_eq!(estimate_prompt_tokens(&req(vec![m])), 4 + IMAGE_LOW + 3);

        let mut a = ChatMessage::assistant("");
        a.content = None;
        a.tool_calls = Some(vec![ToolCall::function("c", "abcd", "{\"x\":1}")]);
        assert_eq!(estimate_prompt_tokens(&req(vec![a])), 4 + PER_TOOL + 1 + 2 + 3);

        let mut r = req(vec![]);
        r.tools = Some(vec![Tool::function("f", None, Some(json!({"type": "object"})))]);
        r.response_format = Some(
            serde_json::from_value(json!({
                "type": "json_schema", "json_schema": {"name": "s", "schema": {"type": "object"}}
            }))
            .unwrap(),
        );
        let _: &ResponseFormat = r.response_format.as_ref().unwrap();
        let est = estimate_prompt_tokens(&r);
        assert!(est > 3 + PER_TOOL + 10, "{est}");
        // Deterministic.
        assert_eq!(est, estimate_prompt_tokens(&r));
    }
}
