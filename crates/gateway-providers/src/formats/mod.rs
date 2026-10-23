//! Inbound API formats other than Chat Completions, bridged to it.
//!
//! The gateway's inference path speaks OpenAI Chat Completions. These
//! modules translate other client-facing formats to a [`ChatRequest`] and
//! the resulting [`ChatResponse`](crate::ChatResponse) or chunk stream back,
//! so that every provider is reachable through every format (LiteLLM's
//! "adapters"):
//!
//! * [`anthropic_messages`]: Anthropic's Messages API (`/v1/messages`);
//! * [`responses`]: OpenAI's Responses API (`/v1/responses`).
//!
//! Everything here is pure: no I/O, no clock beyond id generation.

pub mod anthropic_messages;
pub mod responses;

use serde_json::Value;

use crate::deployment::{Deployment, Protocol};
use crate::types::{ChatRequest, MessageContent};

/// A request that cannot be translated: the client's fault (HTTP 400).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormatError {
    pub message: String,
    /// The offending request field, when known.
    pub param: Option<String>,
}

impl FormatError {
    pub fn new(message: impl Into<String>) -> Self {
        Self { message: message.into(), param: None }
    }

    pub fn param(mut self, param: impl Into<String>) -> Self {
        self.param = Some(param.into());
        self
    }
}

impl std::fmt::Display for FormatError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for FormatError {}

/// One server-sent event with a name: `event: <name>\ndata: <json>\n\n`.
pub fn sse_event(name: &str, data: &Value) -> String {
    format!("event: {name}\ndata: {data}\n\n")
}

/// What the deployments a translated request may be routed to understand
/// beyond plain Chat Completions. A request translated from Anthropic's
/// format carries native fields (`thinking`, `cache_control`, thinking
/// blocks, `top_k`) that the Anthropic adapter forwards and an
/// OpenAI-compatible upstream would reject; [`adapt_to_target`] removes
/// what the target does not understand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Target {
    /// Anthropic's Messages API (directly, or Claude on Bedrock / Vertex AI).
    pub anthropic: bool,
    /// Understands `top_k` (Anthropic, Gemini).
    pub top_k: bool,
}

impl Target {
    /// Everything understood: nothing is removed.
    pub const NATIVE: Target = Target { anthropic: true, top_k: true };

    pub fn of(d: &Deployment) -> Target {
        let protocol = d.provider.protocol();
        let claude_host = matches!(d.provider.name(), "bedrock" | "vertex_ai") && d.model.contains("claude");
        let anthropic = protocol == Protocol::Anthropic || claude_host;
        Target { anthropic, top_k: anthropic || protocol == Protocol::Gemini }
    }

    /// What every one of `deps` understands (all of them may serve the
    /// request through retries and fallbacks).
    pub fn all<'a>(deps: impl IntoIterator<Item = &'a Deployment>) -> Target {
        deps.into_iter().fold(Target::NATIVE, |acc, d| {
            let t = Target::of(d);
            Target { anthropic: acc.anthropic && t.anthropic, top_k: acc.top_k && t.top_k }
        })
    }
}

/// Request fields only Anthropic's Messages API understands.
const ANTHROPIC_ONLY_FIELDS: &[&str] = &["thinking", "service_tier", "container", "mcp_servers", "context_management"];

/// Remove from `req` what `target` does not understand: Anthropic-only
/// fields, `cache_control` markers and replayed thinking blocks unless the
/// target is Anthropic, and `top_k` unless it supports it.
pub fn adapt_to_target(req: &mut ChatRequest, target: Target) {
    if !target.top_k {
        req.extra.remove("top_k");
    }
    if target.anthropic {
        return;
    }
    for f in ANTHROPIC_ONLY_FIELDS {
        req.extra.remove(*f);
    }
    for m in &mut req.messages {
        m.extra.remove("cache_control");
        m.extra.remove("thinking_blocks");
        if let Some(MessageContent::Parts(parts)) = &mut m.content {
            for p in parts.iter_mut() {
                p.extra.remove("cache_control");
            }
        }
    }
    for t in req.tools.iter_mut().flatten() {
        t.extra.remove("cache_control");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn dep(model: &str) -> Deployment {
        Deployment::from_litellm_params_with_env(&json!({"model": model, "api_key": "k"}), |_| None).unwrap()
    }

    #[test]
    fn targets() {
        let claude = dep("anthropic/claude-3-5-sonnet-20241022");
        let gpt = dep("openai/gpt-4o");
        let gemini = dep("gemini/gemini-1.5-pro");
        assert_eq!(Target::of(&claude), Target::NATIVE);
        assert_eq!(Target::of(&gemini), Target { anthropic: false, top_k: true });
        assert_eq!(Target::all([&claude, &gpt]), Target { anthropic: false, top_k: false });
        assert_eq!(Target::all([]), Target::NATIVE);
    }

    #[test]
    fn adapting_strips_native_fields() {
        let mut req: ChatRequest = serde_json::from_value(json!({
            "model": "m",
            "messages": [
                {"role": "system", "content": [{"type": "text", "text": "s", "cache_control": {"type": "ephemeral"}}]},
                {"role": "assistant", "content": "a", "thinking_blocks": [{"type": "thinking", "thinking": "t", "signature": "x"}]}
            ],
            "tools": [{"type": "function", "function": {"name": "f"}, "cache_control": {"type": "ephemeral"}}],
            "thinking": {"type": "enabled", "budget_tokens": 2000},
            "top_k": 3
        }))
        .unwrap();
        let native = req.clone();
        adapt_to_target(&mut req, Target::NATIVE);
        assert_eq!(req, native);
        adapt_to_target(&mut req, Target { anthropic: false, top_k: true });
        let v = serde_json::to_value(&req).unwrap();
        assert_eq!(v["top_k"], 3);
        assert!(v.get("thinking").is_none());
        assert!(v["messages"][0]["content"][0].get("cache_control").is_none());
        assert!(v["messages"][1].get("thinking_blocks").is_none());
        assert!(v["tools"][0].get("cache_control").is_none());
        adapt_to_target(&mut req, Target { anthropic: false, top_k: false });
        assert!(req.extra.get("top_k").is_none());
    }

    #[test]
    fn sse_framing() {
        assert_eq!(sse_event("ping", &json!({"type": "ping"})), "event: ping\ndata: {\"type\":\"ping\"}\n\n");
    }
}
