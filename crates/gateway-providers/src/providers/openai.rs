//! OpenAI and OpenAI-compatible upstreams (including Azure OpenAI).
//!
//! The request is the client's request with gateway-only fields removed, the
//! upstream model name substituted and the deployment's `extra_body` merged
//! in; unknown fields pass through untouched. Responses are already in the
//! target shape. Streams are normalised so that usage arrives exactly once,
//! in a trailing usage-only chunk.

use serde_json::{Value, json};

use super::{HttpRequest, StreamTranslator, encode_path_segment, parse_json};
use crate::deployment::{Deployment, Protocol, Provider};
use crate::error::ProviderError;
use crate::sse::SseEvent;
use crate::types::{
    ChatChunk, ChatRequest, ChatResponse, EmbeddingRequest, EmbeddingResponse, Usage,
};

/// Request fields understood by the gateway (LiteLLM proxy conventions) that
/// must never reach an upstream.
pub const GATEWAY_ONLY_FIELDS: &[&str] = &[
    "mock_response",
    "metadata",
    "litellm_metadata",
    "fallbacks",
    "num_retries",
    "context_window_fallback_dict",
    "caching",
    "cache",
    "tags",
    "guardrails",
    "drop_params",
    "api_key",
    "api_base",
    "base_url",
    "api_version",
];

pub(crate) fn endpoint(dep: &Deployment, path: &str) -> String {
    let base = dep.api_base().trim_end_matches('/');
    match dep.provider.protocol() {
        Protocol::Azure => format!(
            "{base}/openai/deployments/{}/{path}?api-version={}",
            encode_path_segment(&dep.model),
            dep.api_version.as_deref().unwrap_or_default()
        ),
        _ => format!("{base}/{path}"),
    }
}

pub(crate) fn with_auth(dep: &Deployment, req: HttpRequest) -> HttpRequest {
    let Some(key) = &dep.api_key else { return req };
    let req = match dep.provider.protocol() {
        Protocol::Azure => req.header("api-key", key.expose()),
        _ => req.header("authorization", format!("Bearer {}", key.expose())),
    };
    match (&dep.organization, dep.provider) {
        (Some(org), Provider::OpenAi) => req.header("openai-organization", org.clone()),
        _ => req,
    }
}

/// Serialize `body`, drop gateway-only fields, set the upstream model and
/// merge `extra_body`.
pub(crate) fn upstream_body<T: serde::Serialize>(
    dep: &Deployment,
    body: &T,
) -> Result<serde_json::Map<String, Value>, ProviderError> {
    let Value::Object(mut obj) = serde_json::to_value(body)
        .map_err(|e| ProviderError::bad_request(dep.provider.name(), e.to_string()))?
    else {
        unreachable!("request types serialize to objects")
    };
    for key in GATEWAY_ONLY_FIELDS {
        obj.remove(*key);
    }
    obj.insert("model".into(), Value::String(dep.model.clone()));
    for (k, v) in &dep.extra_body {
        obj.insert(k.clone(), v.clone());
    }
    Ok(obj)
}

pub(crate) fn chat_request(
    dep: &Deployment,
    req: &ChatRequest,
    stream: bool,
) -> Result<HttpRequest, ProviderError> {
    let mut obj = upstream_body(dep, req)?;
    // Most OpenAI-compatible servers only know the legacy name.
    if !matches!(dep.provider, Provider::OpenAi | Provider::Azure)
        && !obj.contains_key("max_tokens")
        && let Some(v) = obj.remove("max_completion_tokens")
    {
        obj.insert("max_tokens".into(), v);
    }
    if stream {
        obj.insert("stream".into(), Value::Bool(true));
        if dep.provider.spec().stream_usage {
            let options = obj.entry("stream_options").or_insert_with(|| json!({}));
            if let Value::Object(o) = options {
                o.insert("include_usage".into(), Value::Bool(true));
            }
        } else {
            // These upstreams reject `stream_options` (and report usage
            // unprompted).
            obj.remove("stream_options");
        }
    } else {
        obj.remove("stream");
        obj.remove("stream_options");
    }
    Ok(with_auth(
        dep,
        HttpRequest::new(endpoint(dep, "chat/completions"), Value::Object(obj)),
    ))
}

pub(crate) fn embeddings_request(
    dep: &Deployment,
    req: &EmbeddingRequest,
) -> Result<HttpRequest, ProviderError> {
    let obj = upstream_body(dep, req)?;
    Ok(with_auth(
        dep,
        HttpRequest::new(endpoint(dep, "embeddings"), Value::Object(obj)),
    ))
}

/// Some OpenAI-compatible servers report failures as `200 {"error": ...}`.
pub(crate) fn embedded_error(provider: &str, body: &str) -> Option<ProviderError> {
    let v: Value = serde_json::from_str(body).ok()?;
    let err = v.get("error").filter(|e| !e.is_null())?;
    if v.get("choices").is_some() || v.get("data").is_some() {
        return None;
    }
    let status = err
        .get("code")
        .and_then(|c| c.as_u64().or_else(|| c.as_str()?.parse().ok()))
        .filter(|c| (400..=599).contains(c))
        .unwrap_or(500) as u16;
    Some(ProviderError::from_upstream(provider, status, body, None))
}

pub(crate) fn parse_chat(dep: &Deployment, body: &str) -> Result<ChatResponse, ProviderError> {
    if let Some(e) = embedded_error(dep.provider.name(), body) {
        return Err(e);
    }
    parse_json(dep.provider.name(), body)
}

pub(crate) fn parse_embeddings(
    dep: &Deployment,
    body: &str,
) -> Result<EmbeddingResponse, ProviderError> {
    if let Some(e) = embedded_error(dep.provider.name(), body) {
        return Err(e);
    }
    parse_json(dep.provider.name(), body)
}

struct ChunkIdentity {
    id: String,
    model: String,
    created: u64,
    system_fingerprint: Option<String>,
}

/// Pass-through stream with usage normalisation: usage found on any chunk is
/// removed from it and re-emitted once, as a usage-only chunk, at the end.
pub(crate) struct OpenAiStream {
    provider: &'static str,
    usage: Option<Usage>,
    /// Identity of the latest chunk, reused for the trailing usage chunk.
    last: Option<ChunkIdentity>,
    done: bool,
}

impl OpenAiStream {
    pub fn new(provider: &'static str) -> Self {
        Self {
            provider,
            usage: None,
            last: None,
            done: false,
        }
    }

    fn usage_chunk(&mut self) -> Vec<ChatChunk> {
        let Some(usage) = self.usage.take() else {
            return Vec::new();
        };
        let mut chunk = match self.last.take() {
            Some(last) => {
                let mut c = ChatChunk::new(last.id, last.model, last.created);
                c.system_fingerprint = last.system_fingerprint;
                c
            }
            None => ChatChunk::new(super::gen_id("chatcmpl-"), "", super::now_unix()),
        };
        chunk.usage = Some(usage);
        vec![chunk]
    }
}

impl StreamTranslator for OpenAiStream {
    fn on_event(&mut self, event: SseEvent) -> Result<Vec<ChatChunk>, ProviderError> {
        let data = event.data.trim();
        if data == "[DONE]" {
            self.done = true;
            return Ok(self.usage_chunk());
        }
        if data.is_empty() {
            return Ok(Vec::new());
        }
        if let Some(e) = embedded_error(self.provider, data) {
            return Err(e);
        }
        let mut chunk: ChatChunk = parse_json(self.provider, data)?;
        if let Some(u) = chunk.usage.take() {
            self.usage = Some(u);
        }
        self.last = Some(ChunkIdentity {
            id: chunk.id.clone(),
            model: chunk.model.clone(),
            created: chunk.created,
            system_fingerprint: chunk.system_fingerprint.clone(),
        });
        // Usage-only chunks and choice-less preambles (Azure's
        // `prompt_filter_results`) carry nothing for the client.
        if chunk.choices.is_empty() {
            return Ok(Vec::new());
        }
        Ok(vec![chunk])
    }

    fn is_done(&self) -> bool {
        self.done
    }

    fn finish(&mut self) -> Result<Vec<ChatChunk>, ProviderError> {
        Ok(self.usage_chunk())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::providers::translate_all;
    use crate::types::ChatMessage;
    use serde_json::json;

    fn dep(params: Value) -> Deployment {
        Deployment::from_litellm_params_with_env(&params, |_| None).unwrap()
    }

    fn request() -> ChatRequest {
        serde_json::from_value(json!({
            "model": "client-alias",
            "messages": [{"role": "user", "content": "hi"}],
            "temperature": 0.5,
            "top_k": 3,
            "metadata": {"tenant": "a"},
            "mock_response": "never forwarded",
            "max_completion_tokens": 20,
            "stream_options": {"include_usage": false}
        }))
        .unwrap()
    }

    #[test]
    fn openai_request_shape() {
        let d = dep(
            json!({"model": "openai/gpt-4o", "api_key": "sk", "organization": "org", "extra_body": {"service_tier": "flex"}}),
        );
        let r = chat_request(&d, &request(), false).unwrap();
        assert_eq!(r.url, "https://api.openai.com/v1/chat/completions");
        assert!(
            r.headers
                .contains(&("authorization".into(), "Bearer sk".into()))
        );
        assert!(
            r.headers
                .contains(&("openai-organization".into(), "org".into()))
        );
        assert_eq!(r.body["model"], "gpt-4o");
        assert_eq!(r.body["top_k"], 3);
        assert_eq!(r.body["service_tier"], "flex");
        assert_eq!(r.body["max_completion_tokens"], 20);
        for key in ["metadata", "mock_response", "stream", "stream_options"] {
            assert!(r.body.get(key).is_none(), "{key} must not be forwarded");
        }
    }

    #[test]
    fn streaming_requests_usage_where_supported() {
        let d = dep(json!({"model": "groq/llama3-8b-8192", "api_key": "k"}));
        let r = chat_request(&d, &request(), true).unwrap();
        assert_eq!(r.url, "https://api.groq.com/openai/v1/chat/completions");
        assert_eq!(r.body["stream"], true);
        assert_eq!(r.body["stream_options"]["include_usage"], true);
        assert_eq!(r.body["max_tokens"], 20, "renamed for non-OpenAI providers");
        assert!(r.body.get("max_completion_tokens").is_none());

        let d = dep(json!({"model": "mistral/mistral-large-latest", "api_key": "k"}));
        let mut req = request();
        req.stream_options = None;
        let r = chat_request(&d, &req, true).unwrap();
        assert!(r.body.get("stream_options").is_none());
    }

    #[test]
    fn azure_url_and_auth() {
        let d = dep(json!({
            "model": "azure/my-gpt4o", "api_key": "az",
            "api_base": "https://res.openai.azure.com/", "api_version": "2024-10-21"
        }));
        let r = chat_request(&d, &request(), false).unwrap();
        assert_eq!(
            r.url,
            "https://res.openai.azure.com/openai/deployments/my-gpt4o/chat/completions?api-version=2024-10-21"
        );
        assert_eq!(r.headers, vec![("api-key".to_owned(), "az".to_owned())]);
        let e = embeddings_request(
            &d,
            &serde_json::from_value(json!({"model": "x", "input": "hi"})).unwrap(),
        )
        .unwrap();
        assert!(
            e.url
                .ends_with("/openai/deployments/my-gpt4o/embeddings?api-version=2024-10-21")
        );
    }

    #[test]
    fn self_hosted_without_key() {
        let d = dep(json!({"model": "hosted_vllm/llama", "api_base": "http://vllm:8000/v1"}));
        let r = chat_request(&d, &request(), false).unwrap();
        assert_eq!(r.url, "http://vllm:8000/v1/chat/completions");
        assert!(r.headers.is_empty());
        let d = dep(json!({"model": "ollama_chat/llama3"}));
        assert_eq!(
            chat_request(&d, &request(), false).unwrap().url,
            "http://localhost:11434/v1/chat/completions"
        );
    }

    #[test]
    fn parses_responses_and_embedded_errors() {
        let d = dep(json!({"model": "openai/gpt-4o", "api_key": "k"}));
        let resp = parse_chat(
            &d,
            r#"{"id":"c","object":"chat.completion","created":1,"model":"gpt-4o","choices":[{"index":0,"message":{"role":"assistant","content":"hi"},"finish_reason":"stop"}],"usage":{"prompt_tokens":1,"completion_tokens":1,"total_tokens":2}}"#,
        )
        .unwrap();
        assert_eq!(resp.choices[0].message, ChatMessage::assistant("hi"));
        let err = parse_chat(&d, r#"{"error":{"message":"rate limited","code":429}}"#).unwrap_err();
        assert_eq!(err.status_code(), 429);
        assert!(err.is_retryable());
        assert_eq!(
            parse_chat(&d, "nope").unwrap_err().kind(),
            crate::ErrorKind::InvalidResponse
        );
    }

    #[test]
    fn stream_moves_usage_to_trailing_chunk() {
        let chunks = translate_all(
            OpenAiStream::new("openai"),
            &[
                ("", r#"{"id":"c1","object":"chat.completion.chunk","created":5,"model":"gpt-4o","choices":[],"prompt_filter_results":[]}"#),
                ("", r#"{"id":"c1","object":"chat.completion.chunk","created":5,"model":"gpt-4o","choices":[{"index":0,"delta":{"role":"assistant","content":"Hi"},"finish_reason":null}]}"#),
                ("", r#"{"id":"c1","object":"chat.completion.chunk","created":5,"model":"gpt-4o","choices":[{"index":0,"delta":{},"finish_reason":"stop"}],"usage":{"prompt_tokens":3,"completion_tokens":1,"total_tokens":4}}"#),
                ("", r#"{"id":"c1","object":"chat.completion.chunk","created":5,"model":"gpt-4o","choices":[],"usage":{"prompt_tokens":3,"completion_tokens":2,"total_tokens":5}}"#),
                ("", "[DONE]"),
                ("", "ignored after done"),
            ],
        )
        .unwrap();
        assert_eq!(chunks.len(), 3);
        assert_eq!(chunks[0].choices[0].delta.content.as_deref(), Some("Hi"));
        assert!(chunks[1].usage.is_none());
        assert_eq!(chunks[1].choices[0].finish_reason.as_deref(), Some("stop"));
        assert!(chunks[2].is_usage_only());
        assert_eq!(chunks[2].usage.as_ref().unwrap().completion_tokens, 2);
        assert_eq!((chunks[2].id.as_str(), chunks[2].created), ("c1", 5));
    }

    #[test]
    fn stream_without_done_and_errors() {
        let chunks = translate_all(
            OpenAiStream::new("x"),
            &[("", r#"{"id":"c","choices":[{"index":0,"delta":{"content":"a"}}],"usage":{"prompt_tokens":1,"completion_tokens":1,"total_tokens":2}}"#)],
        )
        .unwrap();
        assert_eq!(chunks.len(), 2);
        assert!(chunks[1].is_usage_only());
        let err = translate_all(
            OpenAiStream::new("x"),
            &[("", r#"{"error":{"message":"overloaded","code":503}}"#)],
        )
        .unwrap_err();
        assert_eq!(err.status_code(), 503);
        assert!(translate_all(OpenAiStream::new("x"), &[("", "{bad")]).is_err());
    }
}
