//! Canned responses without network access, like LiteLLM's
//! `mock_completion`.
//!
//! Used when the request carries `mock_response`, when the deployment sets
//! `mock_response` in `litellm_params`, or for `mock/` / `fake/` deployments.
//! Usage is plausible rather than fixed: prompt tokens come from
//! [`crate::estimate_prompt_tokens`], completion tokens from the length of the
//! canned text. LiteLLM's error triggers are honoured:
//! `litellm.RateLimitError`, `litellm.InternalServerError`,
//! `litellm.ContextWindowExceededError`, `litellm.Timeout`, and any text
//! starting with `Exception: content_filter_policy`.

use futures::stream;

use super::{gen_id, now_unix};
use crate::error::{ErrorKind, ProviderError};
use crate::tokens::{estimate_prompt_tokens, text_tokens};
use crate::types::{
    ChatChunk, ChatMessage, ChatRequest, ChatResponse, Choice, Delta, Embedding, EmbeddingRequest, EmbeddingResponse, EmbeddingVector, JsonObject,
    Role, Usage, finish_reason,
};
use crate::{ChatStream, Deployment};

/// LiteLLM's default mock text.
pub(crate) const DEFAULT_MOCK_RESPONSE: &str = "This is a mock request";
/// Dimensions of mock embeddings when the request does not ask for any.
const DEFAULT_DIMENSIONS: u32 = 8;

/// The canned text to answer with, if this request should be mocked.
pub(crate) fn mock_text<'a>(dep: &'a Deployment, req: &'a ChatRequest) -> Option<&'a str> {
    req.mock_response
        .as_deref()
        .or(dep.mock_response.as_deref())
        .or_else(|| (dep.provider.protocol() == crate::deployment::Protocol::Mock).then_some(DEFAULT_MOCK_RESPONSE))
}

pub(crate) fn check_error_trigger(dep: &Deployment, text: &str) -> Result<(), ProviderError> {
    let provider = dep.provider.name();
    let (kind, message) = match text {
        "litellm.RateLimitError" => (ErrorKind::RateLimited, "this is a mock rate limit error"),
        "litellm.InternalServerError" => (ErrorKind::ServiceUnavailable, "this is a mock internal server error"),
        "litellm.ContextWindowExceededError" => (ErrorKind::ContextWindowExceeded, "this is a mock context window exceeded error"),
        "litellm.Timeout" => (ErrorKind::Timeout, "this is a mock timeout error"),
        t if t.starts_with("Exception: content_filter_policy") => (ErrorKind::ContentPolicy, t),
        _ => return Ok(()),
    };
    let mut err = ProviderError::new(kind, provider, message);
    if kind == ErrorKind::ServiceUnavailable {
        // LiteLLM's InternalServerError is a 500.
        err = ProviderError::from_upstream(provider, 500, message, None);
    }
    Err(err)
}

fn usage(req: &ChatRequest, text: &str) -> Usage {
    Usage::new(estimate_prompt_tokens(req), text_tokens(text).max(1))
}

pub(crate) fn chat(dep: &Deployment, req: &ChatRequest, text: &str) -> Result<ChatResponse, ProviderError> {
    check_error_trigger(dep, text)?;
    let n = req.n.unwrap_or(1).max(1);
    let choices = (0..n)
        .map(|index| Choice {
            index,
            message: ChatMessage::assistant(text),
            finish_reason: Some(finish_reason::STOP.into()),
            logprobs: None,
            extra: JsonObject::new(),
        })
        .collect();
    Ok(ChatResponse {
        id: gen_id("chatcmpl-mock-"),
        object: "chat.completion".into(),
        created: now_unix(),
        model: dep.model.clone(),
        choices,
        usage: Some(usage(req, text)),
        system_fingerprint: None,
        extra: JsonObject::new(),
    })
}

/// Role chunk, one chunk per word (whitespace kept), finish chunk, usage
/// chunk.
pub(crate) fn chat_stream(dep: &Deployment, req: &ChatRequest, text: &str) -> Result<ChatStream, ProviderError> {
    check_error_trigger(dep, text)?;
    let id = gen_id("chatcmpl-mock-");
    let created = now_unix();
    let chunk = || ChatChunk::new(id.clone(), dep.model.clone(), created);
    let mut chunks = vec![chunk().with_delta(Delta { role: Some(Role::Assistant), content: Some(String::new()), ..Delta::default() }, None)];
    chunks.extend(split_words(text).map(|w| chunk().with_delta(Delta { content: Some(w.to_owned()), ..Delta::default() }, None)));
    chunks.push(chunk().with_delta(Delta::default(), Some(finish_reason::STOP.into())));
    chunks.push(chunk().with_usage(usage(req, text)));
    Ok(Box::pin(stream::iter(chunks.into_iter().map(Ok))))
}

/// Split after each run of whitespace: `"a b  c"` -> `["a ", "b  ", "c"]`.
fn split_words(text: &str) -> impl Iterator<Item = &str> {
    let mut rest = text;
    std::iter::from_fn(move || {
        if rest.is_empty() {
            return None;
        }
        let word_end = rest.find(char::is_whitespace).unwrap_or(rest.len());
        let end = rest[word_end..].find(|c: char| !c.is_whitespace()).map_or(rest.len(), |i| word_end + i);
        let (head, tail) = rest.split_at(end);
        rest = tail;
        Some(head)
    })
}

/// Deterministic pseudo-embeddings (FNV-1a seeded per input and dimension).
pub(crate) fn embeddings(dep: &Deployment, req: &EmbeddingRequest) -> EmbeddingResponse {
    let dims = req.dimensions.unwrap_or(DEFAULT_DIMENSIONS);
    let inputs: Vec<String> = match &req.input {
        crate::types::EmbeddingInput::Text(s) => vec![s.clone()],
        crate::types::EmbeddingInput::Texts(v) => v.clone(),
        crate::types::EmbeddingInput::Tokens(t) => vec![format!("{t:?}")],
        crate::types::EmbeddingInput::TokenBatches(b) => b.iter().map(|t| format!("{t:?}")).collect(),
    };
    let data = inputs
        .iter()
        .enumerate()
        .map(|(i, text)| Embedding {
            object: "embedding".into(),
            index: i as u32,
            embedding: EmbeddingVector::Float(
                (0..dims)
                    .map(|d| {
                        let h = fnv1a(text.as_bytes(), d);
                        (h % 2001) as f64 / 1000.0 - 1.0
                    })
                    .collect(),
            ),
        })
        .collect();
    let prompt = inputs.iter().map(|t| text_tokens(t)).sum();
    EmbeddingResponse { object: "list".into(), data, model: dep.model.clone(), usage: Usage::new(prompt, 0), extra: JsonObject::new() }
}

fn fnv1a(bytes: &[u8], seed: u32) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325 ^ u64::from(seed);
    for &b in bytes {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::StreamExt;
    use serde_json::json;

    fn dep(v: serde_json::Value) -> Deployment {
        Deployment::from_litellm_params_with_env(&v, |_| None).unwrap()
    }

    fn req(mock: Option<&str>) -> ChatRequest {
        ChatRequest {
            model: "m".into(),
            messages: vec![ChatMessage::user("hello there")],
            mock_response: mock.map(str::to_owned),
            ..ChatRequest::default()
        }
    }

    #[test]
    fn which_requests_are_mocked() {
        let real = dep(json!({"model": "openai/gpt-4o", "api_key": "k"}));
        assert_eq!(mock_text(&real, &req(None)), None);
        assert_eq!(mock_text(&real, &req(Some("hi"))), Some("hi"));
        let fake = dep(json!({"model": "fake/m"}));
        assert_eq!(mock_text(&fake, &req(None)), Some(DEFAULT_MOCK_RESPONSE));
        let configured = dep(json!({"model": "openai/gpt-4o", "api_key": "k", "mock_response": "canned"}));
        assert_eq!(mock_text(&configured, &req(None)), Some("canned"));
        assert_eq!(mock_text(&configured, &req(Some("override"))), Some("override"));
    }

    #[test]
    fn completion_with_usage() {
        let d = dep(json!({"model": "fake/m"}));
        let mut r = req(None);
        r.n = Some(2);
        let resp = chat(&d, &r, "Hi there, friend").unwrap();
        assert_eq!(resp.choices.len(), 2);
        assert_eq!(resp.choices[1].message.text(), "Hi there, friend");
        let u = resp.usage.unwrap();
        assert_eq!(u.prompt_tokens, estimate_prompt_tokens(&r));
        assert_eq!(u.completion_tokens, 4);
        assert_eq!(u.total_tokens, u.prompt_tokens + 4);
    }

    #[test]
    fn error_triggers() {
        let d = dep(json!({"model": "fake/m"}));
        let kinds = [
            ("litellm.RateLimitError", ErrorKind::RateLimited, 429),
            ("litellm.InternalServerError", ErrorKind::ServiceUnavailable, 500),
            ("litellm.ContextWindowExceededError", ErrorKind::ContextWindowExceeded, 400),
            ("litellm.Timeout", ErrorKind::Timeout, 408),
            ("Exception: content_filter_policy violated", ErrorKind::ContentPolicy, 400),
        ];
        for (text, kind, status) in kinds {
            let e = chat(&d, &req(None), text).unwrap_err();
            assert_eq!((e.kind(), e.status_code()), (kind, status), "{text}");
            assert!(chat_stream(&d, &req(None), text).is_err());
        }
    }

    #[tokio::test]
    async fn stream_shape() {
        let d = dep(json!({"model": "fake/m"}));
        let chunks: Vec<ChatChunk> = chat_stream(&d, &req(None), "a b  c").unwrap().map(Result::unwrap).collect().await;
        let text: String = chunks.iter().filter_map(|c| c.choices.first()?.delta.content.clone()).collect();
        assert_eq!(text, "a b  c");
        assert_eq!(chunks.len(), 1 + 3 + 2);
        assert_eq!(chunks[4].choices[0].finish_reason.as_deref(), Some("stop"));
        assert!(chunks[5].is_usage_only());
    }

    #[test]
    fn word_splitting() {
        assert_eq!(split_words("a b  c").collect::<Vec<_>>(), vec!["a ", "b  ", "c"]);
        assert_eq!(split_words("  x").collect::<Vec<_>>(), vec!["  ", "x"]);
        assert_eq!(split_words("").count(), 0);
    }

    #[test]
    fn deterministic_embeddings() {
        let d = dep(json!({"model": "fake/e"}));
        let r: EmbeddingRequest = serde_json::from_value(json!({"model": "e", "input": ["a", "b"], "dimensions": 3})).unwrap();
        let a = embeddings(&d, &r);
        assert_eq!(a, embeddings(&d, &r));
        assert_eq!(a.data.len(), 2);
        let EmbeddingVector::Float(v) = &a.data[0].embedding else { panic!() };
        assert_eq!(v.len(), 3);
        assert!(v.iter().all(|x| (-1.0..=1.0).contains(x)));
        assert_ne!(a.data[0], a.data[1]);
    }
}
