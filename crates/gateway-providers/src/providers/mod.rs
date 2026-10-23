//! Provider adapters.
//!
//! Each adapter is a set of pure functions — build the upstream request,
//! parse the upstream response — plus a [`StreamTranslator`] that turns the
//! upstream's SSE events into OpenAI chunks. All network I/O lives in
//! [`crate::client`], which keeps every translation unit-testable.

pub(crate) mod anthropic;
pub(crate) mod bedrock;
pub(crate) mod gemini;
pub(crate) mod mock;
pub(crate) mod openai;
pub(crate) mod vertex;

use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use futures::{Stream, StreamExt, stream};
use serde_json::Value;

use crate::error::{ErrorKind, ProviderError};
use crate::sse::SseEvent;
use crate::types::{ChatChunk, ChatRequest, JsonObject};
use crate::{ChatStream, Deployment};

/// A fully built upstream HTTP request (always `POST` with a JSON body).
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct HttpRequest {
    pub url: String,
    pub headers: Vec<(String, String)>,
    pub body: Value,
}

impl HttpRequest {
    pub fn new(url: String, body: Value) -> Self {
        Self { url, headers: Vec::new(), body }
    }

    pub fn header(mut self, name: &str, value: impl Into<String>) -> Self {
        self.headers.push((name.to_owned(), value.into()));
        self
    }
}

/// Converts one upstream stream into OpenAI chunks.
pub(crate) trait StreamTranslator: Send + 'static {
    /// Translate one SSE event.
    fn on_event(&mut self, event: SseEvent) -> Result<Vec<ChatChunk>, ProviderError>;

    /// The upstream signalled the end of the stream; stop reading.
    fn is_done(&self) -> bool;

    /// The byte stream ended. Returns trailing chunks (e.g. the usage chunk
    /// for upstreams without an explicit end marker), or an error if the
    /// stream was cut short.
    fn finish(&mut self) -> Result<Vec<ChatChunk>, ProviderError>;
}

impl StreamTranslator for Box<dyn StreamTranslator> {
    fn on_event(&mut self, event: SseEvent) -> Result<Vec<ChatChunk>, ProviderError> {
        (**self).on_event(event)
    }

    fn is_done(&self) -> bool {
        (**self).is_done()
    }

    fn finish(&mut self) -> Result<Vec<ChatChunk>, ProviderError> {
        (**self).finish()
    }
}

/// Drive `events` through `translator`, enforcing `idle_timeout` between
/// events. The stream ends after the first error.
pub(crate) fn drive<S, T>(provider: &'static str, events: S, translator: T, idle_timeout: Duration) -> ChatStream
where
    S: Stream<Item = Result<SseEvent, ProviderError>> + Send + 'static,
    T: StreamTranslator,
{
    struct State<S, T> {
        events: std::pin::Pin<Box<S>>,
        translator: T,
        queue: VecDeque<Result<ChatChunk, ProviderError>>,
        finished: bool,
    }
    let state = State { events: Box::pin(events), translator, queue: VecDeque::new(), finished: false };
    Box::pin(stream::unfold(state, move |mut st| async move {
        loop {
            if let Some(item) = st.queue.pop_front() {
                return Some((item, st));
            }
            if st.finished {
                return None;
            }
            let next = tokio::time::timeout(idle_timeout, st.events.next()).await;
            let result = match next {
                Err(_) => Err(ProviderError::new(ErrorKind::Timeout, provider, format!("no data from upstream for {}s", idle_timeout.as_secs_f64()))),
                Ok(Some(Ok(event))) => {
                    let result = st.translator.on_event(event);
                    st.finished = st.translator.is_done();
                    result
                }
                Ok(Some(Err(e))) => Err(e),
                Ok(None) => {
                    st.finished = true;
                    st.translator.finish()
                }
            };
            match result {
                Ok(chunks) => st.queue.extend(chunks.into_iter().map(Ok)),
                Err(e) => {
                    st.finished = true;
                    st.queue.push_back(Err(e));
                }
            }
        }
    }))
}

/// Run a translator over a fixed list of events (unit tests).
#[cfg(test)]
pub(crate) fn translate_all<T: StreamTranslator>(mut translator: T, events: &[(&str, &str)]) -> Result<Vec<ChatChunk>, ProviderError> {
    let mut out = Vec::new();
    for (event, data) in events {
        out.extend(translator.on_event(SseEvent { event: (!event.is_empty()).then(|| (*event).to_owned()), data: (*data).to_owned(), id: None })?);
        if translator.is_done() {
            return Ok(out);
        }
    }
    out.extend(translator.finish()?);
    Ok(out)
}

/// Map a provider stop reason to an OpenAI `finish_reason` (LiteLLM's
/// `map_finish_reason` table; unknown values become `stop`).
pub(crate) fn map_finish_reason(reason: &str) -> &'static str {
    use crate::types::finish_reason::{CONTENT_FILTER, FUNCTION_CALL, LENGTH, STOP, TOOL_CALLS};
    match reason {
        // Anthropic
        "end_turn" | "stop_sequence" | "pause_turn" => STOP,
        "max_tokens" | "model_context_window_exceeded" | "compaction" => LENGTH,
        "tool_use" => TOOL_CALLS,
        "refusal" => CONTENT_FILTER,
        // Gemini
        "MAX_TOKENS" | "CONTINUATION" => LENGTH,
        "SAFETY"
        | "RECITATION"
        | "LANGUAGE"
        | "OTHER"
        | "BLOCKLIST"
        | "PROHIBITED_CONTENT"
        | "SPII"
        | "IMAGE_SAFETY"
        | "IMAGE_PROHIBITED_CONTENT"
        | "IMAGE_RECITATION"
        | "IMAGE_OTHER"
        | "NO_IMAGE" => CONTENT_FILTER,
        // OpenAI pass-through
        "length" => LENGTH,
        "tool_calls" => TOOL_CALLS,
        "content_filter" => CONTENT_FILTER,
        "function_call" => FUNCTION_CALL,
        _ => STOP,
    }
}

/// Seconds since the Unix epoch.
pub(crate) fn now_unix() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs())
}

/// A process-unique id such as `chatcmpl-18f0c3a2b4e5-1`.
pub(crate) fn gen_id(prefix: &str) -> String {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_nanos() as u64);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("{prefix}{nanos:x}{n:x}")
}

/// Split `data:<mime>;base64,<data>` into `(mime, data)`.
pub(crate) fn parse_data_url(url: &str) -> Option<(&str, &str)> {
    let rest = url.strip_prefix("data:")?;
    let (meta, data) = rest.split_once(',')?;
    let mime = meta.strip_suffix(";base64")?;
    // Drop parameters such as `;charset=utf-8`.
    let mime = mime.split(';').next().unwrap_or(mime);
    Some((if mime.is_empty() { "application/octet-stream" } else { mime }, data))
}

/// Guess a MIME type from a URL's file extension.
pub(crate) fn mime_from_url(url: &str) -> &'static str {
    let path = url.split(['?', '#']).next().unwrap_or(url);
    let ext = path.rsplit_once('.').map(|(_, e)| e.to_ascii_lowercase());
    match ext.as_deref() {
        Some("png") => "image/png",
        Some("gif") => "image/gif",
        Some("webp") => "image/webp",
        Some("pdf") => "application/pdf",
        Some("mp3") => "audio/mpeg",
        Some("wav") => "audio/wav",
        Some("mp4") => "video/mp4",
        Some("txt") => "text/plain",
        _ => "image/jpeg",
    }
}

/// Percent-encode one URL path segment.
pub(crate) fn encode_path_segment(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for b in s.bytes() {
        if b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.' | b'~') {
            out.push(b as char);
        } else {
            out.push_str(&format!("%{b:02X}"));
        }
    }
    out
}

/// Fill request parameters the client left unset from the deployment's
/// `litellm_params` defaults.
pub(crate) fn apply_request_defaults(dep: &Deployment, req: &ChatRequest) -> Result<ChatRequest, ProviderError> {
    if dep.request_defaults.is_empty() {
        return Ok(req.clone());
    }
    let Value::Object(mut obj) = serde_json::to_value(req).map_err(|e| internal(dep, e))? else {
        unreachable!("ChatRequest serializes to an object")
    };
    for (k, v) in &dep.request_defaults {
        obj.entry(k.clone()).or_insert_with(|| v.clone());
    }
    serde_json::from_value(Value::Object(obj))
        .map_err(|e| ProviderError::config(dep.provider.name(), format!("invalid request default in litellm_params: {e}")))
}

/// Parse a JSON tool-call argument string; empty means `{}`.
pub(crate) fn parse_arguments(provider: &str, args: &str) -> Result<Value, ProviderError> {
    if args.trim().is_empty() {
        return Ok(Value::Object(JsonObject::new()));
    }
    serde_json::from_str(args).map_err(|e| ProviderError::bad_request(provider, format!("tool call arguments are not valid JSON: {e}")))
}

/// Parse an upstream JSON body, mapping failures to `InvalidResponse`.
pub(crate) fn parse_json<T: serde::de::DeserializeOwned>(provider: &str, body: &str) -> Result<T, ProviderError> {
    serde_json::from_str(body).map_err(|e| {
        let mut end = body.len().min(300);
        while !body.is_char_boundary(end) {
            end -= 1;
        }
        ProviderError::invalid_response(provider, format!("could not parse upstream response ({e}): {}", &body[..end]))
    })
}

fn internal(dep: &Deployment, e: impl std::fmt::Display) -> ProviderError {
    ProviderError::config(dep.provider.name(), e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn data_urls() {
        assert_eq!(parse_data_url("data:image/png;base64,AAAA"), Some(("image/png", "AAAA")));
        assert_eq!(parse_data_url("data:text/plain;charset=utf-8;base64,aGk="), Some(("text/plain", "aGk=")));
        assert_eq!(parse_data_url("data:;base64,AA"), Some(("application/octet-stream", "AA")));
        assert_eq!(parse_data_url("data:image/png,raw"), None);
        assert_eq!(parse_data_url("https://x/y.png"), None);
    }

    #[test]
    fn mime_guess_and_encoding() {
        assert_eq!(mime_from_url("https://x/a.PNG?sig=1"), "image/png");
        assert_eq!(mime_from_url("https://x/a"), "image/jpeg");
        assert_eq!(encode_path_segment("my dep/1"), "my%20dep%2F1");
        assert_eq!(encode_path_segment("gemini-1.5-pro"), "gemini-1.5-pro");
    }

    #[test]
    fn finish_reasons() {
        for (from, to) in [
            ("end_turn", "stop"),
            ("stop_sequence", "stop"),
            ("max_tokens", "length"),
            ("tool_use", "tool_calls"),
            ("refusal", "content_filter"),
            ("STOP", "stop"),
            ("MAX_TOKENS", "length"),
            ("SAFETY", "content_filter"),
            ("MALFORMED_FUNCTION_CALL", "stop"),
            ("length", "length"),
            ("whatever", "stop"),
        ] {
            assert_eq!(map_finish_reason(from), to, "{from}");
        }
    }

    #[test]
    fn ids_are_unique() {
        assert_ne!(gen_id("x-"), gen_id("x-"));
        assert!(gen_id("chatcmpl-").starts_with("chatcmpl-"));
    }

    #[test]
    fn request_defaults_fill_missing_only() {
        let dep = Deployment::from_litellm_params_with_env(&json!({"model": "fake/m", "temperature": 0.1, "max_tokens": 50}), |_| None).unwrap();
        let req = ChatRequest { model: "m".into(), temperature: Some(0.9), ..ChatRequest::default() };
        let out = apply_request_defaults(&dep, &req).unwrap();
        assert_eq!(out.temperature, Some(0.9));
        assert_eq!(out.max_tokens, Some(50));
    }

    #[test]
    fn arguments() {
        assert_eq!(parse_arguments("p", "").unwrap(), json!({}));
        assert_eq!(parse_arguments("p", "{\"a\":1}").unwrap(), json!({"a": 1}));
        assert_eq!(parse_arguments("p", "{").unwrap_err().kind(), ErrorKind::BadRequest);
    }

    struct Echo {
        done: bool,
    }

    impl StreamTranslator for Echo {
        fn on_event(&mut self, event: SseEvent) -> Result<Vec<ChatChunk>, ProviderError> {
            match event.data.as_str() {
                "stop" => {
                    self.done = true;
                    Ok(vec![])
                }
                "fail" => Err(ProviderError::invalid_response("t", "boom")),
                d => Ok(vec![ChatChunk::new(d, "m", 0)]),
            }
        }
        fn is_done(&self) -> bool {
            self.done
        }
        fn finish(&mut self) -> Result<Vec<ChatChunk>, ProviderError> {
            Ok(vec![ChatChunk::new("end", "m", 0)])
        }
    }

    fn events(data: &[&str]) -> impl Stream<Item = Result<SseEvent, ProviderError>> + Send + 'static {
        let items: Vec<_> = data.iter().map(|d| Ok(SseEvent { data: (*d).to_owned(), ..SseEvent::default() })).collect();
        stream::iter(items)
    }

    async fn ids(s: ChatStream) -> Vec<Result<String, ErrorKind>> {
        s.map(|r| r.map(|c| c.id).map_err(|e| e.kind())).collect().await
    }

    #[tokio::test]
    async fn drive_stops_at_done_errors_and_eof() {
        let t = || Echo { done: false };
        let s = drive("t", events(&["a", "stop", "never"]), t(), Duration::from_secs(5));
        assert_eq!(ids(s).await, vec![Ok("a".into())]);
        let s = drive("t", events(&["a", "fail", "never"]), t(), Duration::from_secs(5));
        assert_eq!(ids(s).await, vec![Ok("a".into()), Err(ErrorKind::InvalidResponse)]);
        let s = drive("t", events(&["a"]), t(), Duration::from_secs(5));
        assert_eq!(ids(s).await, vec![Ok("a".into()), Ok("end".into())]);
    }

    #[tokio::test]
    async fn drive_idle_timeout() {
        let s = drive("t", stream::pending(), Echo { done: false }, Duration::from_millis(20));
        assert_eq!(ids(s).await, vec![Err(ErrorKind::Timeout)]);
    }
}
