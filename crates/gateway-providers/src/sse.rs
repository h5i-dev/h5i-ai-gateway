//! Minimal Server-Sent Events parser.
//!
//! [`SseDecoder`] is an incremental, transport-agnostic decoder following the
//! WHATWG event-stream rules that matter for LLM APIs: `\n`, `\r\n` and `\r`
//! line endings (also when split across network chunks), multi-line `data:`
//! fields joined with `\n`, `:` comment lines (keep-alives), an optional
//! leading BOM, and an unterminated final event at end of input. The
//! OpenAI `[DONE]` sentinel is surfaced as ordinary data; adapters decide what
//! it means. [`events`] adapts a byte stream (e.g. reqwest's `bytes_stream`).

use std::collections::VecDeque;

use bytes::Bytes;
use futures::{Stream, StreamExt, stream};

use crate::error::ProviderError;

/// One dispatched event.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SseEvent {
    /// The `event:` field, if any.
    pub event: Option<String>,
    /// All `data:` lines joined with `\n`.
    pub data: String,
    /// The `id:` field, if any.
    pub id: Option<String>,
}

/// Incremental SSE decoder.
#[derive(Debug, Default)]
pub struct SseDecoder {
    /// Bytes of the current, not yet terminated line.
    line: Vec<u8>,
    /// The previous chunk ended in `\r`; a leading `\n` must be skipped.
    pending_cr: bool,
    started: bool,
    event: Option<String>,
    data: Option<String>,
    id: Option<String>,
}

impl SseDecoder {
    pub fn new() -> Self {
        Self::default()
    }

    /// Feed bytes; returns the events completed by them.
    pub fn feed(&mut self, mut bytes: &[u8]) -> Vec<SseEvent> {
        let mut out = Vec::new();
        if !self.started && !bytes.is_empty() {
            self.started = true;
            bytes = bytes.strip_prefix(b"\xEF\xBB\xBF").unwrap_or(bytes);
        }
        for &b in bytes {
            if std::mem::take(&mut self.pending_cr) && b == b'\n' {
                continue;
            }
            match b {
                b'\n' => self.end_line(&mut out),
                b'\r' => {
                    self.end_line(&mut out);
                    self.pending_cr = true;
                }
                _ => self.line.push(b),
            }
        }
        out
    }

    /// Signal end of input; returns a final unterminated event, if any.
    pub fn finish(&mut self) -> Option<SseEvent> {
        let mut out = Vec::new();
        if !self.line.is_empty() {
            self.end_line(&mut out);
        }
        self.dispatch(&mut out);
        out.pop()
    }

    fn end_line(&mut self, out: &mut Vec<SseEvent>) {
        let line = std::mem::take(&mut self.line);
        if line.is_empty() {
            self.dispatch(out);
            return;
        }
        if line[0] == b':' {
            return; // comment
        }
        let line = String::from_utf8_lossy(&line);
        let (field, value) = match line.split_once(':') {
            Some((f, v)) => (f, v.strip_prefix(' ').unwrap_or(v)),
            None => (line.as_ref(), ""),
        };
        match field {
            "data" => match &mut self.data {
                Some(d) => {
                    d.push('\n');
                    d.push_str(value);
                }
                None => self.data = Some(value.to_owned()),
            },
            "event" => self.event = Some(value.to_owned()),
            "id" => self.id = Some(value.to_owned()),
            _ => {} // `retry:` and unknown fields are ignored
        }
    }

    fn dispatch(&mut self, out: &mut Vec<SseEvent>) {
        let event = self.event.take();
        let id = self.id.take();
        // Per the spec an event without data is not dispatched.
        if let Some(data) = self.data.take() {
            out.push(SseEvent { event, data, id });
        }
    }
}

/// Decode a byte stream into SSE events. Transport errors are mapped with
/// [`ProviderError::from_reqwest`] and end the stream.
pub(crate) fn events<S>(provider: &'static str, bytes: S) -> impl Stream<Item = Result<SseEvent, ProviderError>> + Send + 'static
where
    S: Stream<Item = Result<Bytes, reqwest::Error>> + Send + 'static,
{
    struct State<S> {
        bytes: std::pin::Pin<Box<S>>,
        decoder: SseDecoder,
        queue: VecDeque<SseEvent>,
        done: bool,
    }
    let state = State { bytes: Box::pin(bytes), decoder: SseDecoder::new(), queue: VecDeque::new(), done: false };
    stream::unfold(state, move |mut st| async move {
        loop {
            if let Some(ev) = st.queue.pop_front() {
                return Some((Ok(ev), st));
            }
            if st.done {
                return None;
            }
            match st.bytes.next().await {
                Some(Ok(chunk)) => st.queue.extend(st.decoder.feed(&chunk)),
                Some(Err(e)) => {
                    st.done = true;
                    return Some((Err(ProviderError::from_reqwest(provider, e)), st));
                }
                None => {
                    st.done = true;
                    st.queue.extend(st.decoder.finish());
                }
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decode_all(chunks: &[&[u8]]) -> Vec<SseEvent> {
        let mut d = SseDecoder::new();
        let mut out: Vec<SseEvent> = chunks.iter().flat_map(|c| d.feed(c)).collect();
        out.extend(d.finish());
        out
    }

    fn data(s: &str) -> SseEvent {
        SseEvent { data: s.into(), ..SseEvent::default() }
    }

    #[test]
    fn basic_events_and_done() {
        let evs = decode_all(&[b"data: {\"a\":1}\n\ndata: [DONE]\n\n"]);
        assert_eq!(evs, vec![data("{\"a\":1}"), data("[DONE]")]);
    }

    #[test]
    fn crlf_and_cr_line_endings_split_across_chunks() {
        let evs = decode_all(&[b"data: a\r", b"\n\r", b"\ndata: b\r\rdata: c\r\n", b"\r\n"]);
        assert_eq!(evs, vec![data("a"), data("b"), data("c")]);
    }

    #[test]
    fn multi_line_data_event_name_id_and_comments() {
        let evs = decode_all(&[b": keep-alive\n\nevent: content_block_delta\nid: 7\ndata: line1\ndata:line2\nretry: 10\n\n"]);
        assert_eq!(evs, vec![SseEvent { event: Some("content_block_delta".into()), data: "line1\nline2".into(), id: Some("7".into()) }]);
    }

    #[test]
    fn events_without_data_are_not_dispatched() {
        assert!(decode_all(&[b"event: ping\n\n: comment\n\n"]).is_empty());
        // `data` with no colon is an empty data line.
        assert_eq!(decode_all(&[b"data\n\n"]), vec![data("")]);
    }

    #[test]
    fn bom_byte_splits_and_unterminated_tail() {
        let evs = decode_all(&[b"\xEF\xBB\xBFda", b"ta: x", b"y\n", b"\ndata: tail"]);
        assert_eq!(evs, vec![data("xy"), data("tail")]);
    }

    #[test]
    fn utf8_split_across_chunks() {
        let s = "data: héllo\n\n".as_bytes();
        let (a, b) = s.split_at(8); // splits the two-byte 'é'
        assert_eq!(decode_all(&[a, b]), vec![data("héllo")]);
    }

    #[tokio::test]
    async fn byte_stream_adapter() {
        let chunks: Vec<Result<Bytes, reqwest::Error>> = vec![Ok(Bytes::from_static(b"data: 1\n\nda")), Ok(Bytes::from_static(b"ta: 2\n\n"))];
        let evs: Vec<_> = events("t", stream::iter(chunks)).collect().await;
        let evs: Vec<_> = evs.into_iter().map(Result::unwrap).collect();
        assert_eq!(evs, vec![data("1"), data("2")]);
    }
}
