//! AWS event-stream binary framing (`application/vnd.amazon.eventstream`),
//! as used by Bedrock's `ConverseStream` and `InvokeModelWithResponseStream`.
//!
//! Each message is
//!
//! ```text
//! [total length: u32 BE][headers length: u32 BE][prelude CRC32: u32 BE]
//! [headers ...][payload ...][message CRC32: u32 BE]
//! ```
//!
//! where the prelude CRC covers the first 8 bytes and the message CRC covers
//! everything before it. A header is `[name length: u8][name][type: u8][value]`
//! with the value encoding given by the type tag (0-9).
//!
//! [`EventStreamDecoder`] is incremental (messages may be split across network
//! chunks arbitrarily) and rejects corrupt frames. `events` adapts a byte
//! stream into [`SseEvent`]s — `event` is the `:event-type` header and `data`
//! the payload — so the Bedrock adapter can reuse the SSE stream driver;
//! `exception` / `error` messages become classified [`ProviderError`]s.

use std::collections::VecDeque;

use bytes::{Buf, Bytes, BytesMut};
use futures::{Stream, StreamExt, stream};

use crate::error::{ErrorKind, ProviderError};
use crate::sse::SseEvent;

/// Prelude (12 bytes) plus the trailing message CRC (4 bytes).
const MIN_MESSAGE_LEN: usize = 16;
/// AWS caps messages at 16 MiB; anything larger is corruption.
const MAX_MESSAGE_LEN: usize = 16 * 1024 * 1024;
const MAX_HEADERS_LEN: usize = 128 * 1024;

/// A header value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HeaderValue {
    Bool(bool),
    Byte(i8),
    Short(i16),
    Int(i32),
    Long(i64),
    Bytes(Bytes),
    String(String),
    /// Milliseconds since the Unix epoch.
    Timestamp(i64),
    Uuid([u8; 16]),
}

impl HeaderValue {
    pub fn as_str(&self) -> Option<&str> {
        match self {
            HeaderValue::String(s) => Some(s),
            _ => None,
        }
    }
}

/// One decoded message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message {
    pub headers: Vec<(String, HeaderValue)>,
    pub payload: Bytes,
}

impl Message {
    /// A string header's value.
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(n, _)| n == name)
            .and_then(|(_, v)| v.as_str())
    }
}

/// A framing error: the stream is corrupt and cannot be resynchronised.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum DecodeError {
    #[error("prelude checksum mismatch (expected {expected:#010x}, computed {computed:#010x})")]
    PreludeCrc { expected: u32, computed: u32 },
    #[error("message checksum mismatch (expected {expected:#010x}, computed {computed:#010x})")]
    MessageCrc { expected: u32, computed: u32 },
    #[error("invalid message length {0}")]
    Length(usize),
    #[error("invalid headers: {0}")]
    Headers(&'static str),
    #[error("stream ended inside a message ({0} bytes left over)")]
    Truncated(usize),
}

/// Incremental decoder.
#[derive(Debug, Default)]
pub struct EventStreamDecoder {
    buf: BytesMut,
}

impl EventStreamDecoder {
    pub fn new() -> Self {
        Self::default()
    }

    /// Feed bytes; returns the messages they complete. After an error the
    /// decoder must not be used again.
    pub fn feed(&mut self, bytes: &[u8]) -> Result<Vec<Message>, DecodeError> {
        self.buf.extend_from_slice(bytes);
        let mut out = Vec::new();
        while let Some(msg) = self.next_message()? {
            out.push(msg);
        }
        Ok(out)
    }

    /// Signal end of input: an error if a partial message is buffered.
    pub fn finish(&self) -> Result<(), DecodeError> {
        if self.buf.is_empty() {
            Ok(())
        } else {
            Err(DecodeError::Truncated(self.buf.len()))
        }
    }

    fn next_message(&mut self) -> Result<Option<Message>, DecodeError> {
        if self.buf.len() < 12 {
            return Ok(None);
        }
        let total = be_u32(&self.buf[0..4]) as usize;
        let headers_len = be_u32(&self.buf[4..8]) as usize;
        let prelude_crc = be_u32(&self.buf[8..12]);
        let computed = crc32(&self.buf[0..8]);
        if computed != prelude_crc {
            return Err(DecodeError::PreludeCrc {
                expected: prelude_crc,
                computed,
            });
        }
        if !(MIN_MESSAGE_LEN..=MAX_MESSAGE_LEN).contains(&total)
            || headers_len > MAX_HEADERS_LEN
            || headers_len > total - MIN_MESSAGE_LEN
        {
            return Err(DecodeError::Length(total));
        }
        if self.buf.len() < total {
            return Ok(None);
        }
        let frame = self.buf.split_to(total).freeze();
        let expected = be_u32(&frame[total - 4..]);
        let computed = crc32(&frame[..total - 4]);
        if computed != expected {
            return Err(DecodeError::MessageCrc { expected, computed });
        }
        let headers = parse_headers(frame.slice(12..12 + headers_len))?;
        let payload = frame.slice(12 + headers_len..total - 4);
        Ok(Some(Message { headers, payload }))
    }
}

fn be_u32(b: &[u8]) -> u32 {
    u32::from_be_bytes([b[0], b[1], b[2], b[3]])
}

fn parse_headers(mut b: Bytes) -> Result<Vec<(String, HeaderValue)>, DecodeError> {
    let need = |b: &Bytes, n: usize| {
        if b.remaining() < n {
            Err(DecodeError::Headers("header runs past the header block"))
        } else {
            Ok(())
        }
    };
    let mut out = Vec::new();
    while b.has_remaining() {
        let name_len = b.get_u8() as usize;
        if name_len == 0 {
            return Err(DecodeError::Headers("empty header name"));
        }
        need(&b, name_len + 1)?;
        let name = String::from_utf8(b.split_to(name_len).to_vec())
            .map_err(|_| DecodeError::Headers("header name is not UTF-8"))?;
        let value = match b.get_u8() {
            0 => HeaderValue::Bool(true),
            1 => HeaderValue::Bool(false),
            2 => {
                need(&b, 1)?;
                HeaderValue::Byte(b.get_i8())
            }
            3 => {
                need(&b, 2)?;
                HeaderValue::Short(b.get_i16())
            }
            4 => {
                need(&b, 4)?;
                HeaderValue::Int(b.get_i32())
            }
            5 => {
                need(&b, 8)?;
                HeaderValue::Long(b.get_i64())
            }
            t @ (6 | 7) => {
                need(&b, 2)?;
                let len = b.get_u16() as usize;
                need(&b, len)?;
                let raw = b.split_to(len);
                if t == 6 {
                    HeaderValue::Bytes(raw)
                } else {
                    HeaderValue::String(
                        String::from_utf8(raw.to_vec())
                            .map_err(|_| DecodeError::Headers("string header is not UTF-8"))?,
                    )
                }
            }
            8 => {
                need(&b, 8)?;
                HeaderValue::Timestamp(b.get_i64())
            }
            9 => {
                need(&b, 16)?;
                let mut uuid = [0u8; 16];
                b.copy_to_slice(&mut uuid);
                HeaderValue::Uuid(uuid)
            }
            _ => return Err(DecodeError::Headers("unknown header value type")),
        };
        out.push((name, value));
    }
    Ok(out)
}

/// CRC-32 (IEEE 802.3, reflected, polynomial 0xEDB88320) as used by the
/// event-stream format.
pub fn crc32(data: &[u8]) -> u32 {
    static TABLE: std::sync::LazyLock<[u32; 256]> = std::sync::LazyLock::new(|| {
        let mut table = [0u32; 256];
        for (i, slot) in table.iter_mut().enumerate() {
            let mut c = i as u32;
            for _ in 0..8 {
                c = if c & 1 != 0 {
                    0xEDB8_8320 ^ (c >> 1)
                } else {
                    c >> 1
                };
            }
            *slot = c;
        }
        table
    });
    let mut crc = !0u32;
    for &b in data {
        crc = TABLE[((crc ^ b as u32) & 0xFF) as usize] ^ (crc >> 8);
    }
    !crc
}

/// Encode a message (string headers only); used by tests and mock servers.
pub fn encode(headers: &[(&str, &str)], payload: &[u8]) -> Vec<u8> {
    let mut h = Vec::new();
    for (name, value) in headers {
        h.push(name.len() as u8);
        h.extend_from_slice(name.as_bytes());
        h.push(7);
        h.extend_from_slice(&(value.len() as u16).to_be_bytes());
        h.extend_from_slice(value.as_bytes());
    }
    let total = 12 + h.len() + payload.len() + 4;
    let mut out = Vec::with_capacity(total);
    out.extend_from_slice(&(total as u32).to_be_bytes());
    out.extend_from_slice(&(h.len() as u32).to_be_bytes());
    let prelude_crc = crc32(&out);
    out.extend_from_slice(&prelude_crc.to_be_bytes());
    out.extend_from_slice(&h);
    out.extend_from_slice(payload);
    let crc = crc32(&out);
    out.extend_from_slice(&crc.to_be_bytes());
    out
}

/// HTTP status for an event-stream exception type (Bedrock runtime errors).
fn exception_status(kind: &str) -> u16 {
    match kind
        .trim_end_matches("Exception")
        .to_ascii_lowercase()
        .as_str()
    {
        "throttling" | "servicequotaexceeded" => 429,
        "validation" => 400,
        "accessdenied" => 403,
        "resourcenotfound" => 404,
        "modeltimeout" => 408,
        "modelnotready" | "serviceunavailable" => 503,
        "modelstreamerror" | "modelerror" => 424,
        _ => 500,
    }
}

/// Convert one decoded message into an SSE-shaped event, or the error it
/// reports.
pub(crate) fn to_event(provider: &str, msg: Message) -> Result<SseEvent, ProviderError> {
    let payload = String::from_utf8_lossy(&msg.payload).into_owned();
    match msg.header(":message-type").unwrap_or("event") {
        "event" => Ok(SseEvent {
            event: msg.header(":event-type").map(str::to_owned),
            data: payload,
            id: None,
        }),
        "exception" => {
            let kind = msg.header(":exception-type").unwrap_or("unknownException");
            let body = if payload.trim().is_empty() {
                kind
            } else {
                &payload
            };
            Err(ProviderError::from_upstream(
                provider,
                exception_status(kind),
                body,
                None,
            ))
        }
        _ => {
            let code = msg.header(":error-code").unwrap_or("InternalError");
            let message = msg.header(":error-message").unwrap_or(code);
            Err(ProviderError::from_upstream(
                provider,
                exception_status(code),
                &serde_json::json!({"message": message, "code": code}).to_string(),
                None,
            ))
        }
    }
}

/// Decode an event-stream byte stream into events. Framing errors and
/// exception messages end the stream with an error.
pub(crate) fn events<S>(
    provider: &'static str,
    bytes: S,
) -> impl Stream<Item = Result<SseEvent, ProviderError>> + Send + 'static
where
    S: Stream<Item = Result<Bytes, reqwest::Error>> + Send + 'static,
{
    struct State<S> {
        bytes: std::pin::Pin<Box<S>>,
        decoder: EventStreamDecoder,
        queue: VecDeque<Result<SseEvent, ProviderError>>,
        done: bool,
    }
    let state = State {
        bytes: Box::pin(bytes),
        decoder: EventStreamDecoder::new(),
        queue: VecDeque::new(),
        done: false,
    };
    let corrupt = move |e: DecodeError| {
        ProviderError::new(
            ErrorKind::InvalidResponse,
            provider,
            format!("malformed event stream: {e}"),
        )
    };
    stream::unfold(state, move |mut st| async move {
        loop {
            if let Some(item) = st.queue.pop_front() {
                if item.is_err() {
                    st.done = true;
                    st.queue.clear();
                }
                return Some((item, st));
            }
            if st.done {
                return None;
            }
            match st.bytes.next().await {
                Some(Ok(chunk)) => match st.decoder.feed(&chunk) {
                    Ok(msgs) => st
                        .queue
                        .extend(msgs.into_iter().map(|m| to_event(provider, m))),
                    Err(e) => {
                        st.done = true;
                        return Some((Err(corrupt(e)), st));
                    }
                },
                Some(Err(e)) => {
                    st.done = true;
                    return Some((Err(ProviderError::from_reqwest(provider, e)), st));
                }
                None => {
                    st.done = true;
                    if let Err(e) = st.decoder.finish() {
                        return Some((Err(corrupt(e)), st));
                    }
                }
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crc32_check_value() {
        assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
        assert_eq!(crc32(b""), 0);
    }

    fn decode_one(frame: &[u8]) -> Result<Message, DecodeError> {
        let mut d = EventStreamDecoder::new();
        let mut msgs = d.feed(frame)?;
        d.finish()?;
        assert_eq!(msgs.len(), 1);
        Ok(msgs.remove(0))
    }

    /// Messages from the AWS CRT test suite
    /// (`aws-c-event-stream/tests/message_deserializer_test.c`).
    #[test]
    fn crt_vectors() {
        let no_headers: &[u8] = &[
            0x00, 0x00, 0x00, 0x1D, 0x00, 0x00, 0x00, 0x00, 0xfd, 0x52, 0x8c, 0x5a, 0x7b, 0x27,
            0x66, 0x6f, 0x6f, 0x27, 0x3a, 0x27, 0x62, 0x61, 0x72, 0x27, 0x7d, 0xc3, 0x65, 0x39,
            0x36,
        ];
        let msg = decode_one(no_headers).unwrap();
        assert!(msg.headers.is_empty());
        assert_eq!(&msg.payload[..], b"{'foo':'bar'}");

        let one_header: &[u8] = &[
            0x00, 0x00, 0x00, 0x3D, 0x00, 0x00, 0x00, 0x20, 0x07, 0xFD, 0x83, 0x96, 0x0C, b'c',
            b'o', b'n', b't', b'e', b'n', b't', b'-', b't', b'y', b'p', b'e', 0x07, 0x00, 0x10,
            b'a', b'p', b'p', b'l', b'i', b'c', b'a', b't', b'i', b'o', b'n', b'/', b'j', b's',
            b'o', b'n', 0x7b, 0x27, 0x66, 0x6f, 0x6f, 0x27, 0x3a, 0x27, 0x62, 0x61, 0x72, 0x27,
            0x7d, 0x8D, 0x9C, 0x08, 0xB1,
        ];
        let msg = decode_one(one_header).unwrap();
        assert_eq!(msg.header("content-type"), Some("application/json"));
        assert_eq!(&msg.payload[..], b"{'foo':'bar'}");
    }

    /// Fixtures from `aws-smithy-eventstream` (Apache-2.0), copied to
    /// `tests/fixtures/eventstream/`.
    #[test]
    fn smithy_fixtures() {
        macro_rules! fixture {
            ($name:literal) => {
                include_bytes!(concat!("../tests/fixtures/eventstream/", $name)) as &[u8]
            };
        }
        let msg = decode_one(fixture!("valid_with_all_headers_and_payload")).unwrap();
        let values: Vec<(&str, HeaderValue)> = msg
            .headers
            .iter()
            .map(|(n, v)| (n.as_str(), v.clone()))
            .collect();
        assert_eq!(
            values,
            vec![
                ("true", HeaderValue::Bool(true)),
                ("false", HeaderValue::Bool(false)),
                ("byte", HeaderValue::Byte(50)),
                ("short", HeaderValue::Short(20_000)),
                ("int", HeaderValue::Int(500_000)),
                ("long", HeaderValue::Long(50_000_000_000)),
                (
                    "bytes",
                    HeaderValue::Bytes(Bytes::from_static(b"some bytes"))
                ),
                ("str", HeaderValue::String("some str".into())),
                ("time", HeaderValue::Timestamp(5_000_000_000)),
                (
                    "uuid",
                    HeaderValue::Uuid(0xb79bc914_de21_4e13_b8b2_bc47e85b7f0b_u128.to_be_bytes())
                ),
            ]
        );
        assert_eq!(&msg.payload[..], b"some payload");
        assert!(
            decode_one(fixture!("valid_empty_payload"))
                .unwrap()
                .payload
                .is_empty()
        );
        assert!(
            decode_one(fixture!("valid_no_headers"))
                .unwrap()
                .headers
                .is_empty()
        );

        assert_eq!(
            decode_one(fixture!("invalid_prelude_checksum")),
            Err(DecodeError::PreludeCrc {
                expected: 0xDEADBEEF,
                computed: 0x8BB495FB
            })
        );
        assert_eq!(
            decode_one(fixture!("invalid_message_checksum")),
            Err(DecodeError::MessageCrc {
                expected: 0xDEADBEEF,
                computed: 0x01a05860
            })
        );
        for bad in [
            fixture!("invalid_header_string_value_length"),
            fixture!("invalid_header_string_length_cut_off"),
            fixture!("invalid_header_value_type"),
            fixture!("invalid_header_name_length"),
            fixture!("invalid_headers_length"),
            fixture!("invalid_header_name_length_too_long"),
        ] {
            assert!(decode_one(bad).is_err());
        }
    }

    #[test]
    fn round_trip_split_anywhere() {
        let mut stream = Vec::new();
        stream.extend(encode(
            &[(":message-type", "event"), (":event-type", "messageStart")],
            br#"{"role":"assistant"}"#,
        ));
        stream.extend(encode(&[(":event-type", "empty")], b""));
        stream.extend(encode(
            &[(":event-type", "contentBlockDelta")],
            br#"{"delta":{"text":"hi"}}"#,
        ));
        for split in 0..=stream.len() {
            let mut d = EventStreamDecoder::new();
            let mut msgs = d.feed(&stream[..split]).unwrap();
            msgs.extend(d.feed(&stream[split..]).unwrap());
            d.finish().unwrap();
            assert_eq!(msgs.len(), 3, "split at {split}");
            assert_eq!(msgs[0].header(":event-type"), Some("messageStart"));
            assert_eq!(&msgs[0].payload[..], br#"{"role":"assistant"}"#);
            assert!(msgs[1].payload.is_empty());
            assert_eq!(msgs[2].header(":event-type"), Some("contentBlockDelta"));
        }
        // Byte by byte.
        let mut d = EventStreamDecoder::new();
        let n: usize = stream
            .iter()
            .map(|b| d.feed(std::slice::from_ref(b)).unwrap().len())
            .sum();
        assert_eq!(n, 3);
    }

    #[test]
    fn all_header_types() {
        let mut h = Vec::new();
        let mut push = |name: &str, tag: u8, value: &[u8]| {
            h.push(name.len() as u8);
            h.extend_from_slice(name.as_bytes());
            h.push(tag);
            h.extend_from_slice(value);
        };
        push("t", 0, &[]);
        push("f", 1, &[]);
        push("b", 2, &[0xFF]);
        push("s", 3, &(-2i16).to_be_bytes());
        push("i", 4, &7i32.to_be_bytes());
        push("l", 5, &(-9i64).to_be_bytes());
        push("y", 6, &[0, 2, 0xDE, 0xAD]);
        push("str", 7, &[0, 2, b'o', b'k']);
        push("ts", 8, &1_700_000_000_000i64.to_be_bytes());
        push("u", 9, &[7u8; 16]);
        let total = 12 + h.len() + 4;
        let mut frame = Vec::new();
        frame.extend_from_slice(&(total as u32).to_be_bytes());
        frame.extend_from_slice(&(h.len() as u32).to_be_bytes());
        let c = crc32(&frame);
        frame.extend_from_slice(&c.to_be_bytes());
        frame.extend_from_slice(&h);
        let c = crc32(&frame);
        frame.extend_from_slice(&c.to_be_bytes());
        let msg = EventStreamDecoder::new().feed(&frame).unwrap().remove(0);
        let values: Vec<HeaderValue> = msg.headers.into_iter().map(|(_, v)| v).collect();
        assert_eq!(
            values,
            vec![
                HeaderValue::Bool(true),
                HeaderValue::Bool(false),
                HeaderValue::Byte(-1),
                HeaderValue::Short(-2),
                HeaderValue::Int(7),
                HeaderValue::Long(-9),
                HeaderValue::Bytes(Bytes::from_static(&[0xDE, 0xAD])),
                HeaderValue::String("ok".into()),
                HeaderValue::Timestamp(1_700_000_000_000),
                HeaderValue::Uuid([7; 16]),
            ]
        );
    }

    #[test]
    fn crc_failures_are_detected() {
        let good = encode(&[(":event-type", "x")], b"payload");
        // Corrupt the payload: message CRC fails.
        let mut bad = good.clone();
        let n = bad.len();
        bad[n - 6] ^= 0x01;
        assert!(matches!(
            EventStreamDecoder::new().feed(&bad),
            Err(DecodeError::MessageCrc { .. })
        ));
        // Corrupt the length: prelude CRC fails before any length is trusted.
        let mut bad = good.clone();
        bad[3] ^= 0x01;
        assert!(matches!(
            EventStreamDecoder::new().feed(&bad),
            Err(DecodeError::PreludeCrc { .. })
        ));
        // A JSON error body is not an event stream.
        assert!(
            EventStreamDecoder::new()
                .feed(br#"{"message":"bad"}"#)
                .is_err()
        );
    }

    #[test]
    fn truncation_and_bad_lengths() {
        let good = encode(&[(":event-type", "x")], b"payload");
        let mut d = EventStreamDecoder::new();
        assert!(d.feed(&good[..good.len() - 1]).unwrap().is_empty());
        assert!(matches!(d.finish(), Err(DecodeError::Truncated(_))));
        // A prelude with a valid CRC but an impossible length.
        let mut frame = Vec::new();
        frame.extend_from_slice(&8u32.to_be_bytes());
        frame.extend_from_slice(&0u32.to_be_bytes());
        let c = crc32(&frame);
        frame.extend_from_slice(&c.to_be_bytes());
        assert_eq!(
            EventStreamDecoder::new().feed(&frame),
            Err(DecodeError::Length(8))
        );
    }

    #[test]
    fn exceptions_become_errors() {
        let msg = EventStreamDecoder::new()
            .feed(&encode(
                &[
                    (":message-type", "exception"),
                    (":exception-type", "throttlingException"),
                ],
                br#"{"message":"Too many requests, please wait"}"#,
            ))
            .unwrap()
            .remove(0);
        let err = to_event("bedrock", msg).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::RateLimited);
        assert_eq!(err.message(), "Too many requests, please wait");

        let msg = EventStreamDecoder::new()
            .feed(&encode(
                &[
                    (":message-type", "exception"),
                    (":exception-type", "validationException"),
                ],
                br#"{"message":"Input is too long for requested model."}"#,
            ))
            .unwrap()
            .remove(0);
        let err = to_event("bedrock", msg).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::ContextWindowExceeded);

        let msg = EventStreamDecoder::new()
            .feed(&encode(
                &[
                    (":message-type", "error"),
                    (":error-code", "InternalServerException"),
                    (":error-message", "boom"),
                ],
                b"",
            ))
            .unwrap()
            .remove(0);
        let err = to_event("bedrock", msg).unwrap_err();
        assert_eq!((err.status_code(), err.message()), (500, "boom"));
        assert!(err.is_retryable());
    }

    #[tokio::test]
    async fn byte_stream_adapter() {
        let mut body = encode(
            &[(":message-type", "event"), (":event-type", "messageStart")],
            br#"{"role":"assistant"}"#,
        );
        body.extend(encode(
            &[(":message-type", "event"), (":event-type", "messageStop")],
            br#"{"stopReason":"end_turn"}"#,
        ));
        let (a, b) = body.split_at(7);
        let chunks: Vec<Result<Bytes, reqwest::Error>> =
            vec![Ok(Bytes::copy_from_slice(a)), Ok(Bytes::copy_from_slice(b))];
        let evs: Vec<_> = events("bedrock", stream::iter(chunks)).collect().await;
        let evs: Vec<SseEvent> = evs.into_iter().map(Result::unwrap).collect();
        assert_eq!(evs.len(), 2);
        assert_eq!(evs[1].event.as_deref(), Some("messageStop"));
        assert_eq!(evs[1].data, r#"{"stopReason":"end_turn"}"#);

        // Truncated stream -> InvalidResponse at the end.
        let good = encode(&[(":event-type", "x")], b"{}");
        let chunks: Vec<Result<Bytes, reqwest::Error>> =
            vec![Ok(Bytes::copy_from_slice(&good[..10]))];
        let evs: Vec<_> = events("bedrock", stream::iter(chunks)).collect().await;
        assert_eq!(evs.len(), 1);
        assert_eq!(
            evs[0].as_ref().unwrap_err().kind(),
            ErrorKind::InvalidResponse
        );
    }
}
