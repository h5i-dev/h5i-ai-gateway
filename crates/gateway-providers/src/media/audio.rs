//! Transcriptions, translations and speech for OpenAI-shaped upstreams
//! (OpenAI, Azure, Groq and other OpenAI-compatible servers), and the
//! multipart re-encoding shared with image edits.

use bytes::Bytes;
use serde_json::{Value, json};

use super::{MediaForm, Multipart, SpeechRequest, TranscriptionResponse};
use crate::deployment::Deployment;
use crate::error::ProviderError;
use crate::providers::openai::{self, GATEWAY_ONLY_FIELDS};
use crate::providers::{HttpRequest, parse_json};

/// The upstream URL, headers and body of a multipart call to `path`: the
/// client's fields (gateway-only ones removed) after the upstream `model`,
/// then the deployment's scalar `extra_body` values, then the files.
pub(crate) fn form_request(dep: &Deployment, path: &str, form: &MediaForm) -> (String, Vec<(String, String)>, Multipart) {
    let auth = openai::with_auth(dep, HttpRequest::new(openai::endpoint(dep, path), Value::Null));
    let mut m = Multipart::new();
    m.text("model", &dep.model);
    for (k, v) in &form.fields {
        let overridden = dep.extra_body.contains_key(k.trim_end_matches("[]"));
        if k != "model" && !GATEWAY_ONLY_FIELDS.contains(&k.as_str()) && !overridden {
            m.text(k, v);
        }
    }
    for (k, v) in &dep.extra_body {
        match v {
            Value::String(s) => m.text(k, s),
            Value::Number(_) | Value::Bool(_) => m.text(k, &v.to_string()),
            Value::Array(items) => {
                for item in items {
                    let s = item.as_str().map_or_else(|| item.to_string(), str::to_owned);
                    m.text(&format!("{k}[]"), &s);
                }
                &mut m
            }
            _ => &mut m,
        };
    }
    for f in &form.files {
        m.file(&f.field, &f.filename, f.content_type.as_deref(), &f.data);
    }
    (auth.url, auth.headers, m)
}

/// JSON when the upstream says so (or the body is JSON for a JSON format);
/// otherwise the text with the upstream's content type.
pub(crate) fn parse_transcription(
    dep: &Deployment,
    form: &MediaForm,
    content_type: Option<&str>,
    body: String,
) -> Result<TranscriptionResponse, ProviderError> {
    let format = form.field("response_format").unwrap_or("json");
    let json_type = content_type.is_some_and(|ct| ct.contains("json"));
    if json_type || (content_type.is_none() && matches!(format, "json" | "verbose_json" | "diarized_json")) {
        if let Some(e) = openai::embedded_error(dep.provider.name(), &body) {
            return Err(e);
        }
        return Ok(TranscriptionResponse::Json(parse_json(dep.provider.name(), &body)?));
    }
    let content_type = content_type.map_or_else(|| text_content_type(format).to_owned(), str::to_owned);
    Ok(TranscriptionResponse::Text { content_type, body })
}

/// The content type of a text transcription format.
pub(crate) fn text_content_type(format: &str) -> &'static str {
    match format {
        "vtt" => "text/vtt; charset=utf-8",
        "srt" => "application/x-subrip; charset=utf-8",
        _ => "text/plain; charset=utf-8",
    }
}

pub(crate) fn mock_transcription(form: &MediaForm, text: &str) -> TranscriptionResponse {
    match form.field("response_format").unwrap_or("json") {
        "json" => TranscriptionResponse::Json(json!({"text": text})),
        "verbose_json" => TranscriptionResponse::Json(json!({"task": "transcribe", "text": text, "segments": []})),
        "srt" => TranscriptionResponse::Text {
            content_type: text_content_type("srt").into(),
            body: format!("1\n00:00:00,000 --> 00:00:01,000\n{text}\n\n"),
        },
        "vtt" => TranscriptionResponse::Text {
            content_type: text_content_type("vtt").into(),
            body: format!("WEBVTT\n\n00:00:00.000 --> 00:00:01.000\n{text}\n\n"),
        },
        other => TranscriptionResponse::Text { content_type: text_content_type(other).into(), body: text.to_owned() },
    }
}

/// The end of the last `srt`/`vtt` cue, in seconds (LiteLLM's
/// `extract_duration_from_srt_or_vtt`).
pub fn subtitle_end(text: &str) -> Option<f64> {
    text.lines().filter_map(|line| line.split_once("-->")).filter_map(|(_, end)| timestamp(end.split_whitespace().next()?)).reduce(f64::max)
}

/// `HH:MM:SS,mmm`, `HH:MM:SS.mmm` or `MM:SS.mmm`.
fn timestamp(s: &str) -> Option<f64> {
    let s = s.replace(',', ".");
    let parts: Vec<&str> = s.split(':').collect();
    let (h, m, sec) = match parts.as_slice() {
        [h, m, s] => (h.parse::<f64>().ok()?, m.parse::<f64>().ok()?, s.parse::<f64>().ok()?),
        [m, s] => (0.0, m.parse::<f64>().ok()?, s.parse::<f64>().ok()?),
        _ => return None,
    };
    Some(h * 3600.0 + m * 60.0 + sec)
}

pub(crate) fn speech_request(dep: &Deployment, req: &SpeechRequest) -> Result<HttpRequest, ProviderError> {
    let obj = openai::upstream_body(dep, req)?;
    Ok(openai::with_auth(dep, HttpRequest::new(openai::endpoint(dep, "audio/speech"), Value::Object(obj))))
}

/// The content type of a speech `response_format` (OpenAI's default is mp3).
pub(crate) fn speech_content_type(format: Option<&str>) -> &'static str {
    match format.unwrap_or("mp3") {
        "opus" => "audio/ogg",
        "aac" => "audio/aac",
        "flac" => "audio/flac",
        "wav" => "audio/wav",
        "pcm" => "audio/pcm",
        _ => "audio/mpeg",
    }
}

/// A tenth of a second of 8 kHz, 16-bit mono silence as WAV.
pub(crate) fn silent_wav() -> Bytes {
    let samples = 800u32;
    let data_len = samples * 2;
    let mut b = Vec::with_capacity(44 + data_len as usize);
    b.extend_from_slice(b"RIFF");
    b.extend_from_slice(&(36 + data_len).to_le_bytes());
    b.extend_from_slice(b"WAVEfmt ");
    b.extend_from_slice(&16u32.to_le_bytes());
    b.extend_from_slice(&1u16.to_le_bytes()); // PCM
    b.extend_from_slice(&1u16.to_le_bytes()); // mono
    b.extend_from_slice(&8000u32.to_le_bytes());
    b.extend_from_slice(&16000u32.to_le_bytes()); // byte rate
    b.extend_from_slice(&2u16.to_le_bytes()); // block align
    b.extend_from_slice(&16u16.to_le_bytes());
    b.extend_from_slice(b"data");
    b.extend_from_slice(&data_len.to_le_bytes());
    b.resize(44 + data_len as usize, 0);
    Bytes::from(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::media::{FilePart, audio_duration};

    fn dep(params: Value) -> Deployment {
        Deployment::from_litellm_params_with_env(&params, |_| None).unwrap()
    }

    fn form() -> MediaForm {
        MediaForm {
            model: "stt".into(),
            fields: vec![
                ("model".into(), "stt".into()),
                ("language".into(), "en".into()),
                ("response_format".into(), "verbose_json".into()),
                ("timestamp_granularities[]".into(), "word".into()),
                ("timestamp_granularities[]".into(), "segment".into()),
                ("mock_response".into(), "x".into()),
            ],
            files: vec![FilePart {
                field: "file".into(),
                filename: "a.wav".into(),
                content_type: Some("audio/wav".into()),
                data: Bytes::from_static(b"RIFFdata"),
            }],
        }
    }

    #[test]
    fn multipart_request() {
        let d = dep(json!({"model": "groq/whisper-large-v3", "api_key": "gk", "extra_body": {"temperature": 0}}));
        let (url, headers, m) = form_request(&d, "audio/transcriptions", &form());
        assert_eq!(url, "https://api.groq.com/openai/v1/audio/transcriptions");
        assert!(headers.contains(&("authorization".into(), "Bearer gk".into())));
        let (ct, body) = m.finish();
        let boundary = ct.strip_prefix("multipart/form-data; boundary=").unwrap();
        let body = String::from_utf8(body).unwrap();
        let parts: Vec<&str> = body.split(&format!("--{boundary}")).collect();
        // model, language, response_format, 2 granularities, temperature, file; no mock_response.
        assert_eq!(parts.len(), 9, "{body}");
        assert!(parts[1].contains("name=\"model\"\r\n\r\nwhisper-large-v3\r\n"));
        assert!(parts[4].contains("name=\"timestamp_granularities[]\"\r\n\r\nword"));
        assert!(parts[6].contains("name=\"temperature\"\r\n\r\n0\r\n"));
        assert!(parts[7].contains("filename=\"a.wav\"\r\nContent-Type: audio/wav\r\n\r\nRIFFdata\r\n"));
        assert!(!body.contains("mock_response"));
        assert_eq!(parts[8], "--\r\n");
    }

    #[test]
    fn azure_audio_urls() {
        let d = dep(json!({"model": "azure/whisper", "api_key": "k", "api_base": "https://r.openai.azure.com",
            "api_version": "2024-06-01"}));
        let (url, headers, _) = form_request(&d, "audio/translations", &form());
        assert_eq!(url, "https://r.openai.azure.com/openai/deployments/whisper/audio/translations?api-version=2024-06-01");
        assert!(headers.contains(&("api-key".into(), "k".into())));
        let tts = dep(json!({"model": "azure/tts", "api_key": "k", "api_base": "https://r.openai.azure.com",
            "api_version": "2024-06-01"}));
        let r: SpeechRequest = serde_json::from_value(json!({"model": "t", "input": "hi", "voice": "alloy"})).unwrap();
        let http = speech_request(&tts, &r).unwrap();
        assert_eq!(http.url, "https://r.openai.azure.com/openai/deployments/tts/audio/speech?api-version=2024-06-01");
        assert_eq!(http.body, json!({"model": "tts", "input": "hi", "voice": "alloy"}));
    }

    #[test]
    fn transcription_responses() {
        let d = dep(json!({"model": "openai/whisper-1", "api_key": "k"}));
        let mut f = form();
        let r = parse_transcription(&d, &f, Some("application/json"), r#"{"text": "hi", "duration": 12.5}"#.into()).unwrap();
        assert_eq!(r.duration(), Some(12.5));
        let r =
            parse_transcription(&d, &f, Some("application/json"), r#"{"text": "hi", "usage": {"type": "duration", "seconds": 3}}"#.into()).unwrap();
        assert_eq!(r.duration(), Some(3.0));
        assert_eq!(r.tokens(), None);
        let r = parse_transcription(
            &d,
            &f,
            None,
            r#"{"text": "hi", "usage": {"type": "tokens", "input_tokens": 120, "output_tokens": 20,
                "input_token_details": {"audio_tokens": 100, "text_tokens": 20}}}"#
                .into(),
        )
        .unwrap();
        let t = r.tokens().unwrap();
        assert_eq!((t.audio_tokens, t.text_tokens, t.output_tokens), (100, 20, 20));
        assert_eq!(r.duration(), None);
        f.fields.push(("response_format".into(), "srt".into()));
        let srt = "1\n00:00:00,000 --> 00:00:02,500\nHello\n\n2\n00:00:02,500 --> 00:01:04,250\nWorld\n";
        let r = parse_transcription(&d, &f, None, srt.into()).unwrap();
        assert_eq!(r, TranscriptionResponse::Text { content_type: "application/x-subrip; charset=utf-8".into(), body: srt.into() });
        assert_eq!(r.subtitle_end(), Some(64.25));
        let r = parse_transcription(&d, &f, Some("text/plain"), "hi".into()).unwrap();
        assert!(matches!(r, TranscriptionResponse::Text { ref content_type, .. } if content_type == "text/plain"));
        let e = parse_transcription(&d, &form(), Some("application/json"), r#"{"error": {"message": "no", "code": 429}}"#.into()).unwrap_err();
        assert_eq!(e.status_code(), 429);
    }

    #[test]
    fn subtitles() {
        assert_eq!(subtitle_end("WEBVTT\n\n00:01.000 --> 00:04.500\nhi\n"), Some(4.5));
        assert_eq!(subtitle_end("01:00:00.000 --> 01:00:01.000 align:start\n"), Some(3601.0));
        assert_eq!(subtitle_end("plain text"), None);
    }

    #[test]
    fn mock_audio() {
        let mut f = form();
        assert_eq!(mock_transcription(&f, "hi"), TranscriptionResponse::Json(json!({"task": "transcribe", "text": "hi", "segments": []})));
        f.fields.push(("response_format".into(), "text".into()));
        assert!(matches!(mock_transcription(&f, "hi"), TranscriptionResponse::Text { body, .. } if body == "hi"));
        let wav = silent_wav();
        let d = audio_duration(&wav);
        assert_eq!(d.estimate, Some(0.1));
        assert_eq!(speech_content_type(None), "audio/mpeg");
        assert_eq!(speech_content_type(Some("opus")), "audio/ogg");
    }
}
