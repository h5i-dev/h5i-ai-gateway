//! Image generation and edits: OpenAI-shaped upstreams (OpenAI, Azure,
//! OpenAI-compatible) and Gemini (Imagen `:predict`, Gemini image models
//! `:generateContent`, following LiteLLM's `GoogleImageGenConfig`).

use serde_json::{Map, Value, json};

use super::{ImageData, ImageRequest, ImageResponse, ImageTokenDetails, ImageUsage};
use crate::deployment::Deployment;
use crate::error::ProviderError;
use crate::providers::{HttpRequest, gemini, mock, now_unix, openai, parse_json};

/// gpt-image models take neither `response_format` (they always return
/// `b64_json`) nor `style`.
pub(crate) fn is_gpt_image(model: &str) -> bool {
    model.contains("gpt-image")
}

/// LiteLLM's `is_gemini_image_model`: Gemini models generate images with
/// `generateContent`; every other Google model (Imagen) uses `predict`.
pub(crate) fn is_gemini_image_model(model: &str) -> bool {
    model.rsplit('/').next().unwrap_or(model).contains("gemini")
}

pub(crate) fn openai_request(
    dep: &Deployment,
    req: &ImageRequest,
) -> Result<HttpRequest, ProviderError> {
    let mut obj = openai::upstream_body(dep, req)?;
    if is_gpt_image(&dep.model) {
        obj.remove("response_format");
        obj.remove("style");
    }
    Ok(openai::with_auth(
        dep,
        HttpRequest::new(
            openai::endpoint(dep, "images/generations"),
            Value::Object(obj),
        ),
    ))
}

pub(crate) fn parse_openai(dep: &Deployment, body: &str) -> Result<ImageResponse, ProviderError> {
    if let Some(e) = openai::embedded_error(dep.provider.name(), body) {
        return Err(e);
    }
    let mut resp: ImageResponse = parse_json(dep.provider.name(), body)?;
    if resp.created == 0 {
        resp.created = now_unix();
    }
    Ok(resp)
}

/// `"1792x1024"` -> `(1792, 1024)`.
pub(crate) fn parse_size(size: &str) -> Option<(u64, u64)> {
    let (w, h) = size.split_once(['x', 'X'])?;
    Some((w.trim().parse().ok()?, h.trim().parse().ok()?))
}

/// The supported aspect ratio closest to `width:height`.
fn aspect_ratio(width: u64, height: u64, supported: &[&'static str]) -> &'static str {
    let target = (width.max(1) as f64 / height.max(1) as f64).ln();
    let ratio = |r: &str| {
        let (a, b) = r.split_once(':').unwrap_or(("1", "1"));
        (a.parse::<f64>().unwrap_or(1.0) / b.parse::<f64>().unwrap_or(1.0)).ln()
    };
    supported
        .iter()
        .min_by(|a, b| {
            (ratio(a) - target)
                .abs()
                .total_cmp(&(ratio(b) - target).abs())
        })
        .copied()
        .unwrap_or("1:1")
}

const GEMINI_RATIOS: &[&str] = &[
    "1:1", "2:3", "3:2", "3:4", "4:3", "4:5", "5:4", "9:16", "16:9", "21:9",
];
const IMAGEN_RATIOS: &[&str] = &["1:1", "3:4", "4:3", "9:16", "16:9"];
/// Imagen parameters passed through from the request's extra fields.
const IMAGEN_PASSTHROUGH: &[&str] = &[
    "personGeneration",
    "safetyFilterLevel",
    "addWatermark",
    "enhancePrompt",
    "negativePrompt",
    "outputOptions",
    "language",
];

pub(crate) fn gemini_request(
    dep: &Deployment,
    req: &ImageRequest,
) -> Result<HttpRequest, ProviderError> {
    let n = req.n.unwrap_or(1).max(1);
    let size = req.size.as_deref().and_then(parse_size);
    if is_gemini_image_model(&dep.model) {
        let mut image_config = Map::new();
        if let Some((w, h)) = size {
            image_config.insert(
                "aspectRatio".into(),
                aspect_ratio(w, h, GEMINI_RATIOS).into(),
            );
            // gemini-2.5-flash-image takes no imageSize (LiteLLM's supports_gemini_image_size).
            if !dep.model.contains("2.5-flash") {
                let image_size = match w.max(h) {
                    0..=1024 => "1K",
                    1025..=2048 => "2K",
                    _ => "4K",
                };
                image_config.insert("imageSize".into(), image_size.into());
            }
        }
        if let Some(Value::Object(extra)) = req.extra.get("imageConfig") {
            image_config.extend(extra.clone());
        }
        let mut generation = Map::new();
        generation.insert("responseModalities".into(), json!(["IMAGE", "TEXT"]));
        if n > 1 {
            generation.insert("candidateCount".into(), n.into());
        }
        if !image_config.is_empty() {
            generation.insert("imageConfig".into(), Value::Object(image_config));
        }
        let mut body = json!({
            "contents": [{"role": "user", "parts": [{"text": req.prompt}]}],
            "generationConfig": generation,
        });
        if let Some(tools) = req.extra.get("tools") {
            body["tools"] = tools.clone();
        }
        return Ok(HttpRequest::new(
            gemini::model_url(dep, "generateContent", false),
            body,
        ));
    }
    let mut parameters = Map::new();
    parameters.insert("sampleCount".into(), n.into());
    if let Some((w, h)) = size {
        parameters.insert(
            "aspectRatio".into(),
            aspect_ratio(w, h, IMAGEN_RATIOS).into(),
        );
        if w.max(h) > 1024 {
            parameters.insert("sampleImageSize".into(), "2K".into());
        }
    }
    for key in IMAGEN_PASSTHROUGH {
        if let Some(v) = req.extra.get(*key) {
            parameters.insert((*key).to_owned(), v.clone());
        }
    }
    let body = json!({"instances": [{"prompt": req.prompt}], "parameters": parameters});
    Ok(HttpRequest::new(
        gemini::model_url(dep, "predict", false),
        body,
    ))
}

/// Sum `[{modality, tokenCount}]` into text and image tokens.
fn modality_tokens(details: Option<&Value>) -> Option<ImageTokenDetails> {
    let list = details?.as_array()?;
    let mut out = ImageTokenDetails::default();
    for d in list {
        let n = d.get("tokenCount").and_then(Value::as_u64).unwrap_or(0);
        match d.get("modality").and_then(Value::as_str) {
            Some("IMAGE") => out.image_tokens += n,
            _ => out.text_tokens += n,
        }
    }
    Some(out)
}

/// `usageMetadata` -> image usage (LiteLLM `transform_gemini_image_usage`),
/// counting thinking tokens as text output.
fn gemini_usage(m: &Value) -> ImageUsage {
    let get = |k: &str| m.get(k).and_then(Value::as_u64).unwrap_or(0);
    let input = get("promptTokenCount");
    let candidates = get("candidatesTokenCount");
    let thoughts = get("thoughtsTokenCount");
    let input_details =
        modality_tokens(m.get("promptTokensDetails")).unwrap_or(ImageTokenDetails {
            text_tokens: input,
            ..ImageTokenDetails::default()
        });
    let mut output_details = match modality_tokens(m.get("candidatesTokensDetails")) {
        Some(mut d) => {
            let known = d.text_tokens + d.image_tokens;
            d.text_tokens += candidates.saturating_sub(known);
            d
        }
        None => ImageTokenDetails {
            image_tokens: candidates,
            ..ImageTokenDetails::default()
        },
    };
    output_details.text_tokens += thoughts;
    ImageUsage {
        input_tokens: input,
        output_tokens: candidates + thoughts,
        total_tokens: get("totalTokenCount").max(input + candidates + thoughts),
        input_tokens_details: Some(input_details),
        output_tokens_details: Some(output_details),
        ..ImageUsage::default()
    }
}

pub(crate) fn parse_gemini(dep: &Deployment, body: &str) -> Result<ImageResponse, ProviderError> {
    let v: Value = parse_json(dep.provider.name(), body)?;
    if v.get("error").is_some_and(|e| !e.is_null()) {
        let status = v["error"]["code"]
            .as_u64()
            .filter(|c| (400..=599).contains(c))
            .unwrap_or(500) as u16;
        return Err(ProviderError::from_upstream(
            dep.provider.name(),
            status,
            body,
            None,
        ));
    }
    let mut data = Vec::new();
    // Imagen: predictions[].bytesBase64Encoded (filtered images carry only a reason).
    for p in v["predictions"].as_array().into_iter().flatten() {
        if let Some(b64) = p.get("bytesBase64Encoded").and_then(Value::as_str) {
            data.push(ImageData {
                b64_json: Some(b64.to_owned()),
                revised_prompt: p.get("prompt").and_then(Value::as_str).map(str::to_owned),
                ..ImageData::default()
            });
        }
    }
    // Gemini: inlineData parts of each candidate.
    for c in v["candidates"].as_array().into_iter().flatten() {
        for part in c["content"]["parts"].as_array().into_iter().flatten() {
            if let Some(b64) = part["inlineData"]["data"].as_str() {
                data.push(ImageData {
                    b64_json: Some(b64.to_owned()),
                    ..ImageData::default()
                });
            }
        }
    }
    Ok(ImageResponse {
        created: now_unix(),
        data,
        usage: v.get("usageMetadata").map(gemini_usage),
        extra: Map::new(),
    })
}

/// `n` copies of the canned image URL (LiteLLM's `mock_image_generation`).
pub(crate) fn mock(
    dep: &Deployment,
    n: Option<u32>,
    text: &str,
) -> Result<ImageResponse, ProviderError> {
    mock::check_error_trigger(dep, text)?;
    let data = (0..n.unwrap_or(1).clamp(1, 10))
        .map(|_| ImageData {
            url: Some(text.to_owned()),
            ..ImageData::default()
        })
        .collect();
    Ok(ImageResponse {
        created: now_unix(),
        data,
        usage: None,
        extra: Map::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::ErrorKind;

    fn dep(params: Value) -> Deployment {
        Deployment::from_litellm_params_with_env(&params, |_| None).unwrap()
    }

    fn req(v: Value) -> ImageRequest {
        serde_json::from_value(v).unwrap()
    }

    #[test]
    fn openai_request_passes_fields_through() {
        let d = dep(json!({"model": "openai/dall-e-3", "api_key": "sk", "extra_body": {"x": 1}}));
        let r = req(
            json!({"model": "img", "prompt": "a cat", "n": 1, "size": "1024x1792",
            "quality": "hd", "style": "vivid", "response_format": "b64_json", "user": "u",
            "mock_response": "nope", "metadata": {"a": 1}, "output_compression": 50}),
        );
        let http = openai_request(&d, &r).unwrap();
        assert_eq!(http.url, "https://api.openai.com/v1/images/generations");
        assert!(
            http.headers
                .contains(&("authorization".into(), "Bearer sk".into()))
        );
        assert_eq!(
            http.body,
            json!({"model": "dall-e-3", "prompt": "a cat", "n": 1, "size": "1024x1792", "quality": "hd",
                "style": "vivid", "response_format": "b64_json", "user": "u", "output_compression": 50, "x": 1})
        );
        // gpt-image drops what it does not take.
        let g = dep(json!({"model": "openai/gpt-image-1", "api_key": "sk"}));
        let body = openai_request(&g, &r).unwrap().body;
        assert!(body.get("response_format").is_none() && body.get("style").is_none());
        assert_eq!(body["quality"], "hd");
    }

    #[test]
    fn azure_url_shape() {
        let d = dep(
            json!({"model": "azure/my-dalle", "api_key": "k", "api_base": "https://r.openai.azure.com/",
            "api_version": "2024-02-01"}),
        );
        let http = openai_request(&d, &req(json!({"prompt": "x"}))).unwrap();
        assert_eq!(
            http.url,
            "https://r.openai.azure.com/openai/deployments/my-dalle/images/generations?api-version=2024-02-01"
        );
        assert!(http.headers.contains(&("api-key".into(), "k".into())));
    }

    #[test]
    fn parses_openai_responses() {
        let d = dep(json!({"model": "openai/gpt-image-1", "api_key": "sk"}));
        let r = parse_openai(
            &d,
            r#"{"created": 5, "data": [{"b64_json": "AAA", "revised_prompt": "rp"}], "size": "1024x1536", "quality": "high",
                "usage": {"input_tokens": 10, "output_tokens": 6240, "total_tokens": 6250,
                          "input_tokens_details": {"text_tokens": 10, "image_tokens": 0}}}"#,
        )
        .unwrap();
        assert_eq!(r.created, 5);
        assert_eq!(r.data[0].b64_json.as_deref(), Some("AAA"));
        assert_eq!(r.data[0].revised_prompt.as_deref(), Some("rp"));
        assert_eq!(r.reported("size"), Some("1024x1536"));
        let u = r.usage.unwrap();
        assert_eq!((u.input_tokens, u.output_tokens), (10, 6240));
        assert_eq!(u.input_tokens_details.unwrap().text_tokens, 10);
        let e = parse_openai(&d, r#"{"error": {"message": "bad", "code": 400}}"#).unwrap_err();
        assert_eq!(e.status_code(), 400);
        assert_eq!(
            parse_openai(&d, "nope").unwrap_err().kind(),
            ErrorKind::InvalidResponse
        );
    }

    #[test]
    fn imagen_request_and_response() {
        let d = dep(json!({"model": "gemini/imagen-3.0-generate-002", "api_key": "g"}));
        let r = req(
            json!({"prompt": "a dog", "n": 2, "size": "1792x1024", "personGeneration": "allow_adult"}),
        );
        let http = gemini_request(&d, &r).unwrap();
        assert_eq!(
            http.url,
            "https://generativelanguage.googleapis.com/v1beta/models/imagen-3.0-generate-002:predict?key=g"
        );
        assert_eq!(
            http.body,
            json!({"instances": [{"prompt": "a dog"}], "parameters": {"sampleCount": 2, "aspectRatio": "16:9",
                "sampleImageSize": "2K", "personGeneration": "allow_adult"}})
        );
        let resp = parse_gemini(
            &d,
            r#"{"predictions": [{"bytesBase64Encoded": "AAA", "mimeType": "image/png"}, {"raiFilteredReason": "x"}]}"#,
        )
        .unwrap();
        assert_eq!(resp.data.len(), 1);
        assert!(resp.usage.is_none());
    }

    #[test]
    fn gemini_image_model_request_and_response() {
        let d = dep(json!({"model": "gemini/gemini-2.5-flash-image", "api_key": "g"}));
        let http =
            gemini_request(&d, &req(json!({"prompt": "a dog", "size": "1024x1024"}))).unwrap();
        assert!(
            http.url
                .ends_with("/models/gemini-2.5-flash-image:generateContent?key=g")
        );
        assert_eq!(
            http.body,
            json!({"contents": [{"role": "user", "parts": [{"text": "a dog"}]}],
                "generationConfig": {"responseModalities": ["IMAGE", "TEXT"], "imageConfig": {"aspectRatio": "1:1"}}})
        );
        let pro = dep(json!({"model": "gemini/gemini-3-pro-image-preview", "api_key": "g"}));
        let body = gemini_request(
            &pro,
            &req(json!({"prompt": "x", "size": "4096x4096", "n": 2})),
        )
        .unwrap()
        .body;
        assert_eq!(body["generationConfig"]["imageConfig"]["imageSize"], "4K");
        assert_eq!(body["generationConfig"]["candidateCount"], 2);
        let resp = parse_gemini(
            &d,
            r#"{"candidates": [{"content": {"parts": [{"text": "here"}, {"inlineData": {"mimeType": "image/png", "data": "QQ"}}]}}],
                "usageMetadata": {"promptTokenCount": 5, "candidatesTokenCount": 1300, "thoughtsTokenCount": 20, "totalTokenCount": 1325,
                  "candidatesTokensDetails": [{"modality": "IMAGE", "tokenCount": 1290}]}}"#,
        )
        .unwrap();
        assert_eq!(resp.data.len(), 1);
        assert_eq!(resp.data[0].b64_json.as_deref(), Some("QQ"));
        let u = resp.usage.unwrap();
        assert_eq!(u.output_tokens, 1320);
        let out = u.output_tokens_details.unwrap();
        assert_eq!((out.image_tokens, out.text_tokens), (1290, 30));
        let e = parse_gemini(
            &d,
            r#"{"error": {"code": 429, "message": "slow down", "status": "RESOURCE_EXHAUSTED"}}"#,
        )
        .unwrap_err();
        assert_eq!(e.status_code(), 429);
    }

    #[test]
    fn sizes_and_ratios() {
        assert_eq!(parse_size("1024x1792"), Some((1024, 1792)));
        assert_eq!(parse_size("auto"), None);
        assert_eq!(aspect_ratio(1024, 1792, IMAGEN_RATIOS), "9:16");
        assert_eq!(aspect_ratio(1536, 1024, GEMINI_RATIOS), "3:2");
        assert_eq!(aspect_ratio(1536, 1024, IMAGEN_RATIOS), "4:3");
    }

    #[test]
    fn mocks() {
        let d = dep(json!({"model": "mock/img"}));
        let r = mock(&d, Some(3), "https://x/y.png").unwrap();
        assert_eq!(r.data.len(), 3);
        assert_eq!(r.data[2].url.as_deref(), Some("https://x/y.png"));
        assert_eq!(
            mock(&d, None, "litellm.RateLimitError").unwrap_err().kind(),
            ErrorKind::RateLimited
        );
    }
}
