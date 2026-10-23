//! Images and audio: `/v1/images/generations`, `/v1/images/edits`,
//! `/v1/audio/transcriptions`, `/v1/audio/translations`, `/v1/audio/speech`
//! (also without `/v1`, and Azure's `/openai/deployments/{model}/...`).
//!
//! Each request goes through [`proxy::call`]: admission reserves the call's
//! worst case in the deployment's media units, the provider is called, and
//! settlement charges the units the response used. [`pricing`] defines the
//! units (images, seconds of audio, characters) and how each request and
//! response is counted in them; the reservation is an upper bound of the
//! settlement whenever the provider does what was asked.
//!
//! A deployment serves these endpoints if its mode is the endpoint's
//! (`image_generation`/`image_edit`, `audio_transcription`, `audio_speech`,
//! from `model_info.mode` or LiteLLM's table) or unknown (then it is
//! unpriced). Uploads are limited to [`MAX_UPLOAD_BYTES`].

pub mod pricing;

use crate::AppState;
use crate::error::ApiError;
use crate::kernel::Gateway;
use crate::proxy::{self, CallInfo, Failure, Units};
use crate::registry::Deployed;
use axum::Router;
use axum::body::Body;
use axum::extract::multipart::MultipartRejection;
use axum::extract::{DefaultBodyLimit, Multipart, Path, State};
use axum::http::{HeaderMap, HeaderValue, StatusCode, header};
use axum::response::{IntoResponse, Response};
use axum::routing::post;
use axum::{Json, http};
use gateway_providers::media::{FilePart, ImageRequest, MediaForm, SpeechRequest, TranscriptionResponse, audio_duration};
use gateway_providers::{ErrorKind, ProviderError};
use h5i_app_http::Actor;
use pricing::{AudioAsk, Endpoint, ImageAsk, MediaPricing};
use serde_json::Value;

/// The largest request body the media routes accept (uploads for edits and
/// transcriptions).
pub const MAX_UPLOAD_BYTES: usize = 64 * 1024 * 1024;

/// The routes of this module.
pub fn routes() -> Router<AppState> {
    Router::new()
        .route("/v1/images/generations", post(image_generations))
        .route("/images/generations", post(image_generations))
        .route("/openai/deployments/{model}/images/generations", post(azure_image_generations))
        .route("/v1/images/edits", post(image_edits))
        .route("/images/edits", post(image_edits))
        .route("/openai/deployments/{model}/images/edits", post(azure_image_edits))
        .route("/v1/audio/transcriptions", post(transcriptions))
        .route("/audio/transcriptions", post(transcriptions))
        .route("/openai/deployments/{model}/audio/transcriptions", post(azure_transcriptions))
        .route("/v1/audio/translations", post(translations))
        .route("/audio/translations", post(translations))
        .route("/openai/deployments/{model}/audio/translations", post(azure_translations))
        .route("/v1/audio/speech", post(speech))
        .route("/audio/speech", post(speech))
        .route("/openai/deployments/{model}/audio/speech", post(azure_speech))
        .layer(DefaultBodyLimit::max(MAX_UPLOAD_BYTES))
}

/// The largest reservation any deployment that may serve `model` (its
/// group, after aliases, and its fallback groups) needs, so that whichever
/// one the kernel picks is covered.
fn group_bound(st: &AppState, model: &str, unit: impl Fn(&MediaPricing) -> Option<Units>) -> Units {
    let model = st.settings.aliases.get(model).map_or(model, String::as_str);
    let mut groups = vec![model];
    groups.extend(st.settings.fallbacks.get(model).into_iter().flatten().map(String::as_str));
    let mut bound = Units::default();
    for d in st.registry.all().into_iter().filter(|d| groups.contains(&d.model_name.as_str())) {
        if let Some(u) = d.media.as_ref().and_then(&unit) {
            bound.prompt = bound.prompt.max(u.prompt);
            bound.completion = bound.completion.max(u.completion);
        }
    }
    bound
}

/// The deployment's media pricing if it serves `endpoint`; `None` for an
/// unpriced deployment of unknown mode.
fn media_for(d: &Deployed, endpoint: Endpoint) -> Result<Option<&MediaPricing>, ProviderError> {
    match (&d.media, &d.mode) {
        (Some(m), _) if m.serves(endpoint) => Ok(Some(m)),
        (None, None) => Ok(None),
        (_, mode) => Err(ProviderError::new(
            ErrorKind::BadRequest,
            d.deployment.provider.name(),
            format!("model '{}' ({} deployment) does not support {}", d.model_name, mode.as_deref().unwrap_or("unknown"), endpoint.path()),
        )),
    }
}

fn respond<T>(result: Result<(T, CallInfo), Failure>, f: impl FnOnce(T, HeaderMap) -> Response) -> Response {
    match result {
        Ok((out, info)) => f(out, info.headers()),
        Err(e) => e.into_response(),
    }
}

fn with_content_type(mut h: HeaderMap, content_type: &str) -> HeaderMap {
    if let Ok(v) = HeaderValue::from_str(content_type) {
        h.insert(header::CONTENT_TYPE, v);
    }
    h
}

/// Read a multipart request: text fields (the `model` apart) and files.
async fn read_form(multipart: Result<Multipart, MultipartRejection>, model: Option<String>) -> Result<MediaForm, Failure> {
    let bad = |status: StatusCode, msg: String| Failure::Api(ApiError::new(status, "invalid_request_error", msg));
    let mut mp = multipart.map_err(|e| bad(e.status(), e.body_text()))?;
    let mut form = MediaForm::default();
    while let Some(field) = mp.next_field().await.map_err(|e| bad(e.status(), e.body_text()))? {
        let name = field.name().unwrap_or_default().to_owned();
        let filename = field.file_name().map(str::to_owned);
        let content_type = field.content_type().map(str::to_owned);
        let data = field.bytes().await.map_err(|e| bad(e.status(), e.body_text()))?;
        match filename {
            Some(filename) => form.files.push(FilePart { field: name, filename, content_type, data }),
            None => {
                let text =
                    String::from_utf8(data.to_vec()).map_err(|_| bad(StatusCode::BAD_REQUEST, format!("form field '{name}' is not UTF-8 text")))?;
                if name == "model" {
                    form.model = text;
                } else {
                    form.fields.push((name, text));
                }
            }
        }
    }
    if let Some(m) = model {
        form.model = m;
    }
    if form.model.is_empty() {
        return Err(bad(StatusCode::BAD_REQUEST, "the 'model' field is required".into()));
    }
    Ok(form)
}

fn set_model(body: &mut Value, model: String) {
    if let Some(o) = body.as_object_mut() {
        o.insert("model".into(), Value::String(model));
    }
}

// ---------------------------------------------------------------------------
// Images

pub async fn image_generations(State(st): State<AppState>, actor: Actor<Gateway>, Json(body): Json<Value>) -> Response {
    let req = match proxy::parse::<ImageRequest>(body) {
        Ok(r) => r,
        Err(f) => return f.into_response(),
    };
    let ask =
        ImageAsk { n: req.n.unwrap_or(1).into(), size: req.size.clone(), quality: req.quality.clone(), prompt: req.prompt.clone(), input_images: 0 };
    let bound = group_bound(&st, &req.model, |m| match m {
        MediaPricing::Images(p) => Some(p.reserve(&ask)),
        _ => None,
    });
    let client = st.client.clone();
    let result = proxy::call(&st, *actor.principal(), &req.model, bound.prompt, bound.completion, |d| {
        let (client, d, req, ask) = (client.clone(), d.clone(), req.clone(), ask.clone());
        async move {
            let media = media_for(&d, Endpoint::ImageGeneration)?.cloned();
            let resp = client.image_generation(&d.deployment, &req).await?;
            let used = match &media {
                Some(MediaPricing::Images(p)) => p.settle(&ask, &resp),
                _ => Units::default(),
            };
            Ok((resp, used))
        }
    })
    .await;
    respond(result, |resp, h| (h, Json(resp)).into_response())
}

pub async fn azure_image_generations(st: State<AppState>, Path(model): Path<String>, actor: Actor<Gateway>, Json(mut body): Json<Value>) -> Response {
    set_model(&mut body, model);
    image_generations(st, actor, Json(body)).await
}

async fn edit(st: AppState, actor: Actor<Gateway>, model: Option<String>, multipart: Result<Multipart, MultipartRejection>) -> Response {
    let form = match read_form(multipart, model).await {
        Ok(f) => f,
        Err(f) => return f.into_response(),
    };
    let ask = ImageAsk {
        n: form.field("n").and_then(|n| n.parse().ok()).unwrap_or(1),
        size: form.field("size").map(str::to_owned),
        quality: form.field("quality").map(str::to_owned),
        prompt: form.field("prompt").unwrap_or_default().to_owned(),
        input_images: form.files.iter().filter(|f| f.field.starts_with("image")).count() as u64,
    };
    let bound = group_bound(&st, &form.model, |m| match m {
        MediaPricing::Images(p) => Some(p.reserve(&ask)),
        _ => None,
    });
    let client = st.client.clone();
    let result = proxy::call(&st, *actor.principal(), &form.model, bound.prompt, bound.completion, |d| {
        let (client, d, form, ask) = (client.clone(), d.clone(), form.clone(), ask.clone());
        async move {
            let media = media_for(&d, Endpoint::ImageEdit)?.cloned();
            let resp = client.image_edit(&d.deployment, &form).await?;
            let used = match &media {
                Some(MediaPricing::Images(p)) => p.settle(&ask, &resp),
                _ => Units::default(),
            };
            Ok((resp, used))
        }
    })
    .await;
    respond(result, |resp, h| (h, Json(resp)).into_response())
}

pub async fn image_edits(State(st): State<AppState>, actor: Actor<Gateway>, multipart: Result<Multipart, MultipartRejection>) -> Response {
    edit(st, actor, None, multipart).await
}

pub async fn azure_image_edits(
    State(st): State<AppState>,
    Path(model): Path<String>,
    actor: Actor<Gateway>,
    multipart: Result<Multipart, MultipartRejection>,
) -> Response {
    edit(st, actor, Some(model), multipart).await
}

// ---------------------------------------------------------------------------
// Transcriptions and translations

async fn transcribe(
    st: AppState,
    actor: Actor<Gateway>,
    model: Option<String>,
    multipart: Result<Multipart, MultipartRejection>,
    translate: bool,
) -> Response {
    let form = match read_form(multipart, model).await {
        Ok(f) => f,
        Err(f) => return f.into_response(),
    };
    let Some(file) = form.file("file") else {
        return ApiError::bad_request("the 'file' field is required").into_response();
    };
    if form.field("stream") == Some("true") {
        return ApiError::bad_request("streamed transcriptions are not supported; omit 'stream'").into_response();
    }
    let duration = audio_duration(&file.data);
    let ask = AudioAsk { bound_seconds: duration.bound, estimate: duration.estimate, prompt: form.field("prompt").unwrap_or_default().to_owned() };
    let bound = group_bound(&st, &form.model, |m| match m {
        MediaPricing::Transcription(p) => Some(p.reserve(&ask)),
        _ => None,
    });
    let client = st.client.clone();
    let result = proxy::call(&st, *actor.principal(), &form.model, bound.prompt, bound.completion, |d| {
        let (client, d, form, ask) = (client.clone(), d.clone(), form.clone(), ask.clone());
        async move {
            let media = media_for(&d, Endpoint::Transcription)?.cloned();
            let resp = client.transcription(&d.deployment, &form, translate).await?;
            let used = match &media {
                Some(MediaPricing::Transcription(p)) => p.settle(&ask, &resp),
                _ => Units::default(),
            };
            Ok((resp, used))
        }
    })
    .await;
    respond(result, |resp, h| match resp {
        TranscriptionResponse::Json(v) => (h, Json(v)).into_response(),
        TranscriptionResponse::Text { content_type, body } => (with_content_type(h, &content_type), body).into_response(),
    })
}

pub async fn transcriptions(State(st): State<AppState>, actor: Actor<Gateway>, multipart: Result<Multipart, MultipartRejection>) -> Response {
    transcribe(st, actor, None, multipart, false).await
}

pub async fn translations(State(st): State<AppState>, actor: Actor<Gateway>, multipart: Result<Multipart, MultipartRejection>) -> Response {
    transcribe(st, actor, None, multipart, true).await
}

pub async fn azure_transcriptions(
    State(st): State<AppState>,
    Path(model): Path<String>,
    actor: Actor<Gateway>,
    multipart: Result<Multipart, MultipartRejection>,
) -> Response {
    transcribe(st, actor, Some(model), multipart, false).await
}

pub async fn azure_translations(
    State(st): State<AppState>,
    Path(model): Path<String>,
    actor: Actor<Gateway>,
    multipart: Result<Multipart, MultipartRejection>,
) -> Response {
    transcribe(st, actor, Some(model), multipart, true).await
}

// ---------------------------------------------------------------------------
// Speech

pub async fn speech(State(st): State<AppState>, actor: Actor<Gateway>, Json(body): Json<Value>) -> Response {
    let req = match proxy::parse::<SpeechRequest>(body) {
        Ok(r) => r,
        Err(f) => return f.into_response(),
    };
    let bound = group_bound(&st, &req.model, |m| match m {
        MediaPricing::Speech(p) => Some(p.units(&req.input)),
        _ => None,
    });
    let client = st.client.clone();
    let result = proxy::call(&st, *actor.principal(), &req.model, bound.prompt, bound.completion, |d| {
        let (client, d, req) = (client.clone(), d.clone(), req.clone());
        async move {
            let media = media_for(&d, Endpoint::Speech)?.cloned();
            // Settled when the audio starts: its cost is known from the input.
            let resp = client.speech(&d.deployment, &req).await?;
            let used = match &media {
                Some(MediaPricing::Speech(p)) => p.units(&req.input),
                _ => Units::default(),
            };
            Ok((resp, used))
        }
    })
    .await;
    respond(result, |resp, h| {
        let h = with_content_type(h, &resp.content_type);
        (http::StatusCode::OK, h, Body::from_stream(resp.body)).into_response()
    })
}

pub async fn azure_speech(st: State<AppState>, Path(model): Path<String>, actor: Actor<Gateway>, Json(mut body): Json<Value>) -> Response {
    set_model(&mut body, model);
    speech(st, actor, Json(body)).await
}
