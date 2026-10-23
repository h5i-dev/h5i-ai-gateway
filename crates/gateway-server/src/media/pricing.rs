//! Units and per-unit prices of media deployments.
//!
//! The kernel prices every call as `prompt_units * input_cost +
//! completion_units * output_cost` (nano-dollars per unit) at the prices of
//! the deployment it picks, and reserves that for the worst case before the
//! call. A media deployment's `input_cost`/`output_cost` are therefore prices
//! per *media unit*, chosen here from its mode, and each endpoint counts its
//! request and response in those units:
//!
//! | Mode | Prompt unit (`input_cost`) | Completion unit (`output_cost`) |
//! |---|---|---|
//! | `image_generation`, `image_edit`, per-image priced (DALL-E, Imagen) | prompt text token (usually free) | 1/1000 of the deployment's most expensive image variant |
//! | `image_generation`, `image_edit`, token priced (gpt-image, Gemini image models) | prompt text token | output image token |
//! | `audio_transcription` | second of audio | output text token (token-priced models only) |
//! | `audio_speech` | input character (or estimated token for token-priced TTS) | — |
//!
//! **Images, per image.** A size/quality variant costing `p` is
//! `ceil(p / u)` completion units per image, where the unit price `u` is a
//! thousandth of the most expensive variant (rounded up to a nano-dollar).
//! The reservation is `n` images at the most expensive variant consistent
//! with the request's `size` and `quality` (all variants when either is
//! `auto` or missing); settlement counts the images returned at the variant
//! they were generated at (as reported by the upstream, else as requested).
//! Settled units never exceed the reservation unless the upstream returns
//! more images, or another size, than asked; rounding overcharges by less
//! than one unit (0.1% of the top price) per image.
//!
//! **Images, per token.** gpt-image and Gemini image models report token
//! usage; settlement charges it (input image tokens converted to prompt
//! units at the input-image/text price ratio; output text and thinking
//! tokens to image-token units at their price ratio). The reservation is
//! the prompt's UTF-8 length (a bound on its tokens) plus, per input image
//! of an edit, 8,000 image tokens; and per output image, the larger of the
//! table's flat per-image price expressed in tokens and OpenAI's token
//! counts (272 / 1,056 / 4,160 tokens per megapixel at low / medium / high
//! quality; Gemini: 1,400, or 2,600 above 2K), plus 2,048 text tokens for
//! models that also bill text output. Token counts are the provider's: like
//! a chat prompt, they can exceed an estimate, and are then charged in full.
//!
//! **Transcription.** One unit is one second of audio, at the model's
//! per-second price (`output_cost_per_second` if set, else
//! `input_cost_per_second`, as LiteLLM; for token-only models, the
//! input-audio-token price times 20 tokens per second). The reservation is
//! the upload's duration bound ([`audio_duration`]); settlement uses the
//! provider's reported duration, else the container's, else the last
//! subtitle cue, else the bound — rounded up to whole seconds. Token-priced
//! models that report token usage are charged it instead: audio and text
//! input converted to seconds at their price ratio, output tokens as
//! completion units (reserved at 16 per second plus 64, capped by the
//! model's output limit).
//!
//! **Speech.** One unit is one input character at `input_cost_per_character`
//! (LiteLLM's `cost_per_character` metric), known before the call, so the
//! reservation is exact. Token-priced TTS models (gpt-4o-mini-tts) are
//! charged their input text tokens, estimated as characters / 4, like LiteLLM
//! (which does not price the audio output of these models either).
//!
//! A model group should contain deployments of one kind. When it mixes
//! them, the reservation is the largest of each deployment's own, which is
//! still an upper bound for whichever deployment the kernel picks.
//!
//! [`audio_duration`]: gateway_providers::media::audio_duration

use crate::proxy::{Units, estimate_text};
use gateway_providers::media::{ImageResponse, TranscriptionResponse};
use gateway_providers::pricing::{self, ImageVariant, Pricing};
use gateway_providers::{Deployment, Provider};
use serde_json::{Map, Value};

/// Completion units per image at the most expensive variant.
pub const UNITS_PER_TOP_IMAGE: u64 = 1000;
/// Image tokens reserved per input image of an edit.
pub const INPUT_IMAGE_TOKENS: u64 = 8_000;
/// Text (and thinking) output tokens reserved for image models that bill them.
pub const IMAGE_TEXT_ALLOWANCE: u64 = 2_048;
/// Input audio tokens per second assumed for token-only transcription prices.
pub const AUDIO_TOKENS_PER_SECOND: f64 = 20.0;
/// Output text tokens per second of audio reserved for token-priced transcription.
pub const TRANSCRIPT_TOKENS_PER_SECOND: f64 = 16.0;

/// USD -> nano-dollars, rounded up.
fn nano(usd: f64) -> u64 {
    pricing::to_nano_per_token(usd)
}

/// `tokens` priced at `from` nano-dollars, in units of `to` nano-dollars (rounded up).
fn convert(tokens: u64, from: u64, to: u64) -> u64 {
    if to == 0 {
        return tokens;
    }
    let v = (u128::from(tokens) * u128::from(from)).div_ceil(u128::from(to));
    u64::try_from(v).unwrap_or(u64::MAX)
}

fn ceil_secs(s: f64) -> u64 {
    if s.is_finite() && s > 0.0 { s.ceil() as u64 } else { 0 }
}

/// The prices a deployment has: LiteLLM's table entry with `litellm_params`
/// and `model_info` overrides (the deployment's own prices win, as in
/// LiteLLM).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Prices {
    pub mode: Option<String>,
    pub input_cost_per_token: Option<f64>,
    pub output_cost_per_token: Option<f64>,
    pub input_cost_per_image: Option<f64>,
    pub output_cost_per_image: Option<f64>,
    pub input_cost_per_pixel: Option<f64>,
    pub input_cost_per_image_token: Option<f64>,
    pub output_cost_per_image_token: Option<f64>,
    pub input_cost_per_second: Option<f64>,
    pub output_cost_per_second: Option<f64>,
    pub input_cost_per_character: Option<f64>,
    pub input_cost_per_audio_token: Option<f64>,
    pub max_output_tokens: Option<u64>,
    /// Whether the deployment sets its own per-image price (then the table's
    /// size/quality variants do not apply).
    pub own_image_price: bool,
}

const IMAGE_PRICE_KEYS: &[&str] = &["input_cost_per_image", "output_cost_per_image", "input_cost_per_pixel"];

impl Prices {
    /// `table` overridden by the token prices parsed into `dep`, then by
    /// `overrides` in order (later ones win).
    pub fn resolve(table: Option<&Pricing>, dep: &Deployment, overrides: &[&Map<String, Value>]) -> Prices {
        let positive = |v: f64| (v > 0.0).then_some(v);
        let mut p = match table {
            Some(t) => Prices {
                mode: t.mode.clone(),
                input_cost_per_token: positive(t.input_cost_per_token),
                output_cost_per_token: positive(t.output_cost_per_token),
                input_cost_per_image: t.input_cost_per_image,
                output_cost_per_image: t.output_cost_per_image,
                input_cost_per_pixel: t.input_cost_per_pixel,
                input_cost_per_image_token: t.input_cost_per_image_token,
                output_cost_per_image_token: t.output_cost_per_image_token,
                input_cost_per_second: t.input_cost_per_second,
                output_cost_per_second: t.output_cost_per_second,
                input_cost_per_character: t.input_cost_per_character,
                input_cost_per_audio_token: t.input_cost_per_audio_token,
                max_output_tokens: t.max_output_tokens,
                own_image_price: false,
            },
            None => Prices::default(),
        };
        if let Some(c) = dep.input_cost_per_token {
            p.input_cost_per_token = Some(c);
        }
        if let Some(c) = dep.output_cost_per_token {
            p.output_cost_per_token = Some(c);
        }
        for o in overrides {
            let f = |k: &str| o.get(k).and_then(|v| v.as_f64().or_else(|| v.as_str()?.parse().ok()));
            if let Some(m) = o.get("mode").and_then(Value::as_str) {
                p.mode = Some(m.to_owned());
            }
            if IMAGE_PRICE_KEYS.iter().any(|k| f(k).is_some()) {
                p.own_image_price = true;
                p.input_cost_per_image = None;
                p.output_cost_per_image = None;
                p.input_cost_per_pixel = None;
            }
            let fields: [(&str, &mut Option<f64>); 11] = [
                ("input_cost_per_token", &mut p.input_cost_per_token),
                ("output_cost_per_token", &mut p.output_cost_per_token),
                ("input_cost_per_image", &mut p.input_cost_per_image),
                ("output_cost_per_image", &mut p.output_cost_per_image),
                ("input_cost_per_pixel", &mut p.input_cost_per_pixel),
                ("input_cost_per_image_token", &mut p.input_cost_per_image_token),
                ("output_cost_per_image_token", &mut p.output_cost_per_image_token),
                ("input_cost_per_second", &mut p.input_cost_per_second),
                ("output_cost_per_second", &mut p.output_cost_per_second),
                ("input_cost_per_character", &mut p.input_cost_per_character),
                ("input_cost_per_audio_token", &mut p.input_cost_per_audio_token),
            ];
            for (k, slot) in fields {
                if let Some(v) = f(k) {
                    *slot = Some(v);
                }
            }
        }
        if p.mode.is_none() {
            p.mode = p.inferred_mode().map(str::to_owned);
        }
        p
    }

    /// The mode the deployment's own media prices imply, for models the
    /// table does not know.
    fn inferred_mode(&self) -> Option<&'static str> {
        if self.input_cost_per_second.is_some() || self.output_cost_per_second.is_some() {
            Some("audio_transcription")
        } else if self.input_cost_per_character.is_some() {
            Some("audio_speech")
        } else if self.own_image_price || self.output_cost_per_image_token.is_some() {
            Some("image_generation")
        } else {
            None
        }
    }
}

/// Which media endpoint a request is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endpoint {
    ImageGeneration,
    ImageEdit,
    Transcription,
    Speech,
}

impl Endpoint {
    pub fn path(self) -> &'static str {
        match self {
            Endpoint::ImageGeneration => "/v1/images/generations",
            Endpoint::ImageEdit => "/v1/images/edits",
            Endpoint::Transcription => "/v1/audio/transcriptions",
            Endpoint::Speech => "/v1/audio/speech",
        }
    }
}

/// How a media deployment counts and prices its calls.
#[derive(Debug, Clone, PartialEq)]
pub enum MediaPricing {
    Images(ImagePricing),
    Transcription(TranscriptionPricing),
    Speech(SpeechPricing),
}

impl MediaPricing {
    /// The pricing for a deployment of a media mode, or `None` for chat,
    /// embeddings and unknown modes. `model` is the name to look image
    /// variants up by (`model_info.base_model` for Azure).
    pub fn new(prices: &Prices, dep: &Deployment, model: &str) -> Option<MediaPricing> {
        match prices.mode.as_deref()? {
            "image_generation" | "image_edit" => Some(MediaPricing::Images(ImagePricing::new(prices, dep, model))),
            "audio_transcription" => Some(MediaPricing::Transcription(TranscriptionPricing::new(prices))),
            "audio_speech" => Some(MediaPricing::Speech(SpeechPricing::new(prices))),
            _ => None,
        }
    }

    /// `(input_cost, output_cost)` for the kernel: nano-dollars per prompt
    /// and completion unit.
    pub fn unit_prices(&self) -> (u64, u64) {
        match self {
            MediaPricing::Images(p) => (p.prompt_nano, p.unit_nano),
            MediaPricing::Transcription(p) => (p.second_nano, p.out_nano),
            MediaPricing::Speech(p) => (p.nano(), 0),
        }
    }

    /// Whether this deployment serves `endpoint`.
    pub fn serves(&self, endpoint: Endpoint) -> bool {
        matches!(
            (self, endpoint),
            (MediaPricing::Images(_), Endpoint::ImageGeneration | Endpoint::ImageEdit)
                | (MediaPricing::Transcription(_), Endpoint::Transcription)
                | (MediaPricing::Speech(_), Endpoint::Speech)
        )
    }
}

// ---------------------------------------------------------------------------
// Images

/// What an image request asks for, as far as pricing goes.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ImageAsk {
    pub n: u64,
    pub size: Option<String>,
    pub quality: Option<String>,
    pub prompt: String,
    /// Images uploaded to an edit.
    pub input_images: u64,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Scheme {
    /// Completion units are thousandths of the top image price.
    PerImage,
    /// Completion units are output image tokens; text output is converted
    /// at this price (nano-dollars per token).
    Tokens { text_out_nano: Option<u64> },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImagePricing {
    /// Nano-dollars per prompt unit (a text token).
    pub prompt_nano: u64,
    /// Nano-dollars per completion unit.
    pub unit_nano: u64,
    image_in_nano: u64,
    scheme: Scheme,
    variants: Vec<ImageVariant>,
    flat: Option<f64>,
    per_pixel: Option<f64>,
    default_size: Option<(u64, u64)>,
    default_quality: Option<&'static str>,
    gemini: bool,
}

/// `"1024x1792"` -> `(1024, 1792)`; `auto` and missing sizes are unknown.
fn parse_size(s: Option<&str>) -> Option<(u64, u64)> {
    let (w, h) = s?.split_once(['x', 'X'])?;
    Some((w.trim().parse().ok()?, h.trim().parse().ok()?))
}

fn norm_quality(q: Option<&str>) -> Option<String> {
    let q = q?.trim().to_ascii_lowercase();
    (!q.is_empty() && q != "auto").then_some(q)
}

/// The largest size assumed when neither the request nor the table gives one.
const DEFAULT_SIZE: (u64, u64) = (1536, 1024);

impl ImagePricing {
    pub fn new(prices: &Prices, dep: &Deployment, model: &str) -> ImagePricing {
        let variants = if prices.own_image_price { Vec::new() } else { pricing::image_variants(dep.provider.name(), model) };
        let flat = prices.input_cost_per_image.or(prices.output_cost_per_image);
        let per_pixel = prices.input_cost_per_pixel;
        let base = model.rsplit('/').next().unwrap_or(model);
        let (default_size, default_quality) = if base.contains("dall-e-3") {
            (Some((1024, 1024)), Some("standard"))
        } else if base.contains("dall-e-2") {
            (Some((1024, 1024)), None)
        } else {
            (None, None)
        };
        let text_nano = prices.input_cost_per_token.map_or(0, nano);
        let image_in_nano = prices.input_cost_per_image_token.map_or(0, nano);
        let prompt_nano = if text_nano > 0 { text_nano } else { image_in_nano };
        let mut p = ImagePricing {
            prompt_nano,
            unit_nano: 0,
            image_in_nano,
            scheme: Scheme::PerImage,
            variants,
            flat,
            per_pixel,
            default_size,
            default_quality,
            gemini: dep.provider == Provider::Gemini,
        };
        match prices.output_cost_per_image_token.filter(|c| *c > 0.0) {
            Some(out) => {
                p.unit_nano = nano(out);
                p.scheme = Scheme::Tokens { text_out_nano: prices.output_cost_per_token.map(nano).filter(|n| *n > 0) };
            }
            None => {
                let top = p.top_usd();
                p.unit_nano = if top > 0.0 { nano(top / UNITS_PER_TOP_IMAGE as f64) } else { 0 };
            }
        }
        p
    }

    /// The most expensive image this deployment's prices describe.
    fn top_usd(&self) -> f64 {
        let largest = self.variants.iter().map(|v| (v.width, v.height)).max_by_key(|(w, h)| w * h).unwrap_or(DEFAULT_SIZE);
        let variant = self.variants.iter().map(|v| v.usd_per_image).fold(0.0, f64::max);
        let pixel = self.per_pixel.map_or(0.0, |p| p * (largest.0 * largest.1) as f64);
        variant.max(self.flat.unwrap_or(0.0)).max(pixel)
    }

    /// The most an image of `size` and `quality` can cost (unknown ones
    /// range over every variant), in nano-dollars.
    fn bound_nano(&self, size: Option<(u64, u64)>, quality: Option<&str>) -> Option<u64> {
        let size = size.or(self.default_size);
        let quality = quality.or(self.default_quality);
        let fits_size = |v: &&ImageVariant| size.is_none_or(|s| (v.width, v.height) == s);
        let fits_quality = |v: &&ImageVariant| match (quality, &v.quality) {
            (Some(q), Some(vq)) => q == vq,
            _ => true,
        };
        let mut candidates: Vec<&ImageVariant> = self.variants.iter().filter(fits_size).filter(fits_quality).collect();
        if candidates.is_empty() {
            candidates = self.variants.iter().filter(fits_size).collect();
        }
        if candidates.is_empty() {
            candidates = self.variants.iter().collect();
        }
        let largest = || self.variants.iter().map(|v| (v.width, v.height)).max_by_key(|(w, h)| w * h).unwrap_or(DEFAULT_SIZE);
        let (w, h) = size.unwrap_or_else(largest);
        let prices = candidates.iter().map(|v| v.usd_per_image).chain(self.flat).chain(self.per_pixel.map(|p| p * (w * h) as f64));
        let max = prices.fold(None, |m: Option<f64>, p| Some(m.map_or(p, |m| m.max(p))))?;
        Some(nano(max))
    }

    /// What an image of `size` and `quality` costs: the exact variant, else
    /// the most it can cost.
    fn actual_nano(&self, size: Option<(u64, u64)>, quality: Option<&str>) -> Option<u64> {
        let size = size.or(self.default_size);
        let quality = quality.or(self.default_quality);
        let exact = self.variants.iter().find(|v| Some((v.width, v.height)) == size && v.quality.as_deref() == quality);
        match exact {
            Some(v) => Some(nano(v.usd_per_image)),
            None => self.bound_nano(size, quality),
        }
    }

    /// Completion units of one image costing `price` nano-dollars.
    fn units_of(&self, price: u64) -> u64 {
        if self.unit_nano == 0 { UNITS_PER_TOP_IMAGE } else { price.div_ceil(self.unit_nano) }
    }

    /// The most output image tokens one image of `size` and `quality` takes.
    fn image_tokens_bound(&self, size: Option<(u64, u64)>, quality: Option<&str>) -> u64 {
        let size = size.or(self.default_size);
        let from_price = self.bound_nano(size, quality).map_or(0, |p| self.units_of(p));
        let formula = if self.gemini {
            if size.is_some_and(|(w, h)| w.max(h) > 2048) { 2_600 } else { 1_400 }
        } else {
            let (w, h) = size.unwrap_or(DEFAULT_SIZE);
            let per_megapixel = match quality {
                Some("low") => 272,
                Some("medium") => 1_056,
                _ => 4_160,
            };
            (w.saturating_mul(h).saturating_mul(per_megapixel)).div_ceil(1024 * 1024)
        };
        from_price.max(formula)
    }

    /// Units per image, reserved.
    fn per_image_bound(&self, size: Option<(u64, u64)>, quality: Option<&str>) -> u64 {
        match self.scheme {
            Scheme::PerImage => self.bound_nano(size, quality).map_or(UNITS_PER_TOP_IMAGE, |p| self.units_of(p)),
            Scheme::Tokens { .. } => self.image_tokens_bound(size, quality),
        }
    }

    /// The reservation: an upper bound of what [`ImagePricing::settle`]
    /// charges for the images asked for.
    pub fn reserve(&self, ask: &ImageAsk) -> Units {
        let size = parse_size(ask.size.as_deref());
        let quality = norm_quality(ask.quality.as_deref());
        let image_tokens = ask.input_images.saturating_mul(INPUT_IMAGE_TOKENS);
        let prompt = (ask.prompt.len() as u64).saturating_add(convert(image_tokens, self.image_in_nano, self.prompt_nano));
        let mut completion = ask.n.max(1).saturating_mul(self.per_image_bound(size, quality.as_deref()));
        if let Scheme::Tokens { text_out_nano: Some(t) } = self.scheme {
            completion = completion.saturating_add(convert(IMAGE_TEXT_ALLOWANCE, t, self.unit_nano));
        }
        Units { prompt, completion }
    }

    /// What a response used: its token usage when the model is token-priced
    /// and reports it, else the images returned at their variant's price.
    pub fn settle(&self, ask: &ImageAsk, resp: &ImageResponse) -> Units {
        if let (Scheme::Tokens { text_out_nano }, Some(u)) = (self.scheme, &resp.usage) {
            let (text_in, image_in) = match &u.input_tokens_details {
                Some(d) if d.text_tokens + d.image_tokens > 0 => (d.text_tokens, d.image_tokens),
                _ => (u.input_tokens, 0),
            };
            let (text_out, image_out) = match &u.output_tokens_details {
                Some(d) if d.text_tokens + d.image_tokens > 0 => (d.text_tokens, d.image_tokens),
                _ => (0, u.output_tokens),
            };
            let text_out_units = convert(text_out, text_out_nano.unwrap_or(self.unit_nano), self.unit_nano);
            return Units {
                prompt: text_in.saturating_add(convert(image_in, self.image_in_nano, self.prompt_nano)),
                completion: image_out.saturating_add(text_out_units),
            };
        }
        let size = parse_size(resp.reported("size")).or(parse_size(ask.size.as_deref()));
        let quality = norm_quality(resp.reported("quality")).or(norm_quality(ask.quality.as_deref()));
        let per_image = match self.scheme {
            Scheme::PerImage => self.actual_nano(size, quality.as_deref()).map_or(UNITS_PER_TOP_IMAGE, |p| self.units_of(p)),
            Scheme::Tokens { .. } => match self.actual_nano(size, quality.as_deref()) {
                Some(p) => self.units_of(p),
                None => self.image_tokens_bound(size, quality.as_deref()),
            },
        };
        Units { prompt: estimate_text(&ask.prompt), completion: (resp.data.len() as u64).saturating_mul(per_image) }
    }
}

// ---------------------------------------------------------------------------
// Transcription

/// What a transcription request uploads, as far as pricing goes.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct AudioAsk {
    /// An upper bound of the audio's duration, in seconds.
    pub bound_seconds: f64,
    /// The container's duration, if it declares one.
    pub estimate: Option<f64>,
    /// The `prompt` field.
    pub prompt: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TranscriptionPricing {
    /// Nano-dollars per second of audio (the prompt unit).
    pub second_nano: u64,
    /// Nano-dollars per output text token (the completion unit).
    pub out_nano: u64,
    audio_nano: Option<u64>,
    text_nano: Option<u64>,
    max_output_tokens: Option<u64>,
}

impl TranscriptionPricing {
    pub fn new(prices: &Prices) -> TranscriptionPricing {
        let per_second = prices
            .output_cost_per_second
            .filter(|c| *c > 0.0)
            .or(prices.input_cost_per_second)
            .or(prices.input_cost_per_audio_token.map(|t| t * AUDIO_TOKENS_PER_SECOND));
        TranscriptionPricing {
            second_nano: per_second.map_or(0, nano),
            out_nano: prices.output_cost_per_token.map_or(0, nano),
            audio_nano: prices.input_cost_per_audio_token.map(nano),
            text_nano: prices.input_cost_per_token.map(nano),
            max_output_tokens: prices.max_output_tokens,
        }
    }

    fn token_priced(&self) -> bool {
        self.audio_nano.is_some() || self.out_nano > 0
    }

    pub fn reserve(&self, ask: &AudioAsk) -> Units {
        let mut prompt = ceil_secs(ask.bound_seconds);
        let mut completion = 0;
        if self.token_priced() {
            prompt = prompt.saturating_add(convert(ask.prompt.len() as u64, self.text_nano.unwrap_or(0), self.second_nano));
            let tokens = ceil_secs(ask.bound_seconds * TRANSCRIPT_TOKENS_PER_SECOND).saturating_add(64);
            completion = self.max_output_tokens.map_or(tokens, |m| tokens.min(m));
        }
        Units { prompt, completion }
    }

    pub fn settle(&self, ask: &AudioAsk, resp: &TranscriptionResponse) -> Units {
        if self.token_priced()
            && let Some(t) = resp.tokens()
        {
            let audio = self.audio_nano.or(self.text_nano).unwrap_or(0);
            let input_nano = (u128::from(t.audio_tokens) * u128::from(audio))
                .saturating_add(u128::from(t.text_tokens) * u128::from(self.text_nano.unwrap_or(audio)));
            let prompt = if self.second_nano == 0 {
                0
            } else {
                u64::try_from(input_nano.div_ceil(u128::from(self.second_nano))).unwrap_or(u64::MAX)
            };
            return Units { prompt, completion: t.output_tokens };
        }
        let seconds = resp.duration().or(ask.estimate).or_else(|| resp.subtitle_end()).unwrap_or(ask.bound_seconds);
        Units { prompt: ceil_secs(seconds), completion: 0 }
    }
}

// ---------------------------------------------------------------------------
// Speech

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SpeechPricing {
    /// Nano-dollars per input character.
    PerCharacter(u64),
    /// Nano-dollars per (estimated) input token.
    PerToken(u64),
}

impl SpeechPricing {
    pub fn new(prices: &Prices) -> SpeechPricing {
        match (prices.input_cost_per_character, prices.input_cost_per_token) {
            (Some(c), _) => SpeechPricing::PerCharacter(nano(c)),
            (None, Some(t)) => SpeechPricing::PerToken(nano(t)),
            (None, None) => SpeechPricing::PerCharacter(0),
        }
    }

    fn nano(&self) -> u64 {
        match *self {
            SpeechPricing::PerCharacter(n) | SpeechPricing::PerToken(n) => n,
        }
    }

    /// The units of synthesizing `input`: known before the call, so the
    /// reservation and the settlement are the same.
    pub fn units(&self, input: &str) -> Units {
        let prompt = match self {
            SpeechPricing::PerCharacter(_) => input.chars().count() as u64,
            SpeechPricing::PerToken(_) => estimate_text(input),
        };
        Units { prompt, completion: 0 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gateway_providers::media::{ImageData, ImageTokenDetails, ImageUsage};
    use serde_json::json;

    fn dep(model: &str) -> Deployment {
        Deployment::from_litellm_params_with_env(&json!({"model": model, "api_key": "k", "api_base": "http://x"}), |_| None).unwrap()
    }

    fn media(model: &str, overrides: Value) -> MediaPricing {
        let d = dep(model);
        let table = d.pricing();
        let o = overrides.as_object().cloned().unwrap_or_default();
        let prices = Prices::resolve(table.as_ref(), &d, &[&o]);
        MediaPricing::new(&prices, &d, &d.model).expect("a media deployment")
    }

    fn images(model: &str, overrides: Value) -> ImagePricing {
        match media(model, overrides) {
            MediaPricing::Images(p) => p,
            other => panic!("{other:?}"),
        }
    }

    fn ask(n: u64, size: Option<&str>, quality: Option<&str>) -> ImageAsk {
        ImageAsk { n, size: size.map(Into::into), quality: quality.map(Into::into), prompt: "a cat".into(), input_images: 0 }
    }

    fn response(n: usize) -> ImageResponse {
        ImageResponse { created: 1, data: vec![ImageData { url: Some("u".into()), ..ImageData::default() }; n], ..ImageResponse::default() }
    }

    fn pair(u: Units) -> (u64, u64) {
        (u.prompt, u.completion)
    }

    /// Nano-dollars the kernel charges for `units` at `p`'s prices.
    fn cost(p: &MediaPricing, u: Units) -> u64 {
        let (i, o) = p.unit_prices();
        u.prompt * i + u.completion * o
    }

    #[test]
    fn dall_e_3_per_image() {
        let p = images("openai/dall-e-3", json!({}));
        // The top variant is hd 1024x1792 at $0.12: units are $0.00012.
        assert_eq!((p.prompt_nano, p.unit_nano), (0, 120_000));
        let m = MediaPricing::Images(p.clone());
        // Standard 1024x1024 is the default: $0.04 = 334 units (rounded up).
        let a = ask(1, None, None);
        let r = p.reserve(&a);
        assert_eq!(r.completion, 334);
        let s = p.settle(&a, &response(1));
        assert_eq!(s.completion, 334);
        let charged = cost(&m, s);
        assert!((40_000_000..40_000_000 + 120_000).contains(&charged), "{charged}");
        // hd wide reserves and charges the top price exactly.
        let a = ask(2, Some("1792x1024"), Some("hd"));
        assert_eq!(p.reserve(&a).completion, 2000);
        assert_eq!(cost(&m, p.settle(&a, &response(2))), 240_000_000);
        // DALL-E 3's default quality is standard; fewer images settle less.
        let a = ask(2, Some("1024x1024"), Some("auto"));
        assert_eq!(p.reserve(&a).completion, 2 * 334);
        assert_eq!(p.settle(&a, &response(1)).completion, 334);
        // An unknown size reserves the dearest of the quality's sizes.
        assert_eq!(p.reserve(&ask(1, Some("999x999"), Some("hd"))).completion, 1000);
    }

    #[test]
    fn settlement_never_exceeds_the_reservation() {
        for model in ["openai/dall-e-3", "openai/dall-e-2", "azure/dall-e-3", "openai/gpt-image-1", "gemini/imagen-3.0-generate-001"] {
            let p = images(model, json!({}));
            for size in [None, Some("1024x1024"), Some("1024x1792"), Some("1536x1024"), Some("256x256"), Some("auto")] {
                for quality in [None, Some("standard"), Some("hd"), Some("low"), Some("medium"), Some("high"), Some("auto")] {
                    for n in 1..=3 {
                        let a = ask(n, size, quality);
                        let r = p.reserve(&a);
                        let s = p.settle(&a, &response(n as usize));
                        assert!(s.prompt <= r.prompt && s.completion <= r.completion, "{model} {size:?} {quality:?}: {s:?} > {r:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn azure_dall_e_per_pixel() {
        let p = images("azure/dall-e-3", json!({}));
        let m = MediaPricing::Images(p.clone());
        let a = ask(1, Some("1024x1024"), Some("standard"));
        let charged = cost(&m, p.settle(&a, &response(1)));
        let exact = 4.19617e-08 * 1024.0 * 1024.0 * 1e9;
        assert!(charged as f64 >= exact && (charged as f64) < exact + p.unit_nano as f64 + 1.0);
    }

    #[test]
    fn gpt_image_tokens() {
        let p = images("openai/gpt-image-1", json!({}));
        assert_eq!((p.prompt_nano, p.unit_nano), (5_000, 40_000));
        // High 1536x1024: the flat $0.25 is 6250 tokens, above OpenAI's 6240.
        let a = ask(1, Some("1536x1024"), Some("high"));
        assert_eq!(pair(p.reserve(&a)), (5, 6250));
        // Unknown size and quality reserve the largest, highest image.
        assert_eq!(p.reserve(&ask(1, None, None)).completion, 6250);
        assert_eq!(p.reserve(&ask(1, Some("1024x1024"), Some("low"))).completion, 275);
        // Usage is charged as reported, image input at twice the text price.
        let mut r = response(1);
        r.usage = Some(ImageUsage {
            input_tokens: 110,
            output_tokens: 4160,
            input_tokens_details: Some(ImageTokenDetails { text_tokens: 10, image_tokens: 100, ..Default::default() }),
            ..ImageUsage::default()
        });
        let s = p.settle(&a, &r);
        assert_eq!(pair(s), (210, 4160));
        assert_eq!(cost(&MediaPricing::Images(p.clone()), s), 10 * 5_000 + 100 * 10_000 + 4160 * 40_000);
        // Without usage, the variant price (high 1024x1024 = $0.167 = 4175 tokens).
        let a = ask(1, Some("1024x1024"), Some("high"));
        assert_eq!(p.settle(&a, &response(1)).completion, 4175);
        // An edit reserves input image tokens, converted to text-token units.
        let mut e = ask(1, Some("1024x1024"), Some("high"));
        e.input_images = 2;
        assert_eq!(p.reserve(&e).prompt, 5 + 2 * 8_000 * 2);
    }

    #[test]
    fn gemini_image_models() {
        let p = images("gemini/gemini-2.5-flash-image", json!({}));
        assert_eq!(p.unit_nano, 30_000);
        let a = ask(1, None, None);
        let r = p.reserve(&a);
        // 1,400 image tokens and 2,048 text tokens at 2.5e-6 / 3e-5.
        assert_eq!(r.completion, 1_400 + (2_048u64 * 2_500).div_ceil(30_000));
        let mut resp = response(1);
        resp.usage = Some(ImageUsage {
            input_tokens: 7,
            output_tokens: 1320,
            output_tokens_details: Some(ImageTokenDetails { text_tokens: 30, image_tokens: 1290, ..Default::default() }),
            ..ImageUsage::default()
        });
        let s = p.settle(&a, &resp);
        assert_eq!(pair(s), (7, 1290 + 3));
        assert!(s.completion <= r.completion);
        // Imagen is per image.
        let i = images("gemini/imagen-3.0-generate-001", json!({}));
        assert_eq!(i.unit_nano, 40_000);
        let a = ask(4, None, None);
        assert_eq!(i.reserve(&a).completion, 4000);
        assert_eq!(cost(&MediaPricing::Images(i.clone()), i.settle(&a, &response(3))), 3 * 40_000_000);
    }

    #[test]
    fn image_price_overrides() {
        // A deployment's own flat price replaces the table's variants.
        let p = images("openai/dall-e-3", json!({"output_cost_per_image": 0.05}));
        assert_eq!(p.unit_nano, 50_000);
        assert_eq!(p.reserve(&ask(1, Some("1792x1024"), Some("hd"))).completion, 1000);
        // An unknown model with an image price is an image model.
        let p = images("openai/my-image-model", json!({"output_cost_per_image": "0.01"}));
        assert_eq!(p.unit_nano, 10_000);
        assert!(matches!(media("openai/whatever", json!({"mode": "image_generation"})), MediaPricing::Images(_)));
    }

    #[test]
    fn whisper_per_second() {
        let m = media("openai/whisper-1", json!({}));
        let MediaPricing::Transcription(p) = &m else { panic!() };
        assert_eq!(m.unit_prices(), (100_000, 0));
        let a = AudioAsk { bound_seconds: 30.2, estimate: Some(30.2), prompt: "names".into() };
        assert_eq!(pair(p.reserve(&a)), (31, 0));
        // The provider's duration wins, then the container's, then subtitles.
        let reported = TranscriptionResponse::Json(json!({"text": "x", "duration": 29.5}));
        assert_eq!(p.settle(&a, &reported).prompt, 30);
        let plain = TranscriptionResponse::Json(json!({"text": "x"}));
        assert_eq!(p.settle(&a, &plain).prompt, 31);
        let srt = TranscriptionResponse::Text { content_type: "x".into(), body: "1\n00:00:00,000 --> 00:00:12,000\nhi\n".into() };
        let unknown = AudioAsk { bound_seconds: 600.0, estimate: None, prompt: String::new() };
        assert_eq!(p.settle(&unknown, &srt).prompt, 12);
        assert_eq!(p.settle(&unknown, &plain).prompt, 600);
        let groq = media("groq/whisper-large-v3-turbo", json!({}));
        assert_eq!(groq.unit_prices(), (11_110, 0));
    }

    #[test]
    fn gpt_4o_transcribe_tokens() {
        let m = media("openai/gpt-4o-transcribe", json!({}));
        let MediaPricing::Transcription(p) = &m else { panic!() };
        assert_eq!(m.unit_prices(), (100_000, 10_000));
        let a = AudioAsk { bound_seconds: 60.0, estimate: Some(60.0), prompt: String::new() };
        let r = p.reserve(&a);
        assert_eq!(pair(r), (60, 60 * 16 + 64));
        let resp = TranscriptionResponse::Json(json!({"text": "x", "usage": {"type": "tokens", "input_tokens": 620, "output_tokens": 150,
            "input_token_details": {"audio_tokens": 600, "text_tokens": 20}}}));
        let s = p.settle(&a, &resp);
        // 620 tokens at $2.5/M = 1,550,000 nano = 15.5 seconds -> 16.
        assert_eq!(pair(s), (16, 150));
        assert!(s.prompt <= r.prompt && s.completion <= r.completion);
        // Durations are used when that is what is reported.
        let d = TranscriptionResponse::Json(json!({"text": "x", "usage": {"type": "duration", "seconds": 42}}));
        assert_eq!(pair(p.settle(&a, &d)), (42, 0));
        // A long upload is capped at the model's output limit.
        let long = AudioAsk { bound_seconds: 3600.0, ..a };
        assert_eq!(p.reserve(&long).completion, 2000);
    }

    #[test]
    fn speech_per_character_and_token() {
        let m = media("openai/tts-1", json!({}));
        let MediaPricing::Speech(p) = &m else { panic!() };
        assert_eq!(m.unit_prices(), (15_000, 0));
        assert_eq!(pair(p.units("héllo world")), (11, 0));
        let hd = media("azure/tts-1-hd", json!({}));
        assert_eq!(hd.unit_prices(), (33_000, 0));
        let mini = media("openai/gpt-4o-mini-tts", json!({}));
        let MediaPricing::Speech(p) = &mini else { panic!() };
        assert_eq!(mini.unit_prices(), (600, 0));
        assert_eq!(pair(p.units("12345678")), (2, 0));
    }

    #[test]
    fn chat_models_are_not_media() {
        let d = dep("openai/gpt-4o");
        let prices = Prices::resolve(d.pricing().as_ref(), &d, &[]);
        assert_eq!(prices.mode.as_deref(), Some("chat"));
        assert!(MediaPricing::new(&prices, &d, &d.model).is_none());
        // An unknown model with a per-second price is a transcription model.
        let d = dep("openai_like/my-asr");
        let o = json!({"input_cost_per_second": 0.0002}).as_object().cloned().unwrap();
        let prices = Prices::resolve(None, &d, &[&o]);
        let m = MediaPricing::new(&prices, &d, &d.model).unwrap();
        assert!(m.serves(Endpoint::Transcription) && !m.serves(Endpoint::Speech));
        assert_eq!(m.unit_prices(), (200_000, 0));
    }
}
