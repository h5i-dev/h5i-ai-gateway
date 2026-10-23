//! Model prices and context windows from LiteLLM's
//! `model_prices_and_context_window.json`, vendored in `data/` (MIT, see
//! `data/README.md`) and parsed once on first use.

use std::collections::HashMap;
use std::sync::LazyLock;

use serde_json::Value;

use crate::deployment::PROVIDERS;

static RAW: &str = include_str!("../data/model_prices_and_context_window.json");

static TABLE: LazyLock<HashMap<String, Pricing>> = LazyLock::new(|| parse(RAW));

/// Price and limits of one model. Costs are USD per token; a missing cost in
/// the table is reported as `0.0`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Pricing {
    pub input_cost_per_token: f64,
    pub output_cost_per_token: f64,
    /// USD per prompt token read from the provider's cache, if priced.
    pub cache_read_input_token_cost: Option<f64>,
    /// USD per prompt token written to the provider's cache, if priced.
    pub cache_creation_input_token_cost: Option<f64>,
    pub max_input_tokens: Option<u64>,
    /// `max_output_tokens`, falling back to the legacy `max_tokens`.
    pub max_output_tokens: Option<u64>,
    pub litellm_provider: Option<String>,
    /// `chat`, `embedding`, `completion`, `image_generation`, ...
    pub mode: Option<String>,
    /// USD per image (LiteLLM's flat per-image price; size/quality variants
    /// carry it under `input_cost_per_image`).
    pub input_cost_per_image: Option<f64>,
    pub output_cost_per_image: Option<f64>,
    /// USD per pixel of a generated image (Azure DALL-E variants).
    pub input_cost_per_pixel: Option<f64>,
    /// USD per image token (gpt-image, Gemini image models).
    pub input_cost_per_image_token: Option<f64>,
    pub output_cost_per_image_token: Option<f64>,
    /// USD per second of audio (transcription).
    pub input_cost_per_second: Option<f64>,
    pub output_cost_per_second: Option<f64>,
    /// USD per input character (text-to-speech).
    pub input_cost_per_character: Option<f64>,
    /// USD per input audio token (token-priced transcription).
    pub input_cost_per_audio_token: Option<f64>,
}

/// One size/quality-specific image price, from a table key such as
/// `hd/1024-x-1792/dall-e-3` or `azure/standard/1024-x-1024/dall-e-3`.
#[derive(Debug, Clone, PartialEq)]
pub struct ImageVariant {
    /// `standard`, `hd`, `low`, `medium`, `high`; `None` for any quality.
    pub quality: Option<String>,
    pub width: u64,
    pub height: u64,
    /// USD per image of this size and quality.
    pub usd_per_image: f64,
}

impl Pricing {
    /// The flat price of one image this entry implies for `width` x
    /// `height` pixels: `input_cost_per_image`, `output_cost_per_image`, or
    /// `input_cost_per_pixel` times the pixels (LiteLLM's
    /// `default_image_cost_calculator` order).
    pub fn usd_per_image(&self, width: u64, height: u64) -> Option<f64> {
        self.input_cost_per_image.or(self.output_cost_per_image).or(self.input_cost_per_pixel.map(|p| p * width.saturating_mul(height) as f64))
    }
}

/// OpenAI's published DALL-E prices, which the vendored table no longer
/// lists (they remain under `azure/`): `(key, USD per image)`.
const LEGACY_IMAGE_PRICES: &[(&str, f64)] = &[
    ("256-x-256/dall-e-2", 0.016),
    ("512-x-512/dall-e-2", 0.018),
    ("1024-x-1024/dall-e-2", 0.02),
    ("standard/1024-x-1024/dall-e-3", 0.04),
    ("standard/1024-x-1792/dall-e-3", 0.08),
    ("standard/1792-x-1024/dall-e-3", 0.08),
    ("hd/1024-x-1024/dall-e-3", 0.08),
    ("hd/1024-x-1792/dall-e-3", 0.12),
    ("hd/1792-x-1024/dall-e-3", 0.12),
];

/// Every size/quality variant of `model`'s image price: the
/// provider-specific keys (`{provider}/{quality}/{W}-x-{H}/{model}`) if
/// there are any, else the generic ones (`{quality}/{W}-x-{H}/{model}`).
/// Empty when the model has none.
pub fn image_variants(provider: &str, model: &str) -> Vec<ImageVariant> {
    let own_prefix = format!("{provider}/");
    let model = model.strip_prefix(&own_prefix).unwrap_or(model);
    let mut specific = Vec::new();
    let mut generic = Vec::new();
    for (key, p) in TABLE.iter() {
        let Some(prefix) = key.strip_suffix(model).and_then(|k| k.strip_suffix('/')) else {
            continue;
        };
        let (own, rest) = match prefix.strip_prefix(&own_prefix) {
            Some(rest) => (true, rest),
            None => (false, prefix),
        };
        let (quality, size) = match rest.rsplit_once('/') {
            Some((q, s)) => (Some(q), s),
            None => (None, rest),
        };
        // A quality is one path segment, and a size is `{W}-x-{H}`.
        if quality.is_some_and(|q| q.contains('/') || q.is_empty()) {
            continue;
        }
        let Some((w, h)) = size.split_once("-x-") else {
            continue;
        };
        let (Ok(width), Ok(height)) = (w.parse::<u64>(), h.parse::<u64>()) else {
            continue;
        };
        let Some(usd_per_image) = p.usd_per_image(width, height) else {
            continue;
        };
        let v = ImageVariant { quality: quality.map(str::to_owned), width, height, usd_per_image };
        if own {
            specific.push(v);
        } else {
            generic.push(v);
        }
    }
    let mut out = if specific.is_empty() { generic } else { specific };
    out.sort_by(|a, b| (&a.quality, a.width, a.height).cmp(&(&b.quality, b.width, b.height)));
    out
}

/// Look a model up: the exact key, then without its provider prefix
/// (`"openai/gpt-4o"` -> `"gpt-4o"`), then a bare name with each known
/// provider prefix (`"gemini-1.5-pro"` -> `"gemini/gemini-1.5-pro"`).
pub fn lookup(model: &str) -> Option<Pricing> {
    let table = &*TABLE;
    if let Some(p) = table.get(model) {
        return Some(p.clone());
    }
    if let Some((_, rest)) = model.split_once('/') {
        return table.get(rest).cloned();
    }
    PROVIDERS.iter().flat_map(|s| s.names).find_map(|name| table.get(&format!("{name}/{model}"))).cloned()
}

/// Look up `"{provider}/{model}"` first (provider-specific prices win), then
/// fall back to [`lookup`].
pub fn lookup_with_provider(provider: &str, model: &str) -> Option<Pricing> {
    TABLE.get(&format!("{provider}/{model}")).cloned().or_else(|| lookup(model))
}

/// Convert USD per token to integer nano-dollars (1e-9 USD) per token,
/// rounding up so spend is never under-counted. Values within floating-point
/// noise of an integer are not bumped (`2.5e-6` -> `2500`, not `2501`).
/// Negative and NaN inputs map to 0; huge values saturate.
pub fn to_nano_per_token(usd_per_token: f64) -> u64 {
    if usd_per_token.is_nan() || usd_per_token <= 0.0 {
        return 0;
    }
    let nano = usd_per_token * 1e9;
    let nearest = nano.round();
    let value = if (nano - nearest).abs() <= nearest.max(1.0) * 1e-9 { nearest } else { nano.ceil() };
    // `as` saturates for out-of-range floats.
    value as u64
}

fn parse(raw: &str) -> HashMap<String, Pricing> {
    let Ok(Value::Object(entries)) = serde_json::from_str::<Value>(raw) else {
        // The file is vendored and checked by tests; an unparseable file
        // degrades to "no pricing known" rather than a panic.
        return HashMap::new();
    };
    let mut table: HashMap<String, Pricing> = entries
        .into_iter()
        .filter(|(k, v)| k != "sample_spec" && v.is_object())
        .map(|(k, v)| {
            let f = |key: &str| v.get(key).and_then(Value::as_f64);
            let u = |key: &str| v.get(key).and_then(Value::as_u64);
            let s = |key: &str| v.get(key).and_then(Value::as_str).map(str::to_owned);
            let pricing = Pricing {
                input_cost_per_token: f("input_cost_per_token").unwrap_or(0.0),
                output_cost_per_token: f("output_cost_per_token").unwrap_or(0.0),
                cache_read_input_token_cost: f("cache_read_input_token_cost"),
                cache_creation_input_token_cost: f("cache_creation_input_token_cost"),
                max_input_tokens: u("max_input_tokens"),
                max_output_tokens: u("max_output_tokens").or_else(|| u("max_tokens")),
                litellm_provider: s("litellm_provider"),
                mode: s("mode"),
                input_cost_per_image: f("input_cost_per_image"),
                output_cost_per_image: f("output_cost_per_image"),
                input_cost_per_pixel: f("input_cost_per_pixel"),
                input_cost_per_image_token: f("input_cost_per_image_token"),
                output_cost_per_image_token: f("output_cost_per_image_token"),
                input_cost_per_second: f("input_cost_per_second"),
                output_cost_per_second: f("output_cost_per_second"),
                input_cost_per_character: f("input_cost_per_character"),
                input_cost_per_audio_token: f("input_cost_per_audio_token"),
            };
            (k, pricing)
        })
        .collect();
    add_legacy_image_prices(&mut table);
    table
}

/// Fill in [`LEGACY_IMAGE_PRICES`] (and bare `dall-e-2`/`dall-e-3` entries,
/// so that their mode is known) where the table lacks them.
fn add_legacy_image_prices(table: &mut HashMap<String, Pricing>) {
    let image = |price: Option<f64>| Pricing {
        litellm_provider: Some("openai".into()),
        mode: Some("image_generation".into()),
        input_cost_per_image: price,
        ..Pricing::default()
    };
    for (key, price) in LEGACY_IMAGE_PRICES {
        table.entry((*key).to_owned()).or_insert_with(|| image(Some(*price)));
    }
    for model in ["dall-e-2", "dall-e-3"] {
        table.entry(model.to_owned()).or_insert_with(|| image(None));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vendored_table_parses() {
        assert!(TABLE.len() > 1000, "only {} entries", TABLE.len());
        assert!(!TABLE.contains_key("sample_spec"));
    }

    #[test]
    fn exact_lookup() {
        let p = lookup("gpt-4o").unwrap();
        assert!(p.input_cost_per_token > 0.0 && p.output_cost_per_token > p.input_cost_per_token);
        assert_eq!(p.litellm_provider.as_deref(), Some("openai"));
        assert_eq!(p.mode.as_deref(), Some("chat"));
        assert!(p.max_input_tokens.unwrap() >= 128_000);
        assert!(p.max_output_tokens.is_some());
        let e = lookup("text-embedding-3-small").unwrap();
        assert_eq!(e.mode.as_deref(), Some("embedding"));
    }

    #[test]
    fn prefix_handling() {
        // With a prefix that is not a key: stripped.
        assert_eq!(lookup("openai/gpt-4o"), lookup("gpt-4o"));
        // Bare name only present with a provider prefix.
        let bare =
            TABLE.keys().find_map(|k| k.strip_prefix("gemini/").filter(|b| !TABLE.contains_key(*b))).expect("some gemini/ key without bare twin");
        assert_eq!(lookup(bare), TABLE.get(&format!("gemini/{bare}")).cloned());
        // Provider-specific entry preferred.
        assert_eq!(lookup_with_provider("azure", "gpt-4o").unwrap().litellm_provider.as_deref(), Some("azure"));
        assert_eq!(lookup_with_provider("groq", "gpt-4o").unwrap().litellm_provider.as_deref(), Some("openai"));
        assert_eq!(lookup("no-such-model-xyz"), None);
    }

    #[test]
    fn anthropic_cache_prices() {
        let p = TABLE.values().find(|p| p.litellm_provider.as_deref() == Some("anthropic") && p.mode.as_deref() == Some("chat")).unwrap();
        assert!(p.cache_read_input_token_cost.is_some());
    }

    #[test]
    fn nano_conversion_rounds_up() {
        assert_eq!(to_nano_per_token(2.5e-6), 2500);
        assert_eq!(to_nano_per_token(1e-5), 10_000);
        assert_eq!(to_nano_per_token(3e-9), 3);
        assert_eq!(to_nano_per_token(1.5e-10), 1);
        assert_eq!(to_nano_per_token(2.0000001e-6), 2001);
        assert_eq!(to_nano_per_token(0.0), 0);
        assert_eq!(to_nano_per_token(-1.0), 0);
        assert_eq!(to_nano_per_token(f64::NAN), 0);
        assert_eq!(to_nano_per_token(f64::INFINITY), u64::MAX);
        for p in TABLE.values() {
            let n = to_nano_per_token(p.input_cost_per_token);
            assert!(n as f64 >= p.input_cost_per_token * 1e9 - 1e-6);
        }
    }

    #[test]
    fn malformed_table_is_empty() {
        assert!(parse("not json").is_empty());
        assert!(parse("[]").is_empty());
    }

    #[test]
    fn media_prices() {
        let w = lookup("whisper-1").unwrap();
        assert_eq!(w.mode.as_deref(), Some("audio_transcription"));
        assert_eq!(w.input_cost_per_second, Some(0.0001));
        let t = lookup("tts-1").unwrap();
        assert_eq!(t.input_cost_per_character, Some(1.5e-5));
        let g = lookup("gpt-image-1").unwrap();
        assert_eq!(g.output_cost_per_image_token, Some(4e-5));
        assert_eq!(g.input_cost_per_image_token, Some(1e-5));
        let i = lookup("gemini/imagen-3.0-generate-001").unwrap();
        assert_eq!(i.usd_per_image(1024, 1024), Some(0.04));
        // Per-pixel prices scale with the size.
        let p = Pricing { input_cost_per_pixel: Some(1e-8), ..Pricing::default() };
        assert_eq!(p.usd_per_image(1000, 1000), Some(0.01));
    }

    #[test]
    fn image_variant_lookup() {
        // DALL-E 3 at OpenAI comes from the legacy prices.
        let v = image_variants("openai", "dall-e-3");
        assert_eq!(v.len(), 6);
        let find = |v: &[ImageVariant], q: &str, w: u64, h: u64| {
            v.iter().find(|v| v.quality.as_deref() == Some(q) && v.width == w && v.height == h).unwrap().usd_per_image
        };
        assert_eq!(find(&v, "hd", 1024, 1792), 0.12);
        assert_eq!(lookup("dall-e-3").unwrap().mode.as_deref(), Some("image_generation"));
        // Azure's are per pixel, under the provider prefix.
        let a = image_variants("azure", "dall-e-3");
        assert_eq!(a.len(), 6);
        assert!((find(&a, "standard", 1024, 1024) - 0.044).abs() < 1e-3);
        // gpt-image-1 has low/medium/high variants.
        let g = image_variants("openai", "gpt-image-1");
        assert_eq!(find(&g, "high", 1536, 1024), 0.25);
        assert!(image_variants("openai", "no-such-image-model").is_empty());
        // A provider prefix on the model is ignored; no quality is `None`.
        let d2 = image_variants("openai", "openai/dall-e-2");
        assert_eq!(d2.len(), 3);
        assert!(d2.iter().all(|v| v.quality.is_none()));
    }
}
