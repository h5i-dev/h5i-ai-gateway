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
    PROVIDERS
        .iter()
        .flat_map(|s| s.names)
        .find_map(|name| table.get(&format!("{name}/{model}")))
        .cloned()
}

/// Look up `"{provider}/{model}"` first (provider-specific prices win), then
/// fall back to [`lookup`].
pub fn lookup_with_provider(provider: &str, model: &str) -> Option<Pricing> {
    TABLE
        .get(&format!("{provider}/{model}"))
        .cloned()
        .or_else(|| lookup(model))
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
    let value = if (nano - nearest).abs() <= nearest.max(1.0) * 1e-9 {
        nearest
    } else {
        nano.ceil()
    };
    // `as` saturates for out-of-range floats.
    value as u64
}

fn parse(raw: &str) -> HashMap<String, Pricing> {
    let Ok(Value::Object(entries)) = serde_json::from_str::<Value>(raw) else {
        // The file is vendored and checked by tests; an unparseable file
        // degrades to "no pricing known" rather than a panic.
        return HashMap::new();
    };
    entries
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
            };
            (k, pricing)
        })
        .collect()
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
        let bare = TABLE
            .keys()
            .find_map(|k| {
                k.strip_prefix("gemini/")
                    .filter(|b| !TABLE.contains_key(*b))
            })
            .expect("some gemini/ key without bare twin");
        assert_eq!(lookup(bare), TABLE.get(&format!("gemini/{bare}")).cloned());
        // Provider-specific entry preferred.
        assert_eq!(
            lookup_with_provider("azure", "gpt-4o")
                .unwrap()
                .litellm_provider
                .as_deref(),
            Some("azure")
        );
        assert_eq!(
            lookup_with_provider("groq", "gpt-4o")
                .unwrap()
                .litellm_provider
                .as_deref(),
            Some("openai")
        );
        assert_eq!(lookup("no-such-model-xyz"), None);
    }

    #[test]
    fn anthropic_cache_prices() {
        let p = TABLE
            .values()
            .find(|p| {
                p.litellm_provider.as_deref() == Some("anthropic")
                    && p.mode.as_deref() == Some("chat")
            })
            .unwrap();
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
}
