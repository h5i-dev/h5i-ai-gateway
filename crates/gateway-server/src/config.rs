//! LiteLLM's `config.yaml`: `model_list`, `router_settings`,
//! `litellm_settings`, `general_settings` and `environment_variables`.
//!
//! The parts the gateway implements are typed; the rest is accepted and
//! ignored (with a warning) so existing LiteLLM configs load.

use serde::Deserialize;
use serde_json::Value;
use std::collections::{BTreeMap, HashMap};
use std::path::Path;

#[derive(Debug, Default, Deserialize)]
pub struct Config {
    #[serde(default)]
    pub model_list: Vec<ModelEntry>,
    #[serde(default)]
    pub router_settings: RouterSettings,
    #[serde(default)]
    pub litellm_settings: LitellmSettings,
    #[serde(default)]
    pub general_settings: GeneralSettings,
    /// Set in this process's environment before anything else is read.
    #[serde(default)]
    pub environment_variables: BTreeMap<String, Value>,
    #[serde(flatten)]
    pub other: BTreeMap<String, Value>,
}

/// One deployment: the model group clients name, and how to reach it.
#[derive(Debug, Clone, Deserialize)]
pub struct ModelEntry {
    pub model_name: String,
    pub litellm_params: serde_json::Map<String, Value>,
    #[serde(default)]
    pub model_info: serde_json::Map<String, Value>,
}

#[derive(Debug, Default, Deserialize)]
pub struct RouterSettings {
    pub routing_strategy: Option<String>,
    pub num_retries: Option<u32>,
    pub allowed_fails: Option<u64>,
    /// Seconds.
    pub cooldown_time: Option<f64>,
    /// Seconds per call.
    pub timeout: Option<f64>,
    #[serde(default)]
    pub fallbacks: Vec<HashMap<String, Vec<String>>>,
    #[serde(default)]
    pub model_group_alias: HashMap<String, String>,
    #[serde(flatten)]
    pub other: BTreeMap<String, Value>,
}

#[derive(Debug, Default, Deserialize)]
pub struct LitellmSettings {
    pub num_retries: Option<u32>,
    pub request_timeout: Option<f64>,
    #[serde(default)]
    pub fallbacks: Vec<HashMap<String, Vec<String>>>,
    pub drop_params: Option<bool>,
    #[serde(flatten)]
    pub other: BTreeMap<String, Value>,
}

#[derive(Debug, Default, Deserialize)]
pub struct GeneralSettings {
    pub master_key: Option<String>,
    pub database_url: Option<String>,
    /// Signs virtual keys. Defaults to `LITELLM_SALT_KEY`, then the master key.
    pub key_signing_secret: Option<String>,
    /// The tenant of the master key and of the keys it creates.
    pub org_id: Option<u64>,
    /// Seconds an unsettled reservation is held before it may be expired.
    pub reservation_ttl: Option<u64>,
    /// `log`, or a URL that receives each spend log as a JSON POST.
    pub spend_logs: Option<String>,
    /// `max_tokens` assumed for a request that sets none and whose model has
    /// no known output limit.
    pub default_max_tokens: Option<u64>,
    #[serde(flatten)]
    pub other: BTreeMap<String, Value>,
}

#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("cannot read {path}: {source}")]
    Read { path: String, source: std::io::Error },
    #[error("invalid config: {0}")]
    Parse(#[from] serde_yaml::Error),
    #[error("environment variable {0} is not set")]
    MissingEnv(String),
}

impl Config {
    pub fn load(path: &Path) -> Result<Config, ConfigError> {
        let text = std::fs::read_to_string(path).map_err(|source| ConfigError::Read { path: path.display().to_string(), source })?;
        Self::parse(&text)
    }

    pub fn parse(text: &str) -> Result<Config, ConfigError> {
        let config: Config = serde_yaml::from_str(text)?;
        for key in config.other.keys() {
            tracing::warn!(section = %key, "config section not supported; ignored");
        }
        Ok(config)
    }

    /// Retries per model group: `router_settings`, then `litellm_settings`.
    pub fn num_retries(&self) -> u32 {
        self.router_settings.num_retries.or(self.litellm_settings.num_retries).unwrap_or(2)
    }

    /// Timeout per provider call, in seconds.
    pub fn timeout_secs(&self) -> f64 {
        self.router_settings.timeout.or(self.litellm_settings.request_timeout).unwrap_or(600.0)
    }

    /// Model groups to try, in order, after `model` has no deployment left.
    pub fn fallbacks(&self) -> HashMap<String, Vec<String>> {
        let mut out = HashMap::new();
        for map in self.litellm_settings.fallbacks.iter().chain(&self.router_settings.fallbacks) {
            for (k, v) in map {
                out.insert(k.clone(), v.clone());
            }
        }
        out
    }
}

/// A LiteLLM secret reference: `os.environ/NAME` reads `NAME` from `env`.
pub fn resolve(value: &str, env: &dyn Fn(&str) -> Option<String>) -> Result<String, ConfigError> {
    match value.strip_prefix("os.environ/") {
        Some(name) => env(name).ok_or_else(|| ConfigError::MissingEnv(name.to_string())),
        None => Ok(value.to_string()),
    }
}

pub fn process_env(name: &str) -> Option<String> {
    std::env::var(name).ok()
}

/// A LiteLLM duration (`30s`, `15m`, `12h`, `30d`, `2w`, `1mo`) in seconds.
pub fn parse_duration(s: &str) -> Option<u64> {
    let s = s.trim();
    let split = s.find(|c: char| !c.is_ascii_digit())?;
    let (n, unit) = s.split_at(split);
    let n: u64 = n.parse().ok()?;
    let mult = match unit.trim() {
        "s" => 1,
        "m" => 60,
        "h" => 3_600,
        "d" => 86_400,
        "w" => 7 * 86_400,
        "mo" => 30 * 86_400,
        _ => return None,
    };
    n.checked_mul(mult)
}

/// The kernel id of a deployment: from `model_info.id` if the operator gave
/// one, else from what identifies it in the config. Stable across restarts,
/// so a deployment keeps its health and counters. FNV-1a, with the top bit
/// cleared so it survives a round trip through a signed BIGINT unchanged.
pub fn deployment_id(entry: &ModelEntry) -> u64 {
    let ident = match entry.model_info.get("id") {
        Some(Value::String(s)) => s.clone(),
        Some(v) if !v.is_null() => v.to_string(),
        _ => {
            let field = |k: &str| entry.litellm_params.get(k).map(|v| v.to_string()).unwrap_or_default();
            format!("{}\0{}\0{}\0{}", entry.model_name, field("model"), field("api_base"), field("api_version"))
        }
    };
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in ident.as_bytes() {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    (h >> 1).max(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    const YAML: &str = r#"
model_list:
  - model_name: gpt-4o
    litellm_params:
      model: openai/gpt-4o
      api_key: os.environ/OPENAI_API_KEY
      rpm: 100
  - model_name: claude
    litellm_params:
      model: anthropic/claude-3-5-sonnet-20241022
    model_info:
      id: claude-primary
router_settings:
  num_retries: 3
  allowed_fails: 2
  cooldown_time: 30
  fallbacks: [{"gpt-4o": ["claude"]}]
general_settings:
  master_key: sk-1234
litellm_settings:
  drop_params: true
  success_callback: ["langfuse"]
"#;

    #[test]
    fn parses_litellm_config() {
        let c = Config::parse(YAML).unwrap();
        assert_eq!(c.model_list.len(), 2);
        assert_eq!(c.num_retries(), 3);
        assert_eq!(c.router_settings.allowed_fails, Some(2));
        assert_eq!(c.fallbacks()["gpt-4o"], vec!["claude".to_string()]);
        assert_eq!(c.general_settings.master_key.as_deref(), Some("sk-1234"));
        assert!(c.litellm_settings.other.contains_key("success_callback"));
        let a = deployment_id(&c.model_list[0]);
        assert_eq!(a, deployment_id(&c.model_list[0]));
        assert_ne!(a, deployment_id(&c.model_list[1]));
        assert!(a < 1 << 63);
    }

    #[test]
    fn durations_and_secrets() {
        assert_eq!(parse_duration("30d"), Some(30 * 86_400));
        assert_eq!(parse_duration("15m"), Some(900));
        assert_eq!(parse_duration("1mo"), Some(30 * 86_400));
        assert_eq!(parse_duration("abc"), None);
        let env = |n: &str| (n == "K").then(|| "v".to_string());
        assert_eq!(resolve("os.environ/K", &env).unwrap(), "v");
        assert!(resolve("os.environ/X", &env).is_err());
        assert_eq!(resolve("plain", &env).unwrap(), "plain");
    }
}
