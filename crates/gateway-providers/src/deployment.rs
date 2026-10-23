//! Deployments: one upstream model endpoint, parsed from a LiteLLM
//! `litellm_params` object.
//!
//! ```yaml
//! litellm_params:
//!   model: anthropic/claude-3-5-sonnet-20241022   # "<provider>/<upstream model>"
//!   api_key: os.environ/ANTHROPIC_API_KEY        # env indirection
//!   timeout: 30
//!   rpm: 600
//! ```
//!
//! Recognised keys: `model`, `custom_llm_provider`, `api_key`, `api_base`
//! (alias `base_url`), `api_version`, `organization`, `timeout`,
//! `stream_timeout`, `max_retries`, `extra_headers` (alias `headers`),
//! `extra_body`, `input_cost_per_token`, `output_cost_per_token`, `rpm`,
//! `tpm`, `order`, `mock_response`, plus OpenAI sampling defaults
//! ([`REQUEST_DEFAULT_KEYS`]) that are applied when the request omits them.
//! Everything else is kept in [`Deployment::extra`] and not sent upstream.
//!
//! Any string value of the form `os.environ/NAME` is replaced by the value of
//! environment variable `NAME` (an error if unset). When `api_key` /
//! `api_base` / `api_version` are absent, the provider's conventional
//! environment variables are consulted (e.g. `OPENAI_API_KEY`), like LiteLLM.

use std::fmt;
use std::time::Duration;

use serde_json::Value;

use crate::error::ProviderError;
use crate::pricing::{self, Pricing};
use crate::types::JsonObject;

/// Default Azure OpenAI `api-version` when neither the deployment nor
/// `AZURE_API_VERSION` sets one.
pub const DEFAULT_AZURE_API_VERSION: &str = "2025-02-01-preview";

/// OpenAI request parameters that may be set in `litellm_params` as
/// deployment-level defaults.
pub const REQUEST_DEFAULT_KEYS: &[&str] = &[
    "temperature",
    "top_p",
    "max_tokens",
    "max_completion_tokens",
    "stop",
    "seed",
    "presence_penalty",
    "frequency_penalty",
    "reasoning_effort",
    "response_format",
    "parallel_tool_calls",
];

/// Wire protocol an adapter speaks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Protocol {
    OpenAi,
    Azure,
    Anthropic,
    Gemini,
    Mock,
}

/// Upstream provider.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Provider {
    OpenAi,
    Azure,
    Anthropic,
    Gemini,
    Groq,
    DeepSeek,
    Mistral,
    TogetherAi,
    FireworksAi,
    OpenRouter,
    XAi,
    Perplexity,
    DeepInfra,
    Cerebras,
    NvidiaNim,
    SambaNova,
    /// Self-hosted vLLM (`hosted_vllm/`); requires `api_base`.
    HostedVllm,
    /// Any OpenAI-compatible server (`openai_like/`, `custom_openai/`);
    /// requires `api_base`.
    OpenAiLike,
    Ollama,
    OllamaChat,
    LmStudio,
    /// Canned responses without network (`mock/`, `fake/`).
    Mock,
}

/// Static per-provider facts.
pub(crate) struct ProviderSpec {
    pub provider: Provider,
    /// Accepted `model` prefixes; the first is the canonical name.
    pub names: &'static [&'static str],
    pub protocol: Protocol,
    /// Base URL used when the deployment sets none. For OpenAI-compatible
    /// providers this ends right before `/chat/completions`.
    pub default_api_base: Option<&'static str>,
    pub api_key_env: &'static [&'static str],
    pub api_base_env: &'static [&'static str],
    /// Whether an API key is mandatory.
    pub requires_api_key: bool,
    /// Whether the upstream accepts `stream_options.include_usage`.
    pub stream_usage: bool,
    /// Path appended to the configured `api_base` (Ollama serves its
    /// OpenAI-compatible API under `/v1`).
    pub base_suffix: &'static str,
}

const fn openai_compatible(
    provider: Provider,
    names: &'static [&'static str],
    default_api_base: Option<&'static str>,
    api_key_env: &'static [&'static str],
    api_base_env: &'static [&'static str],
    stream_usage: bool,
) -> ProviderSpec {
    ProviderSpec {
        provider,
        names,
        protocol: Protocol::OpenAi,
        default_api_base,
        api_key_env,
        api_base_env,
        requires_api_key: true,
        stream_usage,
        base_suffix: "",
    }
}

const fn self_hosted(spec: ProviderSpec, base_suffix: &'static str) -> ProviderSpec {
    ProviderSpec {
        requires_api_key: false,
        base_suffix,
        ..spec
    }
}

pub(crate) static PROVIDERS: &[ProviderSpec] = &[
    openai_compatible(
        Provider::OpenAi,
        &["openai", "text-completion-openai"],
        Some("https://api.openai.com/v1"),
        &["OPENAI_API_KEY"],
        &["OPENAI_API_BASE", "OPENAI_BASE_URL"],
        true,
    ),
    ProviderSpec {
        protocol: Protocol::Azure,
        ..openai_compatible(
            Provider::Azure,
            &["azure"],
            None,
            &["AZURE_API_KEY"],
            &["AZURE_API_BASE"],
            true,
        )
    },
    ProviderSpec {
        protocol: Protocol::Anthropic,
        ..openai_compatible(
            Provider::Anthropic,
            &["anthropic"],
            Some("https://api.anthropic.com"),
            &["ANTHROPIC_API_KEY"],
            &["ANTHROPIC_API_BASE", "ANTHROPIC_BASE_URL"],
            true,
        )
    },
    ProviderSpec {
        protocol: Protocol::Gemini,
        ..openai_compatible(
            Provider::Gemini,
            &["gemini"],
            Some("https://generativelanguage.googleapis.com"),
            &["GEMINI_API_KEY", "GOOGLE_API_KEY"],
            &["GEMINI_API_BASE"],
            true,
        )
    },
    openai_compatible(
        Provider::Groq,
        &["groq"],
        Some("https://api.groq.com/openai/v1"),
        &["GROQ_API_KEY"],
        &["GROQ_API_BASE"],
        true,
    ),
    openai_compatible(
        Provider::DeepSeek,
        &["deepseek"],
        Some("https://api.deepseek.com/beta"),
        &["DEEPSEEK_API_KEY"],
        &["DEEPSEEK_API_BASE"],
        true,
    ),
    openai_compatible(
        Provider::Mistral,
        &["mistral"],
        Some("https://api.mistral.ai/v1"),
        &["MISTRAL_API_KEY"],
        &["MISTRAL_API_BASE"],
        false,
    ),
    openai_compatible(
        Provider::TogetherAi,
        &["together_ai"],
        Some("https://api.together.xyz/v1"),
        &[
            "TOGETHERAI_API_KEY",
            "TOGETHER_AI_API_KEY",
            "TOGETHER_API_KEY",
        ],
        &["TOGETHER_AI_API_BASE"],
        true,
    ),
    openai_compatible(
        Provider::FireworksAi,
        &["fireworks_ai"],
        Some("https://api.fireworks.ai/inference/v1"),
        &[
            "FIREWORKS_AI_API_KEY",
            "FIREWORKS_API_KEY",
            "FIREWORKSAI_API_KEY",
        ],
        &["FIREWORKS_AI_API_BASE"],
        false,
    ),
    openai_compatible(
        Provider::OpenRouter,
        &["openrouter"],
        Some("https://openrouter.ai/api/v1"),
        &["OPENROUTER_API_KEY", "OR_API_KEY"],
        &["OPENROUTER_API_BASE"],
        true,
    ),
    openai_compatible(
        Provider::XAi,
        &["xai"],
        Some("https://api.x.ai/v1"),
        &["XAI_API_KEY"],
        &["XAI_API_BASE"],
        true,
    ),
    openai_compatible(
        Provider::Perplexity,
        &["perplexity"],
        Some("https://api.perplexity.ai"),
        &["PERPLEXITYAI_API_KEY", "PERPLEXITY_API_KEY"],
        &["PERPLEXITY_API_BASE"],
        false,
    ),
    openai_compatible(
        Provider::DeepInfra,
        &["deepinfra"],
        Some("https://api.deepinfra.com/v1/openai"),
        &["DEEPINFRA_API_KEY"],
        &["DEEPINFRA_API_BASE"],
        true,
    ),
    openai_compatible(
        Provider::Cerebras,
        &["cerebras"],
        Some("https://api.cerebras.ai/v1"),
        &["CEREBRAS_API_KEY"],
        &["CEREBRAS_API_BASE"],
        false,
    ),
    openai_compatible(
        Provider::NvidiaNim,
        &["nvidia_nim"],
        Some("https://integrate.api.nvidia.com/v1"),
        &["NVIDIA_NIM_API_KEY"],
        &["NVIDIA_NIM_API_BASE"],
        false,
    ),
    openai_compatible(
        Provider::SambaNova,
        &["sambanova"],
        Some("https://api.sambanova.ai/v1"),
        &["SAMBANOVA_API_KEY"],
        &["SAMBANOVA_API_BASE"],
        false,
    ),
    self_hosted(
        openai_compatible(
            Provider::HostedVllm,
            &["hosted_vllm", "vllm"],
            None,
            &["HOSTED_VLLM_API_KEY"],
            &["HOSTED_VLLM_API_BASE"],
            true,
        ),
        "",
    ),
    self_hosted(
        openai_compatible(
            Provider::OpenAiLike,
            &["openai_like", "custom_openai"],
            None,
            &[],
            &[],
            true,
        ),
        "",
    ),
    self_hosted(
        openai_compatible(
            Provider::Ollama,
            &["ollama"],
            Some("http://localhost:11434"),
            &["OLLAMA_API_KEY"],
            &["OLLAMA_API_BASE"],
            true,
        ),
        "/v1",
    ),
    self_hosted(
        openai_compatible(
            Provider::OllamaChat,
            &["ollama_chat"],
            Some("http://localhost:11434"),
            &["OLLAMA_API_KEY"],
            &["OLLAMA_API_BASE"],
            true,
        ),
        "/v1",
    ),
    self_hosted(
        openai_compatible(
            Provider::LmStudio,
            &["lm_studio"],
            Some("http://localhost:1234/v1"),
            &["LM_STUDIO_API_KEY"],
            &["LM_STUDIO_API_BASE"],
            false,
        ),
        "",
    ),
    ProviderSpec {
        protocol: Protocol::Mock,
        ..self_hosted(
            openai_compatible(Provider::Mock, &["mock", "fake"], None, &[], &[], true),
            "",
        )
    },
];

impl Provider {
    pub(crate) fn spec(self) -> &'static ProviderSpec {
        PROVIDERS
            .iter()
            .find(|s| s.provider == self)
            .expect("every provider has a spec")
    }

    /// Canonical LiteLLM provider name (e.g. `"together_ai"`).
    pub fn name(self) -> &'static str {
        self.spec().names[0]
    }

    /// Parse a LiteLLM provider name (case-insensitive), including aliases.
    pub fn from_name(name: &str) -> Option<Provider> {
        let name = name.to_ascii_lowercase();
        PROVIDERS
            .iter()
            .find(|s| s.names.contains(&name.as_str()))
            .map(|s| s.provider)
    }

    /// Infer the provider of a bare model name the way LiteLLM does for the
    /// common cases, falling back to the pricing table's `litellm_provider`.
    pub fn infer(model: &str) -> Option<Provider> {
        let m = model.to_ascii_lowercase();
        let is_o_series = ["o1", "o3", "o4"]
            .iter()
            .any(|p| m == *p || m.starts_with(&format!("{p}-")));
        if is_o_series
            || [
                "gpt-",
                "chatgpt-",
                "text-embedding-",
                "omni-moderation",
                "davinci",
                "babbage",
                "codex-",
            ]
            .iter()
            .any(|p| m.starts_with(p))
        {
            return Some(Provider::OpenAi);
        }
        if m.starts_with("claude-") {
            return Some(Provider::Anthropic);
        }
        if m.starts_with("gemini-") || m.starts_with("gemma-") {
            return Some(Provider::Gemini);
        }
        pricing::lookup(model)
            .and_then(|p| p.litellm_provider)
            .and_then(|name| Provider::from_name(&name))
    }

    pub(crate) fn protocol(self) -> Protocol {
        self.spec().protocol
    }
}

impl fmt::Display for Provider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A credential whose `Debug` output is redacted.
#[derive(Clone, PartialEq, Eq)]
pub struct Secret(String);

impl Secret {
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn expose(&self) -> &str {
        &self.0
    }
}

impl fmt::Debug for Secret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Secret(***)")
    }
}

/// One upstream model endpoint.
#[derive(Debug, Clone, PartialEq)]
pub struct Deployment {
    pub provider: Provider,
    /// Upstream model name with the provider prefix removed (for Azure, the
    /// deployment name).
    pub model: String,
    /// The `model` string as configured (e.g. `"openai/gpt-4o"`).
    pub litellm_model: String,
    pub api_key: Option<Secret>,
    /// Resolved base URL (configured, from env, or the provider default).
    pub api_base: Option<String>,
    pub api_version: Option<String>,
    pub organization: Option<String>,
    pub timeout: Option<Duration>,
    pub stream_timeout: Option<Duration>,
    /// Upstream retries LiteLLM would attempt; informational for the server
    /// (the [`crate::Client`] itself never retries).
    pub max_retries: Option<u32>,
    pub extra_headers: Vec<(String, String)>,
    /// Object merged into OpenAI-compatible request bodies.
    pub extra_body: JsonObject,
    /// Deployment-level defaults for request parameters
    /// ([`REQUEST_DEFAULT_KEYS`]); the request wins when it sets them.
    pub request_defaults: JsonObject,
    /// Pricing overrides (USD per token).
    pub input_cost_per_token: Option<f64>,
    pub output_cost_per_token: Option<f64>,
    pub rpm: Option<u64>,
    pub tpm: Option<u64>,
    pub order: Option<i64>,
    /// Canned response for every request (LiteLLM `mock_response`).
    pub mock_response: Option<String>,
    /// Unrecognised keys (env references resolved), not sent upstream.
    pub extra: JsonObject,
}

impl Deployment {
    /// Parse `litellm_params`, resolving `os.environ/` references against the
    /// process environment.
    pub fn from_litellm_params(params: &Value) -> Result<Self, ProviderError> {
        Self::from_litellm_params_with_env(params, |name| std::env::var(name).ok())
    }

    /// Parse `litellm_params` with an injectable environment lookup.
    pub fn from_litellm_params_with_env(
        params: &Value,
        env: impl Fn(&str) -> Option<String>,
    ) -> Result<Self, ProviderError> {
        let Value::Object(raw) = params else {
            return Err(ProviderError::config(
                "config",
                "litellm_params must be an object",
            ));
        };
        let mut obj = resolve_env(Value::Object(raw.clone()), &env)?
            .as_object()
            .cloned()
            .unwrap_or_default();

        let litellm_model = take_string(&mut obj, "model")?
            .ok_or_else(|| ProviderError::config("config", "litellm_params.model is required"))?;
        let explicit = take_string(&mut obj, "custom_llm_provider")?;
        let (provider, model) = split_model(&litellm_model, explicit.as_deref())?;
        let spec = provider.spec();
        let cfg_err = |msg: String| ProviderError::config(provider.name(), msg);
        let from_env = |names: &[&str]| names.iter().find_map(|n| env(n).filter(|v| !v.is_empty()));

        let api_key = take_string(&mut obj, "api_key")?.or_else(|| from_env(spec.api_key_env));
        let configured_base = match take_string(&mut obj, "api_base")? {
            Some(b) => Some(b),
            None => take_string(&mut obj, "base_url")?,
        };
        let api_base = configured_base
            .or_else(|| from_env(spec.api_base_env))
            .or_else(|| spec.default_api_base.map(str::to_owned))
            .map(|b| {
                let b = b.trim_end_matches('/');
                if b.ends_with(spec.base_suffix) {
                    b.to_owned()
                } else {
                    format!("{b}{}", spec.base_suffix)
                }
            });
        let mut api_version = take_string(&mut obj, "api_version")?;
        if provider == Provider::Azure && api_version.is_none() {
            api_version = Some(
                from_env(&["AZURE_API_VERSION"])
                    .unwrap_or_else(|| DEFAULT_AZURE_API_VERSION.to_owned()),
            );
        }

        if api_base.is_none() && provider.protocol() != Protocol::Mock {
            return Err(cfg_err(format!(
                "api_base is required for provider '{provider}'"
            )));
        }
        if api_key.is_none() && spec.requires_api_key {
            return Err(cfg_err(format!(
                "api_key is required for provider '{provider}' (set api_key or {})",
                spec.api_key_env.join("/")
            )));
        }

        let mut extra_headers = Vec::new();
        for key in ["headers", "extra_headers"] {
            match obj.remove(key) {
                None | Some(Value::Null) => {}
                Some(Value::Object(h)) => {
                    for (k, v) in h {
                        let v = scalar_string(&v)
                            .ok_or_else(|| cfg_err(format!("{key}.{k} must be a string")))?;
                        extra_headers.push((k, v));
                    }
                }
                Some(_) => return Err(cfg_err(format!("{key} must be an object"))),
            }
        }
        let extra_body = match obj.remove("extra_body") {
            None | Some(Value::Null) => JsonObject::new(),
            Some(Value::Object(b)) => b,
            Some(_) => return Err(cfg_err("extra_body must be an object".into())),
        };
        let mut request_defaults = JsonObject::new();
        for key in REQUEST_DEFAULT_KEYS {
            if let Some(v) = obj.remove(*key).filter(|v| !v.is_null()) {
                request_defaults.insert((*key).to_owned(), v);
            }
        }

        Ok(Deployment {
            provider,
            model,
            litellm_model,
            api_key: api_key.map(Secret),
            api_base,
            api_version,
            organization: take_string(&mut obj, "organization")?,
            timeout: take_number(&mut obj, "timeout")?
                .map(seconds)
                .transpose()
                .map_err(cfg_err)?,
            stream_timeout: take_number(&mut obj, "stream_timeout")?
                .map(seconds)
                .transpose()
                .map_err(cfg_err)?,
            max_retries: take_number(&mut obj, "max_retries")?.map(|n| n as u32),
            extra_headers,
            extra_body,
            request_defaults,
            input_cost_per_token: take_number(&mut obj, "input_cost_per_token")?,
            output_cost_per_token: take_number(&mut obj, "output_cost_per_token")?,
            rpm: take_number(&mut obj, "rpm")?.map(|n| n as u64),
            tpm: take_number(&mut obj, "tpm")?.map(|n| n as u64),
            order: take_number(&mut obj, "order")?.map(|n| n as i64),
            mock_response: take_string(&mut obj, "mock_response")?,
            extra: obj,
        })
    }

    /// Effective pricing: the vendored LiteLLM table entry for this model,
    /// with `input_cost_per_token` / `output_cost_per_token` overrides
    /// applied. `None` if the model is unknown and no override is set.
    pub fn pricing(&self) -> Option<Pricing> {
        let base = pricing::lookup_with_provider(self.provider.name(), &self.model);
        if self.input_cost_per_token.is_none() && self.output_cost_per_token.is_none() {
            return base;
        }
        let mut p = base.unwrap_or_else(|| Pricing {
            litellm_provider: Some(self.provider.name().to_owned()),
            ..Pricing::default()
        });
        if let Some(c) = self.input_cost_per_token {
            p.input_cost_per_token = c;
        }
        if let Some(c) = self.output_cost_per_token {
            p.output_cost_per_token = c;
        }
        Some(p)
    }

    pub(crate) fn api_base(&self) -> &str {
        self.api_base.as_deref().unwrap_or_default()
    }
}

/// Split `"provider/model"`. An unknown prefix is treated as part of a bare
/// model name (e.g. `"meta-llama/Llama-3"` with `custom_llm_provider`).
fn split_model(model: &str, explicit: Option<&str>) -> Result<(Provider, String), ProviderError> {
    if let Some(name) = explicit {
        let provider = Provider::from_name(name)
            .ok_or_else(|| ProviderError::config(name, format!("unknown provider '{name}'")))?;
        let rest = match model.split_once('/') {
            Some((prefix, rest)) if Provider::from_name(prefix) == Some(provider) => rest,
            _ => model,
        };
        return Ok((provider, rest.to_owned()));
    }
    if let Some((prefix, rest)) = model.split_once('/')
        && let Some(provider) = Provider::from_name(prefix)
    {
        if rest.is_empty() {
            return Err(ProviderError::config(
                prefix,
                format!("model name missing in '{model}'"),
            ));
        }
        return Ok((provider, rest.to_owned()));
    }
    Provider::infer(model)
        .map(|p| (p, model.to_owned()))
        .ok_or_else(|| {
            ProviderError::config(
                "config",
                format!(
                    "cannot determine the provider for model '{model}'; use '<provider>/{model}'"
                ),
            )
        })
}

const ENV_PREFIX: &str = "os.environ/";

/// Recursively replace `os.environ/NAME` strings.
fn resolve_env(
    value: Value,
    env: &impl Fn(&str) -> Option<String>,
) -> Result<Value, ProviderError> {
    Ok(match value {
        Value::String(s) => match s.strip_prefix(ENV_PREFIX) {
            Some(name) => Value::String(env(name).ok_or_else(|| {
                ProviderError::config(
                    "config",
                    format!("environment variable '{name}' is not set"),
                )
            })?),
            None => Value::String(s),
        },
        Value::Array(items) => Value::Array(
            items
                .into_iter()
                .map(|v| resolve_env(v, env))
                .collect::<Result<_, _>>()?,
        ),
        Value::Object(map) => Value::Object(
            map.into_iter()
                .map(|(k, v)| Ok((k, resolve_env(v, env)?)))
                .collect::<Result<_, ProviderError>>()?,
        ),
        other => other,
    })
}

fn scalar_string(v: &Value) -> Option<String> {
    match v {
        Value::String(s) => Some(s.clone()),
        Value::Number(n) => Some(n.to_string()),
        Value::Bool(b) => Some(b.to_string()),
        _ => None,
    }
}

fn take_string(obj: &mut JsonObject, key: &str) -> Result<Option<String>, ProviderError> {
    match obj.remove(key) {
        None | Some(Value::Null) => Ok(None),
        Some(v) => scalar_string(&v)
            .map(Some)
            .ok_or_else(|| ProviderError::config("config", format!("{key} must be a string"))),
    }
}

/// A number, also accepted as a numeric string (env values are strings).
fn take_number(obj: &mut JsonObject, key: &str) -> Result<Option<f64>, ProviderError> {
    let bad = || ProviderError::config("config", format!("{key} must be a number"));
    match obj.remove(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::Number(n)) => n.as_f64().map(Some).ok_or_else(bad),
        Some(Value::String(s)) => s.trim().parse::<f64>().map(Some).map_err(|_| bad()),
        Some(_) => Err(bad()),
    }
}

fn seconds(n: f64) -> Result<Duration, String> {
    Duration::try_from_secs_f64(n).map_err(|_| format!("invalid duration: {n}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn env(name: &str) -> Option<String> {
        match name {
            "MY_KEY" => Some("sk-from-env".into()),
            "OPENAI_API_KEY" => Some("sk-openai".into()),
            "ANTHROPIC_API_KEY" => Some("sk-ant".into()),
            "GEMINI_API_KEY" => Some("gm".into()),
            "TIMEOUT" => Some("12.5".into()),
            _ => None,
        }
    }

    fn parse(v: Value) -> Result<Deployment, ProviderError> {
        Deployment::from_litellm_params_with_env(&v, env)
    }

    #[test]
    fn provider_prefixes() {
        let cases = [
            ("openai/gpt-4o", Provider::OpenAi, "gpt-4o"),
            (
                "anthropic/claude-3-5-sonnet-20241022",
                Provider::Anthropic,
                "claude-3-5-sonnet-20241022",
            ),
            ("gemini/gemini-1.5-pro", Provider::Gemini, "gemini-1.5-pro"),
            ("groq/llama3-8b-8192", Provider::Groq, "llama3-8b-8192"),
            (
                "openrouter/anthropic/claude-3.5-sonnet",
                Provider::OpenRouter,
                "anthropic/claude-3.5-sonnet",
            ),
            (
                "together_ai/meta-llama/Llama-3-70b",
                Provider::TogetherAi,
                "meta-llama/Llama-3-70b",
            ),
            ("ollama_chat/llama3", Provider::OllamaChat, "llama3"),
            ("fake/anything", Provider::Mock, "anything"),
        ];
        for (model, provider, name) in cases {
            let d = parse(json!({"model": model, "api_key": "k"})).unwrap();
            assert_eq!((d.provider, d.model.as_str()), (provider, name), "{model}");
            assert_eq!(d.litellm_model, model);
        }
    }

    #[test]
    fn infers_bare_names() {
        assert_eq!(Provider::infer("gpt-4o-mini"), Some(Provider::OpenAi));
        assert_eq!(Provider::infer("o1"), Some(Provider::OpenAi));
        assert_eq!(Provider::infer("o3-mini"), Some(Provider::OpenAi));
        assert_eq!(
            Provider::infer("text-embedding-3-small"),
            Some(Provider::OpenAi)
        );
        assert_eq!(
            Provider::infer("claude-3-haiku-20240307"),
            Some(Provider::Anthropic)
        );
        assert_eq!(Provider::infer("gemini-2.0-flash"), Some(Provider::Gemini));
        assert_eq!(Provider::infer("o1x"), None);
        assert_eq!(Provider::infer("totally-unknown-model"), None);
        let d = parse(json!({"model": "gpt-4o"})).unwrap();
        assert_eq!(d.provider, Provider::OpenAi);
        assert_eq!(d.api_key.unwrap().expose(), "sk-openai");
        assert!(parse(json!({"model": "totally-unknown-model"})).is_err());
    }

    #[test]
    fn os_environ_indirection() {
        let d = parse(json!({
            "model": "openai/gpt-4o",
            "api_key": "os.environ/MY_KEY",
            "timeout": "os.environ/TIMEOUT",
            "extra_headers": {"X-Key": "os.environ/MY_KEY"},
        }))
        .unwrap();
        assert_eq!(d.api_key.as_ref().unwrap().expose(), "sk-from-env");
        assert_eq!(d.timeout, Some(Duration::from_secs_f64(12.5)));
        assert_eq!(
            d.extra_headers,
            vec![("X-Key".to_owned(), "sk-from-env".to_owned())]
        );
        let err =
            parse(json!({"model": "openai/gpt-4o", "api_key": "os.environ/NOPE"})).unwrap_err();
        assert!(err.message().contains("NOPE"));
    }

    #[test]
    fn all_fields() {
        let d = parse(json!({
            "model": "azure/my-deployment",
            "api_key": "az",
            "api_base": "https://res.openai.azure.com/",
            "api_version": "2024-06-01",
            "organization": "org-1",
            "stream_timeout": 5,
            "max_retries": 2,
            "input_cost_per_token": 0.000001,
            "output_cost_per_token": 0.000002,
            "rpm": 100,
            "tpm": 10000,
            "order": 1,
            "temperature": 0.2,
            "weight": 3,
            "extra_body": {"foo": "bar"},
        }))
        .unwrap();
        assert_eq!(d.provider, Provider::Azure);
        assert_eq!(d.model, "my-deployment");
        assert_eq!(d.api_base.as_deref(), Some("https://res.openai.azure.com"));
        assert_eq!(d.api_version.as_deref(), Some("2024-06-01"));
        assert_eq!(d.organization.as_deref(), Some("org-1"));
        assert_eq!(d.stream_timeout, Some(Duration::from_secs(5)));
        assert_eq!(d.max_retries, Some(2));
        assert_eq!((d.rpm, d.tpm, d.order), (Some(100), Some(10000), Some(1)));
        assert_eq!(d.request_defaults["temperature"], 0.2);
        assert_eq!(d.extra["weight"], 3);
        assert_eq!(d.extra_body["foo"], "bar");
        let p = d.pricing().unwrap();
        assert_eq!(
            (p.input_cost_per_token, p.output_cost_per_token),
            (0.000001, 0.000002)
        );
        assert!(
            !format!("{d:?}").contains("\"az\""),
            "api key must be redacted"
        );
    }

    #[test]
    fn defaults_and_requirements() {
        let d = parse(json!({"model": "anthropic/claude-sonnet-4-5"})).unwrap();
        assert_eq!(d.api_base.as_deref(), Some("https://api.anthropic.com"));
        assert_eq!(d.api_key.unwrap().expose(), "sk-ant");

        let d =
            parse(json!({"model": "azure/dep", "api_key": "k", "api_base": "https://x"})).unwrap();
        assert_eq!(d.api_version.as_deref(), Some(DEFAULT_AZURE_API_VERSION));

        let d = parse(json!({"model": "ollama/llama3", "api_base": "http://gpu:11434/"})).unwrap();
        assert_eq!(d.api_base.as_deref(), Some("http://gpu:11434/v1"));
        assert!(d.api_key.is_none());
        let d = parse(json!({"model": "ollama_chat/llama3"})).unwrap();
        assert_eq!(d.api_base.as_deref(), Some("http://localhost:11434/v1"));
        let d =
            parse(json!({"model": "ollama/llama3", "api_base": "http://gpu:11434/v1"})).unwrap();
        assert_eq!(d.api_base.as_deref(), Some("http://gpu:11434/v1"));

        assert_eq!(
            parse(json!({"model": "hosted_vllm/m"})).unwrap_err().kind(),
            crate::ErrorKind::Config
        );
        let d =
            parse(json!({"model": "hosted_vllm/m", "api_base": "http://vllm:8000/v1"})).unwrap();
        assert_eq!(d.api_base.as_deref(), Some("http://vllm:8000/v1"));
        assert!(
            parse(json!({"model": "groq/llama3-8b-8192"})).is_err(),
            "groq key required"
        );
        assert!(
            parse(json!({"model": "azure/dep", "api_key": "k"})).is_err(),
            "azure base required"
        );
        assert!(parse(json!({"api_key": "k"})).is_err());
        assert!(parse(json!("openai/gpt-4o")).is_err());
    }

    #[test]
    fn custom_llm_provider_override() {
        let d = parse(json!({
            "model": "meta-llama/Llama-3-8b",
            "custom_llm_provider": "openai_like",
            "api_base": "http://h/v1",
        }))
        .unwrap();
        assert_eq!(d.provider, Provider::OpenAiLike);
        assert_eq!(d.model, "meta-llama/Llama-3-8b");
    }

    #[test]
    fn provider_names_round_trip() {
        for spec in PROVIDERS {
            assert_eq!(
                Provider::from_name(spec.provider.name()),
                Some(spec.provider)
            );
        }
        assert_eq!(Provider::from_name("VLLM"), Some(Provider::HostedVllm));
    }

    #[test]
    fn pricing_from_table() {
        let d = parse(json!({"model": "openai/gpt-4o"})).unwrap();
        let p = d.pricing().unwrap();
        assert!(p.input_cost_per_token > 0.0);
        let d = parse(json!({"model": "fake/none", "input_cost_per_token": 0.5})).unwrap();
        let p = d.pricing().unwrap();
        assert_eq!(
            (p.input_cost_per_token, p.output_cost_per_token),
            (0.5, 0.0)
        );
    }
}
