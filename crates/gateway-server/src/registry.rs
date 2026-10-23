//! The configured deployments: for each kernel deployment id, how to reach
//! the provider (credentials stay here, never in the kernel's rows) and the
//! prices and limits the kernel decides with.
//!
//! Prices are per unit of the deployment's mode (`model_info.mode`, else
//! LiteLLM's table, else implied by its own media prices): tokens for chat
//! and embeddings; images, seconds of audio or characters for media
//! deployments ([`crate::media::pricing`] documents the units). They come
//! from the deployment's `litellm_params` and `model_info` (e.g.
//! `input_cost_per_token`, `output_cost_per_image`, `input_cost_per_second`,
//! `input_cost_per_character`), else from LiteLLM's table (for Azure, under
//! `model_info.base_model`).

use crate::config::{Config, ModelEntry, deployment_id};
use crate::media::pricing::{MediaPricing, Prices};
use gateway_kernel::{DeploymentSpec, UNLIMITED};
use gateway_providers::{Deployment, pricing};
use serde_json::{Value, json};
use std::collections::HashMap;
use std::sync::RwLock;

/// One configured deployment.
#[derive(Debug, Clone)]
pub struct Deployed {
    /// The model group clients name.
    pub model_name: String,
    /// The deployment's id in the config (`model_info.id`, or the kernel id).
    pub config_id: String,
    pub deployment: Deployment,
    /// What the kernel knows: prices in nano-dollars per unit, limits, order.
    pub spec: DeploymentSpec,
    /// The output limit of the model, if known, to reserve for.
    pub max_output_tokens: Option<u64>,
    /// `chat`, `embedding`, `image_generation`, `audio_transcription`, …
    pub mode: Option<String>,
    /// How a media deployment counts its units; `None` for token-priced modes.
    pub media: Option<MediaPricing>,
}

impl Deployed {
    /// `litellm_params` without credentials, for `/model/info`.
    pub fn public_params(&self) -> Value {
        json!({
            "model": self.deployment.litellm_model,
            "api_base": self.deployment.api_base,
            "api_version": self.deployment.api_version,
            "rpm": self.deployment.rpm,
            "tpm": self.deployment.tpm,
            "order": self.deployment.order,
        })
    }
}

#[derive(Debug, thiserror::Error)]
pub enum RegistryError {
    #[error("model_list entry {model_name:?}: {source}")]
    Deployment { model_name: String, source: gateway_providers::ProviderError },
    #[error("model_list entries {a:?} and {b:?} have the same id")]
    DuplicateId { a: String, b: String },
}

#[derive(Debug, Default)]
pub struct Registry {
    by_id: HashMap<u64, Deployed>,
    /// Kernel model group ids, learned when deployments are synced.
    model_names: RwLock<HashMap<u64, String>>,
}

impl Registry {
    pub fn from_config(config: &Config, env: &dyn Fn(&str) -> Option<String>) -> Result<Registry, RegistryError> {
        let mut by_id = HashMap::new();
        for entry in &config.model_list {
            let id = deployment_id(entry);
            let d = deployed(entry, id, env)?;
            if let Some(old) = by_id.insert(id, d) {
                return Err(RegistryError::DuplicateId { a: old.model_name, b: entry.model_name.clone() });
            }
        }
        Ok(Registry { by_id, model_names: RwLock::default() })
    }

    pub fn get(&self, id: u64) -> Option<&Deployed> {
        self.by_id.get(&id)
    }

    pub fn all(&self) -> Vec<&Deployed> {
        let mut v: Vec<&Deployed> = self.by_id.values().collect();
        v.sort_by_key(|d| d.spec.id);
        v
    }

    pub fn set_model_name(&self, id: u64, name: &str) {
        self.model_names.write().unwrap_or_else(|e| e.into_inner()).insert(id, name.to_string());
    }

    pub fn model_name(&self, id: u64) -> Option<String> {
        self.model_names.read().unwrap_or_else(|e| e.into_inner()).get(&id).cloned()
    }

    /// The kernel id of a model group, by name.
    pub fn model_id(&self, name: &str) -> Option<u64> {
        self.model_names.read().unwrap_or_else(|e| e.into_inner()).iter().find(|(_, n)| n.as_str() == name).map(|(id, _)| *id)
    }

    /// The largest known output limit among a model group's deployments.
    pub fn max_output_tokens(&self, model_name: &str) -> Option<u64> {
        self.by_id.values().filter(|d| d.model_name == model_name).filter_map(|d| d.max_output_tokens).max()
    }
}

fn deployed(entry: &ModelEntry, id: u64, env: &dyn Fn(&str) -> Option<String>) -> Result<Deployed, RegistryError> {
    let params = Value::Object(entry.litellm_params.clone());
    let deployment = Deployment::from_litellm_params_with_env(&params, env)
        .map_err(|source| RegistryError::Deployment { model_name: entry.model_name.clone(), source })?;
    // Prices: the deployment's own, else LiteLLM's table (for Azure, under `model_info.base_model`).
    let base = entry.model_info.get("base_model").and_then(Value::as_str);
    let table = base.and_then(pricing::lookup).or_else(|| deployment.pricing());
    let input = deployment.input_cost_per_token.or(table.as_ref().map(|p| p.input_cost_per_token));
    let output = deployment.output_cost_per_token.or(table.as_ref().map(|p| p.output_cost_per_token));
    // Media deployments are priced per image, second or character.
    let prices = Prices::resolve(table.as_ref(), &deployment, &[&deployment.extra, &entry.model_info]);
    let media = MediaPricing::new(&prices, &deployment, base.unwrap_or(&deployment.model));
    let (input_cost, output_cost) = match &media {
        Some(m) => m.unit_prices(),
        None => (input.map(pricing::to_nano_per_token).unwrap_or(0), output.map(pricing::to_nano_per_token).unwrap_or(0)),
    };
    if input_cost == 0 && output_cost == 0 && (media.is_some() || (input.is_none() && output.is_none())) {
        tracing::warn!(model = %deployment.litellm_model, "no price known; calls to it cost nothing");
    }
    let enabled = !matches!(entry.model_info.get("disabled"), Some(Value::Bool(true)));
    let spec = DeploymentSpec {
        id,
        input_cost,
        output_cost,
        rpm: deployment.rpm.unwrap_or(UNLIMITED),
        tpm: deployment.tpm.unwrap_or(UNLIMITED),
        // LiteLLM tries `order: 1` first; deployments without an order come last.
        priority: deployment.order.map(|o| o.max(0) as u64).unwrap_or(u64::from(u32::MAX)),
        enabled,
    };
    let config_id = match entry.model_info.get("id") {
        Some(Value::String(s)) => s.clone(),
        _ => id.to_string(),
    };
    Ok(Deployed {
        model_name: entry.model_name.clone(),
        config_id,
        max_output_tokens: table.and_then(|p| p.max_output_tokens),
        deployment,
        spec,
        mode: prices.mode,
        media,
    })
}
