//! h5i-ai-gateway: an OpenAI-compatible LLM gateway, a Rust port of the
//! LiteLLM proxy, built on h5i-app.
//!
//! The kernel (`gateway-kernel`, proven in `proofs/`) makes every decision:
//! who may call which model, budgets, rate limits, routing, cooldowns and
//! spend. This crate is the shell around it: HTTP, authentication, the
//! configuration file, the provider calls (`gateway-providers`) and the
//! spend log sink. It decides nothing; the kernel's `Command`s are its only
//! way to change state.

pub mod anthropic_api;
pub mod auth;
pub mod batcher;
pub mod cache;
pub mod config;
pub mod error;
pub mod guardrails;
pub mod kernel;
pub mod management;
pub mod media;
pub mod proxy;
pub mod registry;
pub mod responses_api;
pub mod spend;
pub mod ui;

use crate::auth::GatewayAuth;
use crate::config::Config;
use crate::error::ApiError;
use crate::kernel::{Backend, Gateway};
use crate::registry::Registry;
use crate::spend::SpendReader;
use axum::Router;
use axum::extract::FromRef;
use axum::routing::{get, post};
use gateway_kernel::{Command, Principal, Reply};
use h5i_app_core::TenantId;
use h5i_app_http::Auth;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

/// How the proxy retries and falls back; from the configuration.
#[derive(Debug, Clone)]
pub struct ProxySettings {
    /// The tenant of the master key.
    pub org: u64,
    /// Further deployments to try in a model group after a retryable failure.
    pub num_retries: u32,
    /// Model groups to try once a group has no deployment left.
    pub fallbacks: HashMap<String, Vec<String>>,
    /// Names clients may use for a model group.
    pub aliases: HashMap<String, String>,
    pub timeout: Duration,
    /// `max_tokens` to reserve for when neither the request nor the model sets one.
    pub default_max_tokens: u64,
}

/// What every handler shares.
#[derive(Clone)]
pub struct AppState {
    pub backend: Arc<Backend>,
    pub keys: Arc<GatewayAuth>,
    pub registry: Arc<Registry>,
    pub client: gateway_providers::Client,
    pub settings: Arc<ProxySettings>,
    pub spend: Option<Arc<SpendReader>>,
    /// The configured guardrails (`guardrails:`); empty when none.
    pub guardrails: Arc<guardrails::Guardrails>,
    /// The response cache (`litellm_settings.cache`), if enabled.
    pub cache: Option<Arc<cache::Cache>>,
}

impl FromRef<AppState> for Auth<Gateway> {
    fn from_ref(st: &AppState) -> Self {
        Auth(st.keys.clone())
    }
}

impl AppState {
    /// Run a kernel command; a refusal becomes the matching API error.
    pub async fn run(&self, actor: &Principal, cmd: Command) -> Result<Reply, ApiError> {
        self.backend.run(actor, &cmd).await?.map_err(ApiError::refusal)
    }

    /// The master key's principal, for the shell's own housekeeping.
    pub fn operator(&self) -> Principal {
        Principal { org: self.settings.org, key: 0, master: true, now: 0 }
    }
}

/// The gateway's routes. Every route but the health checks authenticates.
pub fn router(state: AppState) -> Router {
    use management as m;
    Router::new()
        // Inference (OpenAI-compatible).
        .route("/v1/chat/completions", post(proxy::chat_completions))
        .route("/chat/completions", post(proxy::chat_completions))
        .route("/openai/deployments/{model}/chat/completions", post(proxy::azure_chat_completions))
        .route("/v1/embeddings", post(proxy::embeddings))
        .route("/embeddings", post(proxy::embeddings))
        .route("/v1/models", get(m::list_models))
        .route("/models", get(m::list_models))
        // Keys.
        .route("/key/generate", post(m::generate_key))
        .route("/key/update", post(m::update_key))
        .route("/key/delete", post(m::delete_keys))
        .route("/key/block", post(m::block_key))
        .route("/key/unblock", post(m::unblock_key))
        .route("/key/reset_spend", post(m::reset_key_spend))
        .route("/key/info", get(m::key_info))
        .route("/key/list", get(m::list_keys))
        // Teams.
        .route("/team/new", post(m::new_team))
        .route("/team/update", post(m::update_team))
        .route("/team/delete", post(m::delete_teams))
        .route("/team/block", post(m::block_team))
        .route("/team/unblock", post(m::unblock_team))
        .route("/team/info", get(m::team_info))
        .route("/team/list", get(m::list_teams))
        // Models, spend, health.
        .route("/model/info", get(m::model_info))
        .route("/v1/model/info", get(m::model_info))
        .route("/spend/logs", get(m::spend_logs))
        .route("/global/spend", get(m::global_spend))
        .route("/health/liveliness", get(m::liveliness))
        .route("/health/readiness", get(m::readiness))
        .merge(anthropic_api::routes())
        .merge(responses_api::routes())
        .merge(media::routes())
        .merge(ui::routes())
        .with_state(state)
}

/// Bring the kernel's router settings and deployments in line with the
/// configuration: configure, upsert every configured deployment, and delete
/// the ones no longer configured. Records the model group ids.
pub async fn sync(state: &AppState, config: &Config) -> Result<(), ApiError> {
    let op = state.operator();
    let rs = &config.router_settings;
    state
        .run(
            &op,
            Command::Configure {
                allowed_fails: rs.allowed_fails.unwrap_or(3),
                cooldown_secs: rs.cooldown_time.map(|s| s.max(0.0).ceil() as u64).unwrap_or(5),
                reservation_ttl: config.general_settings.reservation_ttl.unwrap_or_else(|| (state.settings.timeout.as_secs() + 60).max(120)),
            },
        )
        .await?;
    for d in state.registry.all() {
        let reply = state.run(&op, Command::UpsertDeployment { model: d.model_name.as_bytes().to_vec(), spec: d.spec }).await?;
        if let Reply::Created(model) = reply {
            state.registry.set_model_name(model, &d.model_name);
        }
    }
    if let Reply::State(s) = state.run(&op, Command::Dump).await? {
        for d in &s.deployments {
            if state.registry.get(d.id).is_none() {
                tracing::info!(deployment = d.id, "removing deployment no longer in the config");
                state.run(&op, Command::DeleteDeployment { id: d.id }).await?;
            }
        }
    }
    Ok(())
}

/// Release reservations whose calls never settled (a crashed or cancelled
/// request), once they pass the reservation TTL. The kernel refuses to
/// expire a reservation early, so running this often is harmless.
pub async fn sweep(state: &AppState, tenant: TenantId) -> Result<usize, ApiError> {
    let op = Principal { org: tenant.0, ..state.operator() };
    let Reply::State(s) = state.run(&op, Command::Dump).await? else {
        return Ok(0);
    };
    let ttl = s.settings.reservation_ttl;
    let now = auth::unix_now();
    let mut released = 0;
    for r in s.reservations.iter().filter(|r| now >= r.created_at.saturating_add(ttl)) {
        match state.backend.run(&op, &Command::Expire { reservation: r.id }).await? {
            Ok(_) => released += 1,
            Err(e) => tracing::debug!(reservation = r.id, ?e, "not expired"),
        }
    }
    Ok(released)
}
