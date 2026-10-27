//! Turn a configuration into a running gateway's state: the backend (memory
//! or PostgreSQL), keys, deployments, guardrails and cache, plus the
//! background tasks (spend log dispatch, reservation sweep). Shared by the
//! `h5i-gateway` binary and the Vercel function.

use crate::cache::Cache;
use crate::config::{Config, process_env, resolve};
use crate::guardrails::Guardrails;
use crate::kernel::{Backend, Gateway, GatewayStore, MemoryExecutor, SPEND_LOGS};
use crate::registry::Registry;
use crate::spend::{self, Deliverer, Sink, SpendReader};
use crate::{AppState, ProxySettings, auth::GatewayAuth, sweep, sync};
use h5i_app_core::TenantId;
use h5i_app_pg::outbox::DispatchConfig;
use h5i_app_pg::{Engine, EngineConfig, pool, with_schema};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

pub type BootError = Box<dyn std::error::Error + Send + Sync>;

/// Build the gateway's state from `config` and spawn its background tasks
/// on the current Tokio runtime.
pub async fn start(config: &Config) -> Result<AppState, BootError> {
    // LiteLLM's `environment_variables` section, before any secret is resolved.
    for (k, v) in &config.environment_variables {
        let v = v.as_str().map(str::to_string).unwrap_or_else(|| v.to_string());
        // SAFETY: called once at startup, before anything else reads or
        // writes the environment.
        unsafe { std::env::set_var(k, v) };
    }

    let gs = &config.general_settings;
    let master_key = match gs.master_key.as_deref() {
        Some(k) => Some(resolve(k, &process_env)?),
        None => std::env::var("LITELLM_MASTER_KEY").ok(),
    };
    let secret = gs
        .key_signing_secret
        .as_deref()
        .map(|s| resolve(s, &process_env))
        .transpose()?
        .or_else(|| std::env::var("LITELLM_SALT_KEY").ok())
        .or_else(|| master_key.clone())
        .ok_or("set general_settings.master_key (or LITELLM_MASTER_KEY): it administers the gateway and signs virtual keys")?;
    let org = gs.org_id.unwrap_or(1);
    let database_url = match gs.database_url.as_deref() {
        Some(u) => Some(resolve(u, &process_env)?),
        None => std::env::var("DATABASE_URL").ok(),
    };
    let sink = match gs.spend_logs.as_deref() {
        None | Some("log") => Sink::Log,
        Some(url) => Sink::Webhook(resolve(url, &process_env)?),
    };

    let (backend, reader, dispatcher) = match &database_url {
        Some(url) => {
            let url = with_schema(url, "h5i_gateway")?;
            let engine = Engine::<Gateway, GatewayStore>::new(pool(&url, 16)?, EngineConfig::default().database_time());
            engine.install_schema().await?;
            let registry = HashMap::from([(SPEND_LOGS, sink.clone())]);
            let dispatcher = engine.dispatcher(registry, Deliverer::default(), DispatchConfig::default());
            let reader = SpendReader::connect(&url).await?;
            (Backend::postgres(engine, gs.batch_max.unwrap_or(256)), Some(Arc::new(reader)), Some(dispatcher))
        }
        None => {
            tracing::warn!("no database_url: keys, budgets and spend live in memory and are lost on restart");
            // `/spend/logs` (and the admin UI) read the most recent logs back from memory.
            let reader = Arc::new(SpendReader::memory(10_000));
            let recorder = reader.clone();
            let exec = MemoryExecutor::new(Box::new(move |t, log| {
                tracing::info!(target: "spend", payload = %spend::json(t, log), "spend log");
                recorder.record(t, log);
            }));
            (Backend::Memory(exec), Some(reader), None)
        }
    };

    let registry = Registry::from_config(config, &process_env)?;
    let guardrails = Guardrails::from_config(&config.guardrails, &process_env)?;
    if !guardrails.is_empty() {
        tracing::info!(guardrails = ?guardrails.names(), "guardrails configured");
    }
    let ls = &config.litellm_settings;
    let cache = Cache::from_settings(ls.cache, &ls.cache_params, &process_env).await?;
    if let Some(c) = &cache {
        tracing::info!(backend = c.backend(), "response cache enabled");
    }
    let settings = ProxySettings {
        org,
        num_retries: config.num_retries(),
        fallbacks: config.fallbacks(),
        aliases: config.router_settings.model_group_alias.clone(),
        timeout: Duration::from_secs_f64(config.timeout_secs()),
        default_max_tokens: gs.default_max_tokens.unwrap_or(4096),
    };
    let state = AppState {
        backend: Arc::new(backend),
        keys: Arc::new(GatewayAuth::new(master_key, secret, org)),
        registry: Arc::new(registry),
        client: gateway_providers::Client::new(Default::default())?,
        settings: Arc::new(settings),
        spend: reader,
        guardrails: Arc::new(guardrails),
        cache: cache.map(Arc::new),
    };
    sync(&state, config).await?;
    tracing::info!(deployments = state.registry.all().len(), "deployments synced");

    if let Some(dispatcher) = dispatcher {
        tokio::spawn(async move {
            loop {
                if let Err(e) = dispatcher.run_once().await {
                    tracing::warn!(error = %e, "spend log dispatch failed");
                }
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
        });
    }
    let sweeper = state.clone();
    tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_secs(30)).await;
            match sweep(&sweeper, TenantId(org)).await {
                Ok(0) => {}
                Ok(n) => tracing::info!(released = n, "expired unsettled reservations"),
                Err(e) => tracing::warn!(error = %e, "reservation sweep failed"),
            }
        }
    });
    Ok(state)
}
