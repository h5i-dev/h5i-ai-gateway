//! `h5i-gateway --config config.yaml [--port 4000] [--host 0.0.0.0]`
//!
//! Reads a LiteLLM `config.yaml`. With `general_settings.database_url` (or
//! `DATABASE_URL`) the kernel's state lives in PostgreSQL and every request
//! runs in a SERIALIZABLE transaction; without one it lives in memory.

use gateway_server::cache::Cache;
use gateway_server::config::{Config, process_env, resolve};
use gateway_server::guardrails::Guardrails;
use gateway_server::kernel::{Backend, Gateway, GatewayStore, MemoryExecutor, SPEND_LOGS};
use gateway_server::registry::Registry;
use gateway_server::spend::{self, Deliverer, Sink, SpendReader};
use gateway_server::{AppState, ProxySettings, auth::GatewayAuth, router, sweep, sync};
use h5i_app_core::TenantId;
use h5i_app_pg::outbox::DispatchConfig;
use h5i_app_pg::{Engine, EngineConfig, pool, with_schema};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

struct Args {
    config: Option<PathBuf>,
    host: String,
    port: u16,
}

fn args() -> Result<Args, String> {
    let mut a = Args {
        config: std::env::var("LITELLM_CONFIG").ok().map(PathBuf::from),
        host: std::env::var("HOST").unwrap_or_else(|_| "0.0.0.0".into()),
        port: std::env::var("PORT").ok().and_then(|p| p.parse().ok()).unwrap_or(4000),
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        let mut value = || it.next().ok_or(format!("{flag} needs a value"));
        match flag.as_str() {
            "--config" | "-c" => a.config = Some(PathBuf::from(value()?)),
            "--host" => a.host = value()?,
            "--port" | "-p" => a.port = value()?.parse().map_err(|_| "invalid --port")?,
            "--help" | "-h" => {
                println!("usage: h5i-gateway --config config.yaml [--host 0.0.0.0] [--port 4000]");
                std::process::exit(0);
            }
            other => return Err(format!("unknown argument {other}")),
        }
    }
    Ok(a)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "info,h5i_app_pg=warn".into()))
        .init();
    let args = args()?;
    let config = match &args.config {
        Some(path) => Config::load(path)?,
        None => Config::default(),
    };
    // LiteLLM's `environment_variables` section, before any secret is resolved.
    for (k, v) in &config.environment_variables {
        let v = v.as_str().map(str::to_string).unwrap_or_else(|| v.to_string());
        // SAFETY: still single-threaded with respect to environment access;
        // nothing else reads or writes the environment yet.
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

    let registry = Registry::from_config(&config, &process_env)?;
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
    sync(&state, &config).await?;
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

    let addr = format!("{}:{}", args.host, args.port);
    let listener = tokio::net::TcpListener::bind(&addr).await?;
    // Streamed responses are many small writes; without TCP_NODELAY each one
    // waits for the client's delayed ACK (~40 ms).
    let listener = axum::serve::ListenerExt::tap_io(listener, |tcp| {
        let _ = tcp.set_nodelay(true);
    });
    tracing::info!(%addr, "h5i-gateway listening");
    axum::serve(listener, router(state)).with_graceful_shutdown(shutdown()).await?;
    Ok(())
}

async fn shutdown() {
    let _ = tokio::signal::ctrl_c().await;
}
