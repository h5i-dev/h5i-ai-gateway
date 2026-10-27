//! `h5i-gateway --config config.yaml [--port 4000] [--host 0.0.0.0]`
//!
//! Reads a LiteLLM `config.yaml`. With `general_settings.database_url` (or
//! `DATABASE_URL`) the kernel's state lives in PostgreSQL and every request
//! runs in a SERIALIZABLE transaction; without one it lives in memory.

use gateway_server::boot;
use gateway_server::config::Config;
use gateway_server::router;
use std::path::PathBuf;

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
async fn main() -> Result<(), boot::BootError> {
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "info,h5i_app_pg=warn".into()))
        .init();
    let args = args()?;
    let config = match &args.config {
        Some(path) => Config::load(path)?,
        None => Config::default(),
    };
    let state = boot::start(&config).await?;

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
