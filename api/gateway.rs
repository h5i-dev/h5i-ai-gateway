//! h5i-ai-gateway as a Vercel function. `vercel.json` rewrites every path
//! here, so the whole gateway (API and `/ui`) runs in this one function.
//!
//! The configuration is `LITELLM_CONFIG_YAML` (a whole LiteLLM `config.yaml`
//! in one environment variable) or, without it, `vercel/config.yaml` as
//! built into the binary. Set `DATABASE_URL` to PostgreSQL to keep keys,
//! budgets and spend: in memory they last only as long as one function
//! instance, and instances do not share them.

use gateway_server::config::Config;
use gateway_server::{boot, router};
use tower::ServiceBuilder;
use vercel_runtime::Error;
use vercel_runtime::axum::VercelLayer;

const CONFIG: &str = include_str!("../vercel/config.yaml");

#[tokio::main]
async fn main() -> Result<(), Error> {
    tracing_subscriber::fmt()
        .with_ansi(false)
        .with_env_filter(tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "info,h5i_app_pg=warn".into()))
        .init();
    let config = match std::env::var("LITELLM_CONFIG_YAML") {
        Ok(text) => Config::parse(&text)?,
        Err(_) => Config::parse(CONFIG)?,
    };
    let state = boot::start(&config).await?;
    let app = ServiceBuilder::new().layer(VercelLayer::new()).service(router(state));
    vercel_runtime::run(app).await
}
