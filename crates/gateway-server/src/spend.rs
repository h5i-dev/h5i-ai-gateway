//! Spend logs: the kernel emits one per settled or expired reservation, the
//! store queues it in the outbox in the same transaction as the charge, and
//! a dispatcher delivers it to the operator's sink (the log, or a webhook in
//! the manner of LiteLLM's generic logging callback).

use gateway_kernel::{CallStatus, SpendLog};
use h5i_app_core::TenantId;
use h5i_app_pg::outbox::{Deliver, Delivery};
use serde_json::{Value, json};
use std::time::Duration;

/// Nano-dollars per US dollar.
pub const NANO: f64 = 1e9;

pub fn usd(nano: u64) -> f64 {
    nano as f64 / NANO
}

/// A dollar amount from a request as nano-dollars; `None` (no limit) is `UNLIMITED`.
pub fn nano(usd: Option<f64>) -> u64 {
    match usd {
        None => gateway_kernel::UNLIMITED,
        Some(d) if d.is_nan() || d <= 0.0 => 0,
        Some(d) => {
            let n = (d * NANO).round();
            if n >= u64::MAX as f64 { gateway_kernel::UNLIMITED } else { n as u64 }
        }
    }
}

pub fn status_str(s: CallStatus) -> &'static str {
    match s {
        CallStatus::Success => "success",
        CallStatus::Failure => "failure",
        CallStatus::Retryable => "failure",
        CallStatus::Expired => "expired",
    }
}

/// A spend log as JSON, with LiteLLM's `LiteLLM_SpendLogs` field names where
/// one exists.
pub fn json(tenant: TenantId, log: &SpendLog) -> Value {
    json!({
        "request_id": log.reservation.to_string(),
        "org_id": tenant.0,
        "api_key": log.key.to_string(),
        "team_id": if log.team == 0 { Value::Null } else { log.team.to_string().into() },
        "model_id": log.deployment.to_string(),
        "model_group_id": log.model,
        "prompt_tokens": log.prompt_tokens,
        "completion_tokens": log.completion_tokens,
        "total_tokens": log.prompt_tokens.saturating_add(log.completion_tokens),
        "spend": usd(log.cost),
        "spend_nano_usd": log.cost,
        "endTime": log.at,
        "status": status_str(log.status),
        "retryable_failure": log.status == CallStatus::Retryable,
    })
}

/// The outbox payload of a spend log.
pub fn payload(tenant: TenantId, log: &SpendLog) -> Vec<u8> {
    serde_json::to_vec(&json(tenant, log)).unwrap_or_default()
}

/// Where the dispatcher sends spend logs.
#[derive(Clone, Debug)]
pub enum Sink {
    /// One `tracing` event per log.
    Log,
    /// POST the JSON with an `Idempotency-Key` header (deliveries repeat on retry).
    Webhook(String),
}

#[derive(Clone, Default)]
pub struct Deliverer {
    http: reqwest::Client,
}

impl Deliver<Sink> for Deliverer {
    async fn deliver(&self, sink: &Sink, d: &Delivery) -> Result<(), String> {
        match sink {
            Sink::Log => {
                tracing::info!(target: "spend", key = %d.key, payload = %String::from_utf8_lossy(&d.payload), "spend log");
                Ok(())
            }
            Sink::Webhook(url) => {
                let resp = self
                    .http
                    .post(url) // h5i-allow: no-actor (an outgoing webhook, not a route)
                    .header("content-type", "application/json")
                    .header("idempotency-key", &d.key)
                    .body(d.payload.clone())
                    .timeout(Duration::from_secs(10))
                    .send()
                    .await
                    .map_err(|e| e.to_string())?;
                if resp.status().is_success() { Ok(()) } else { Err(format!("webhook answered {}", resp.status())) }
            }
        }
    }
}

/// Reads delivered and pending spend logs back from the outbox, newest first.
/// A read path for `/spend/logs`, outside the kernel: it changes nothing.
pub struct SpendReader {
    client: tokio_postgres::Client,
}

impl SpendReader {
    pub async fn connect(url: &str) -> Result<Self, tokio_postgres::Error> {
        let (client, conn) = tokio_postgres::connect(url, tokio_postgres::NoTls).await?;
        tokio::spawn(async move {
            if let Err(e) = conn.await {
                tracing::warn!(error = %e, "spend log reader connection closed");
            }
        });
        Ok(SpendReader { client })
    }

    pub async fn recent(&self, tenant: TenantId, limit: i64) -> Result<Vec<Value>, tokio_postgres::Error> {
        let rows = self
            .client
            .query(
                "SELECT payload FROM h5i_outbox WHERE tenant_id = $1 AND dest = $2 ORDER BY id DESC LIMIT $3",
                &[&(tenant.0 as i64), &(crate::kernel::SPEND_LOGS as i64), &limit],
            )
            .await?;
        Ok(rows.iter().filter_map(|r| serde_json::from_slice(r.get::<_, &[u8]>(0)).ok()).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dollars_and_nanos() {
        assert_eq!(nano(Some(1.5)), 1_500_000_000);
        assert_eq!(nano(None), gateway_kernel::UNLIMITED);
        assert_eq!(nano(Some(-1.0)), 0);
        assert_eq!(usd(2_500), 2.5e-6);
    }
}
