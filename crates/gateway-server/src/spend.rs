//! Spend logs: the kernel emits one per settled or expired reservation, the
//! store queues it in the outbox in the same transaction as the charge, and
//! a dispatcher delivers it to the operator's sink (the log, or a webhook in
//! the manner of LiteLLM's generic logging callback).

use gateway_kernel::{CallStatus, SpendLog};
use h5i_app_core::TenantId;
use h5i_app_pg::outbox::{Deliver, Delivery};
use serde_json::{Value, json};
use std::collections::VecDeque;
use std::sync::Mutex;
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

/// Which spend logs `/spend/logs` returns; every set field must match.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct SpendFilter {
    /// The key id (`api_key`).
    pub key: Option<u64>,
    pub team: Option<u64>,
    /// The kernel's model group id (`model_group_id`).
    pub model_group: Option<u64>,
    /// `success`, `failure` or `expired`.
    pub status: Option<String>,
    /// `endTime` at or after this Unix second.
    pub since: Option<u64>,
    /// `endTime` before this Unix second.
    pub until: Option<u64>,
}

impl SpendFilter {
    /// Whether a spend log (as [`json`] writes it) passes.
    pub fn matches(&self, log: &Value) -> bool {
        let id = |field: &str| log[field].as_str().and_then(|s| s.parse::<u64>().ok());
        let at = log["endTime"].as_u64().unwrap_or(0);
        self.key.is_none_or(|k| id("api_key") == Some(k))
            && self.team.is_none_or(|t| id("team_id") == Some(t))
            && self.model_group.is_none_or(|m| log["model_group_id"].as_u64() == Some(m))
            && self.status.as_deref().is_none_or(|s| log["status"].as_str() == Some(s))
            && self.since.is_none_or(|t| at >= t)
            && self.until.is_none_or(|t| at < t)
    }
}

/// Reads spend logs back, newest first. A read path for `/spend/logs`,
/// outside the kernel: it changes nothing.
///
/// With PostgreSQL it reads the outbox (delivered and pending logs). The
/// in-memory executor has no outbox, so its sink also hands each committed
/// log to a bounded buffer here, for development.
pub struct SpendReader {
    source: Source,
}

enum Source {
    Postgres(tokio_postgres::Client),
    Memory { logs: Mutex<VecDeque<(TenantId, Value)>>, capacity: usize },
}

impl SpendReader {
    pub async fn connect(url: &str) -> Result<Self, tokio_postgres::Error> {
        let (client, conn) = tokio_postgres::connect(url, tokio_postgres::NoTls).await?;
        tokio::spawn(async move {
            if let Err(e) = conn.await {
                tracing::warn!(error = %e, "spend log reader connection closed");
            }
        });
        Ok(SpendReader { source: Source::Postgres(client) })
    }

    /// A reader that keeps the last `capacity` logs handed to [`SpendReader::record`].
    pub fn memory(capacity: usize) -> Self {
        SpendReader { source: Source::Memory { logs: Mutex::new(VecDeque::new()), capacity: capacity.max(1) } }
    }

    /// Keep a committed spend log (in-memory readers only; PostgreSQL has the outbox).
    pub fn record(&self, tenant: TenantId, log: &SpendLog) {
        if let Source::Memory { logs, capacity } = &self.source {
            let mut logs = logs.lock().unwrap_or_else(|e| e.into_inner());
            if logs.len() >= *capacity {
                logs.pop_front();
            }
            logs.push_back((tenant, json(tenant, log)));
        }
    }

    pub async fn recent(&self, tenant: TenantId, limit: i64) -> Result<Vec<Value>, tokio_postgres::Error> {
        self.search(tenant, &SpendFilter::default(), limit).await
    }

    /// The newest `limit` logs of a tenant that pass `filter`.
    pub async fn search(&self, tenant: TenantId, filter: &SpendFilter, limit: i64) -> Result<Vec<Value>, tokio_postgres::Error> {
        let limit = limit.max(0);
        match &self.source {
            Source::Memory { logs, .. } => {
                let logs = logs.lock().unwrap_or_else(|e| e.into_inner());
                Ok(logs
                    .iter()
                    .rev()
                    .filter(|(t, v)| *t == tenant && filter.matches(v))
                    .take(limit as usize)
                    .map(|(_, v)| v.clone())
                    .collect())
            }
            Source::Postgres(client) => {
                let text = |v: Option<u64>| v.map(|v| v.to_string());
                let int = |v: Option<u64>| v.map(|v| v.min(i64::MAX as u64) as i64);
                let rows = client
                    .query(
                        "SELECT o.payload FROM h5i_outbox o, LATERAL (SELECT convert_from(o.payload, 'UTF8')::jsonb AS j) p
                         WHERE o.tenant_id = $1 AND o.dest = $2
                           AND ($4::text IS NULL OR p.j->>'api_key' = $4)
                           AND ($5::text IS NULL OR p.j->>'team_id' = $5)
                           AND ($6::text IS NULL OR p.j->>'model_group_id' = $6)
                           AND ($7::text IS NULL OR p.j->>'status' = $7)
                           AND ($8::bigint IS NULL OR (p.j->>'endTime')::bigint >= $8)
                           AND ($9::bigint IS NULL OR (p.j->>'endTime')::bigint < $9)
                         ORDER BY o.id DESC LIMIT $3",
                        &[
                            &(tenant.0 as i64),
                            &(crate::kernel::SPEND_LOGS as i64),
                            &limit,
                            &text(filter.key),
                            &text(filter.team),
                            &text(filter.model_group),
                            &filter.status,
                            &int(filter.since),
                            &int(filter.until),
                        ],
                    )
                    .await?;
                Ok(rows.iter().filter_map(|r| serde_json::from_slice(r.get::<_, &[u8]>(0)).ok()).collect())
            }
        }
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
