//! LiteLLM's management API: `/key/*`, `/team/*`, `/model/info`,
//! `/spend/*` and `/health/*`. Each handler turns JSON into a kernel command
//! and the reply back into JSON; the kernel decides who may do what.

use crate::auth::unix_now;
use crate::config::parse_duration;
use crate::error::ApiError;
use crate::kernel::{Backend, Gateway};
use crate::spend::{SpendFilter, nano, usd};
use crate::AppState;
use axum::extract::{Query, State};
use axum::Json;
use gateway_kernel::{self as k, Command, Reply, UNLIMITED};
use h5i_app_core::TenantId;
use h5i_app_http::Actor;
use serde::Deserialize;
use serde_json::{Value, json};

type Result<T> = std::result::Result<T, ApiError>;

/// An id that LiteLLM clients send as a string or a number.
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub enum Id {
    Num(u64),
    Str(String),
}

impl Id {
    fn get(&self) -> Result<u64> {
        match self {
            Id::Num(n) => Ok(*n),
            Id::Str(s) => s.parse().map_err(|_| ApiError::bad_request(format!("invalid id {s:?}"))),
        }
    }
}

/// A user id: a number, or any string, kept as its stable hash.
fn user_id(v: &Option<Value>) -> u64 {
    match v {
        Some(Value::Number(n)) => n.as_u64().unwrap_or(0),
        Some(Value::String(s)) => s.parse().unwrap_or_else(|_| {
            s.bytes().fold(0xcbf2_9ce4_8422_2325u64, |h, b| (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)) >> 1
        }),
        _ => 0,
    }
}

fn limit(v: Option<u64>) -> u64 {
    v.unwrap_or(UNLIMITED)
}

fn duration(v: &Option<String>, field: &str) -> Result<Option<u64>> {
    match v {
        None => Ok(None),
        Some(s) => parse_duration(s).map(Some).ok_or_else(|| ApiError::bad_request(format!("invalid {field} {s:?}"))),
    }
}

fn names(models: &[String]) -> Vec<Vec<u8>> {
    models.iter().map(|m| m.as_bytes().to_vec()).collect()
}

fn opt_limit(v: Option<Value>) -> Option<u64> {
    match v {
        Some(Value::Null) => Some(UNLIMITED),
        Some(v) => v.as_u64(),
        None => None,
    }
}

fn opt_budget(v: Option<Value>) -> Option<u64> {
    match v {
        Some(Value::Null) => Some(UNLIMITED),
        Some(v) => v.as_f64().map(|d| nano(Some(d))),
        None => None,
    }
}

fn time_or_null(t: u64) -> Value {
    if t == UNLIMITED { Value::Null } else { t.into() }
}

fn limit_or_null(v: u64) -> Value {
    if v == UNLIMITED { Value::Null } else { v.into() }
}

fn budget_or_null(v: u64) -> Value {
    if v == UNLIMITED { Value::Null } else { usd(v).into() }
}

impl AppState {
    fn model_names(&self, ids: &[u64]) -> Vec<String> {
        ids.iter().map(|id| self.registry.model_name(*id).unwrap_or_else(|| id.to_string())).collect()
    }

    pub(crate) fn key_json(&self, key: &k::Key, models: &[u64], reserved: u64) -> Value {
        json!({
            "token_id": key.id.to_string(),
            "team_id": if key.team == 0 { Value::Null } else { key.team.to_string().into() },
            "user_id": key.user.to_string(),
            "spend": usd(key.spend),
            "reserved_spend": usd(reserved),
            "max_budget": budget_or_null(key.max_budget),
            "rpm_limit": limit_or_null(key.rpm),
            "tpm_limit": limit_or_null(key.tpm),
            "max_parallel_requests": limit_or_null(key.max_parallel),
            "expires": time_or_null(key.expires_at),
            "budget_duration": if key.budget_duration == 0 { Value::Null } else { format!("{}s", key.budget_duration).into() },
            "budget_reset_at": if key.budget_duration == 0 { Value::Null } else { key.budget_reset_at.into() },
            "blocked": key.blocked,
            "user_role": if key.admin { "proxy_admin" } else { "internal_user" },
            "models": if key.all_models { Vec::new() } else { self.model_names(models) },
        })
    }

    pub(crate) fn team_json(&self, team: &k::Team, models: &[u64], reserved: u64) -> Value {
        json!({
            "team_id": team.id.to_string(),
            "spend": usd(team.spend),
            "reserved_spend": usd(reserved),
            "max_budget": budget_or_null(team.max_budget),
            "rpm_limit": limit_or_null(team.rpm),
            "tpm_limit": limit_or_null(team.tpm),
            "budget_duration": if team.budget_duration == 0 { Value::Null } else { format!("{}s", team.budget_duration).into() },
            "budget_reset_at": if team.budget_duration == 0 { Value::Null } else { team.budget_reset_at.into() },
            "blocked": team.blocked,
            "models": if team.all_models { Vec::new() } else { self.model_names(models) },
        })
    }

    /// The key id a request names: a virtual key, or a key id (`token_id`).
    fn key_id(&self, actor: &Actor<Gateway>, key: &str) -> Result<u64> {
        if let Ok(id) = key.parse::<u64>() {
            return Ok(id);
        }
        let (org, id) = self.keys.parse_key(key).map_err(|_| ApiError::bad_request("invalid key"))?;
        if org != actor.principal().org {
            return Err(ApiError::not_found("key not found"));
        }
        Ok(id)
    }

    async fn dump(&self, actor: &Actor<Gateway>) -> Result<k::Snapshot> {
        match self.run(actor.principal(), Command::Dump).await? {
            Reply::State(s) => Ok(s),
            r => Err(ApiError::internal(format!("unexpected reply {r:?}"))),
        }
    }
}

// ---------------------------------------------------------------------------
// Keys

#[derive(Debug, Default, Deserialize)]
pub struct GenerateKey {
    #[serde(default)]
    pub models: Vec<String>,
    pub max_budget: Option<f64>,
    pub rpm_limit: Option<u64>,
    pub tpm_limit: Option<u64>,
    pub max_parallel_requests: Option<u64>,
    /// How long the key works, e.g. `30d`; unset for ever.
    pub duration: Option<String>,
    pub budget_duration: Option<String>,
    pub team_id: Option<Id>,
    pub user_id: Option<Value>,
    pub user_role: Option<String>,
    pub key_alias: Option<String>,
    pub metadata: Option<Value>,
}

pub async fn generate_key(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<GenerateKey>) -> Result<Json<Value>> {
    let expires_at = match duration(&req.duration, "duration")? {
        Some(d) => unix_now().saturating_add(d),
        None => UNLIMITED,
    };
    let spec = k::KeySpec {
        team: match &req.team_id {
            Some(t) => t.get()?,
            None => 0,
        },
        user: user_id(&req.user_id),
        max_budget: nano(req.max_budget),
        rpm: limit(req.rpm_limit),
        tpm: limit(req.tpm_limit),
        max_parallel: limit(req.max_parallel_requests),
        expires_at,
        budget_duration: duration(&req.budget_duration, "budget_duration")?.unwrap_or(0),
        admin: req.user_role.as_deref() == Some("proxy_admin"),
        all_models: req.models.is_empty() || req.models.iter().any(|m| m == "*" || m == "all-proxy-models"),
    };
    let models = if spec.all_models { Vec::new() } else { names(&req.models) };
    let id = match st.run(actor.principal(), Command::CreateKey { spec, models }).await? {
        Reply::Created(id) => id,
        r => return Err(ApiError::internal(format!("unexpected reply {r:?}"))),
    };
    let key = st.keys.issue(actor.principal().org, id, expires_at);
    Ok(Json(json!({
        "key": key,
        "key_name": format!("sk-...{}", &key[key.len().saturating_sub(4)..]),
        "token_id": id.to_string(),
        "key_alias": req.key_alias,
        "expires": time_or_null(expires_at),
        "models": req.models,
        "max_budget": req.max_budget,
        "rpm_limit": req.rpm_limit,
        "tpm_limit": req.tpm_limit,
        "max_parallel_requests": req.max_parallel_requests,
        "team_id": req.team_id.as_ref().map(|t| match t { Id::Num(n) => n.to_string(), Id::Str(s) => s.clone() }),
        "user_id": spec.user.to_string(),
        "budget_duration": req.budget_duration,
        "metadata": req.metadata.unwrap_or_else(|| json!({})),
    })))
}

#[derive(Debug, Default, Deserialize)]
pub struct UpdateKey {
    pub key: String,
    pub models: Option<Vec<String>>,
    pub max_budget: Option<Value>,
    pub rpm_limit: Option<Value>,
    pub tpm_limit: Option<Value>,
    pub max_parallel_requests: Option<Value>,
    pub duration: Option<String>,
    pub budget_duration: Option<String>,
    pub blocked: Option<bool>,
}

pub async fn update_key(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<UpdateKey>) -> Result<Json<Value>> {
    let id = st.key_id(&actor, &req.key)?;
    let all = req.models.as_ref().map(|m| m.is_empty() || m.iter().any(|m| m == "*" || m == "all-proxy-models"));
    let patch = k::KeyPatch {
        max_budget: opt_budget(req.max_budget),
        rpm: opt_limit(req.rpm_limit),
        tpm: opt_limit(req.tpm_limit),
        max_parallel: opt_limit(req.max_parallel_requests),
        expires_at: duration(&req.duration, "duration")?.map(|d| unix_now().saturating_add(d)),
        budget_duration: duration(&req.budget_duration, "budget_duration")?,
        blocked: req.blocked,
        all_models: all,
    };
    st.run(actor.principal(), Command::UpdateKey { id, patch }).await?;
    if let (Some(models), Some(false)) = (&req.models, all) {
        st.run(actor.principal(), Command::SetKeyModels { id, models: names(models) }).await?;
    }
    key_info_json(&st, &actor, id).await
}

#[derive(Debug, Deserialize)]
pub struct KeyRef {
    pub key: String,
}

pub async fn block_key(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<KeyRef>) -> Result<Json<Value>> {
    set_blocked(st, actor, req.key, true).await
}

pub async fn unblock_key(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<KeyRef>) -> Result<Json<Value>> {
    set_blocked(st, actor, req.key, false).await
}

async fn set_blocked(st: AppState, actor: Actor<Gateway>, key: String, blocked: bool) -> Result<Json<Value>> {
    let id = st.key_id(&actor, &key)?;
    let patch = k::KeyPatch { blocked: Some(blocked), ..no_key_patch() };
    st.run(actor.principal(), Command::UpdateKey { id, patch }).await?;
    key_info_json(&st, &actor, id).await
}

fn no_key_patch() -> k::KeyPatch {
    k::KeyPatch { max_budget: None, rpm: None, tpm: None, max_parallel: None, expires_at: None, budget_duration: None, blocked: None, all_models: None }
}

#[derive(Debug, Deserialize)]
pub struct DeleteKeys {
    #[serde(default)]
    pub keys: Vec<String>,
}

pub async fn delete_keys(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<DeleteKeys>) -> Result<Json<Value>> {
    let mut deleted = Vec::new();
    for key in &req.keys {
        let id = st.key_id(&actor, key)?;
        st.run(actor.principal(), Command::DeleteKey { id }).await?;
        deleted.push(key.clone());
    }
    Ok(Json(json!({ "deleted_keys": deleted })))
}

pub async fn reset_key_spend(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<KeyRef>) -> Result<Json<Value>> {
    let id = st.key_id(&actor, &req.key)?;
    st.run(actor.principal(), Command::ResetKeySpend { id }).await?;
    key_info_json(&st, &actor, id).await
}

#[derive(Debug, Deserialize)]
pub struct KeyQuery {
    pub key: Option<String>,
}

/// `/key/info?key=...`: a key's limits and spend; without `key`, the caller's.
pub async fn key_info(State(st): State<AppState>, actor: Actor<Gateway>, Query(q): Query<KeyQuery>) -> Result<Json<Value>> {
    let id = match &q.key {
        Some(key) => st.key_id(&actor, key)?,
        None if actor.principal().master => return Err(ApiError::bad_request("pass ?key=")),
        None => actor.principal().key,
    };
    key_info_json(&st, &actor, id).await
}

async fn key_info_json(st: &AppState, actor: &Actor<Gateway>, id: u64) -> Result<Json<Value>> {
    match st.run(actor.principal(), Command::KeyInfo { id }).await? {
        Reply::KeyInfo { key, models, reserved } => Ok(Json(json!({ "key": id.to_string(), "info": st.key_json(&key, &models, reserved) }))),
        r => Err(ApiError::internal(format!("unexpected reply {r:?}"))),
    }
}

pub async fn list_keys(State(st): State<AppState>, actor: Actor<Gateway>) -> Result<Json<Value>> {
    let s = st.dump(&actor).await?;
    let keys: Vec<Value> = s
        .keys
        .iter()
        .map(|key| {
            let models = k::models_of_key(&s.key_models, key.id);
            st.key_json(key, &models, k::reserved_by_key(&s.reservations, key.id))
        })
        .collect();
    Ok(Json(json!({ "keys": keys, "total_count": keys.len() })))
}

// ---------------------------------------------------------------------------
// Teams

#[derive(Debug, Default, Deserialize)]
pub struct NewTeam {
    pub team_alias: Option<String>,
    #[serde(default)]
    pub models: Vec<String>,
    pub max_budget: Option<f64>,
    pub rpm_limit: Option<u64>,
    pub tpm_limit: Option<u64>,
    pub budget_duration: Option<String>,
}

pub async fn new_team(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<NewTeam>) -> Result<Json<Value>> {
    let spec = k::TeamSpec {
        max_budget: nano(req.max_budget),
        rpm: limit(req.rpm_limit),
        tpm: limit(req.tpm_limit),
        budget_duration: duration(&req.budget_duration, "budget_duration")?.unwrap_or(0),
        all_models: req.models.is_empty() || req.models.iter().any(|m| m == "*" || m == "all-proxy-models"),
    };
    let models = if spec.all_models { Vec::new() } else { names(&req.models) };
    let id = match st.run(actor.principal(), Command::CreateTeam { spec, models }).await? {
        Reply::Created(id) => id,
        r => return Err(ApiError::internal(format!("unexpected reply {r:?}"))),
    };
    let mut info = team_info_value(&st, &actor, id).await?;
    info["team_alias"] = req.team_alias.into();
    Ok(Json(info))
}

#[derive(Debug, Deserialize)]
pub struct UpdateTeam {
    pub team_id: Id,
    pub models: Option<Vec<String>>,
    pub max_budget: Option<Value>,
    pub rpm_limit: Option<Value>,
    pub tpm_limit: Option<Value>,
    pub budget_duration: Option<String>,
    pub blocked: Option<bool>,
}

pub async fn update_team(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<UpdateTeam>) -> Result<Json<Value>> {
    let id = req.team_id.get()?;
    let all = req.models.as_ref().map(|m| m.is_empty() || m.iter().any(|m| m == "*" || m == "all-proxy-models"));
    let patch = k::TeamPatch {
        max_budget: opt_budget(req.max_budget),
        rpm: opt_limit(req.rpm_limit),
        tpm: opt_limit(req.tpm_limit),
        budget_duration: duration(&req.budget_duration, "budget_duration")?,
        blocked: req.blocked,
        all_models: all,
    };
    st.run(actor.principal(), Command::UpdateTeam { id, patch }).await?;
    if let (Some(models), Some(false)) = (&req.models, all) {
        st.run(actor.principal(), Command::SetTeamModels { id, models: names(models) }).await?;
    }
    Ok(Json(team_info_value(&st, &actor, id).await?))
}

#[derive(Debug, Deserialize)]
pub struct TeamRef {
    pub team_id: Id,
}

pub async fn block_team(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<TeamRef>) -> Result<Json<Value>> {
    set_team_blocked(st, actor, req.team_id, true).await
}

pub async fn unblock_team(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<TeamRef>) -> Result<Json<Value>> {
    set_team_blocked(st, actor, req.team_id, false).await
}

async fn set_team_blocked(st: AppState, actor: Actor<Gateway>, team: Id, blocked: bool) -> Result<Json<Value>> {
    let id = team.get()?;
    let patch = k::TeamPatch { max_budget: None, rpm: None, tpm: None, budget_duration: None, blocked: Some(blocked), all_models: None };
    st.run(actor.principal(), Command::UpdateTeam { id, patch }).await?;
    Ok(Json(team_info_value(&st, &actor, id).await?))
}

#[derive(Debug, Deserialize)]
pub struct DeleteTeams {
    #[serde(default)]
    pub team_ids: Vec<Id>,
}

pub async fn delete_teams(State(st): State<AppState>, actor: Actor<Gateway>, Json(req): Json<DeleteTeams>) -> Result<Json<Value>> {
    let mut deleted = Vec::new();
    for t in &req.team_ids {
        let id = t.get()?;
        st.run(actor.principal(), Command::DeleteTeam { id }).await?;
        deleted.push(id.to_string());
    }
    Ok(Json(json!({ "deleted_teams": deleted })))
}

#[derive(Debug, Deserialize)]
pub struct TeamQuery {
    pub team_id: Id,
}

pub async fn team_info(State(st): State<AppState>, actor: Actor<Gateway>, Query(q): Query<TeamQuery>) -> Result<Json<Value>> {
    let id = q.team_id.get()?;
    Ok(Json(team_info_value(&st, &actor, id).await?))
}

async fn team_info_value(st: &AppState, actor: &Actor<Gateway>, id: u64) -> Result<Value> {
    match st.run(actor.principal(), Command::TeamInfo { id }).await? {
        Reply::TeamInfo { team, models, reserved } => Ok(json!({ "team_id": id.to_string(), "team_info": st.team_json(&team, &models, reserved) })),
        r => Err(ApiError::internal(format!("unexpected reply {r:?}"))),
    }
}

pub async fn list_teams(State(st): State<AppState>, actor: Actor<Gateway>) -> Result<Json<Value>> {
    let s = st.dump(&actor).await?;
    let teams: Vec<Value> = s
        .teams
        .iter()
        .map(|t| st.team_json(t, &k::models_of_team(&s.team_models, t.id), k::reserved_by_team(&s.reservations, t.id)))
        .collect();
    Ok(Json(Value::Array(teams)))
}

// ---------------------------------------------------------------------------
// Models

/// `/v1/models`: the model groups the caller may call.
pub async fn list_models(State(st): State<AppState>, actor: Actor<Gateway>) -> Result<Json<Value>> {
    let models = match st.run(actor.principal(), Command::ListModels).await? {
        Reply::Models(ms) => ms,
        r => return Err(ApiError::internal(format!("unexpected reply {r:?}"))),
    };
    let data: Vec<Value> = models
        .iter()
        .map(|m| json!({ "id": String::from_utf8_lossy(&m.name), "object": "model", "created": 1_677_610_602u64, "owned_by": "openai" }))
        .collect();
    Ok(Json(json!({ "object": "list", "data": data })))
}

/// `/model/info`: every deployment with its prices, limits and health, but
/// never its credentials. Admins only.
pub async fn model_info(State(st): State<AppState>, actor: Actor<Gateway>) -> Result<Json<Value>> {
    let s = st.dump(&actor).await?;
    let now = unix_now();
    let data: Vec<Value> = s
        .deployments
        .iter()
        .map(|d| {
            let entry = st.registry.get(d.id);
            json!({
                "model_name": st.registry.model_name(d.model),
                "litellm_params": entry.map(|e| e.public_params()).unwrap_or(Value::Null),
                "model_info": {
                    "id": entry.map(|e| e.config_id.clone()).unwrap_or_else(|| d.id.to_string()),
                    "db_model": false,
                    "input_cost_per_token": usd(d.input_cost),
                    "output_cost_per_token": usd(d.output_cost),
                    "rpm": limit_or_null(d.rpm),
                    "tpm": limit_or_null(d.tpm),
                    "order": d.priority,
                    "enabled": d.enabled,
                    "cooling_down": now < d.cooldown_until,
                    "cooldown_until": if d.cooldown_until == 0 { Value::Null } else { d.cooldown_until.into() },
                },
            })
        })
        .collect();
    Ok(Json(json!({ "data": data })))
}

// ---------------------------------------------------------------------------
// Spend and health

#[derive(Debug, Default, Deserialize)]
pub struct SpendQuery {
    pub limit: Option<i64>,
    /// A virtual key or key id (`token_id`).
    pub api_key: Option<String>,
    pub team_id: Option<String>,
    /// A model group name.
    pub model: Option<String>,
    /// `success`, `failure` or `expired`.
    pub status: Option<String>,
    /// `YYYY-MM-DD` (UTC) or Unix seconds; logs at or after it.
    pub start_date: Option<String>,
    /// `YYYY-MM-DD` (UTC, inclusive) or Unix seconds (exclusive); logs before it.
    pub end_date: Option<String>,
}

/// Unix seconds at the start of a `YYYY-MM-DD` day (UTC).
fn day_start(s: &str) -> Option<u64> {
    let mut it = s.splitn(3, '-');
    let (y, m, d): (i64, i64, i64) = (it.next()?.parse().ok()?, it.next()?.parse().ok()?, it.next()?.parse().ok()?);
    if !(1..=12).contains(&m) || !(1..=31).contains(&d) {
        return None;
    }
    // Days from the civil date (Howard Hinnant's algorithm).
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let doy = (153 * ((m + 9) % 12) + 2) / 5 + d - 1;
    let days = era * 146_097 + yoe * 365 + yoe / 4 - yoe / 100 + doy - 719_468;
    u64::try_from(days).ok().map(|d| d * 86_400)
}

/// A `start_date`/`end_date` bound; a date ending the range includes its whole day.
fn time_bound(v: &Option<String>, field: &str, end: bool) -> Result<Option<u64>> {
    let Some(s) = v.as_deref().map(str::trim).filter(|s| !s.is_empty()) else {
        return Ok(None);
    };
    if let Ok(secs) = s.parse::<u64>() {
        return Ok(Some(secs));
    }
    let day = day_start(s).ok_or_else(|| ApiError::bad_request(format!("invalid {field} {s:?}: use YYYY-MM-DD or Unix seconds")))?;
    Ok(Some(if end { day + 86_400 } else { day }))
}

fn non_empty(v: &Option<String>) -> Option<&str> {
    v.as_deref().map(str::trim).filter(|s| !s.is_empty())
}

/// `/spend/logs`: the newest spend logs, filtered by key, team, model group,
/// status and time, each with its model group's name. Admins only.
pub async fn spend_logs(State(st): State<AppState>, actor: Actor<Gateway>, Query(q): Query<SpendQuery>) -> Result<Json<Value>> {
    // The kernel decides who is an admin; a Dump is refused otherwise.
    st.dump(&actor).await?;
    let reader = st.spend.as_ref().ok_or_else(|| ApiError::not_found("spend logs need a database (general_settings.database_url)"))?;
    let filter = SpendFilter {
        key: non_empty(&q.api_key).map(|k| st.key_id(&actor, k)).transpose()?,
        team: non_empty(&q.team_id).map(|t| Id::Str(t.to_string()).get()).transpose()?,
        model_group: match non_empty(&q.model) {
            None => None,
            Some(name) => match st.registry.model_id(name) {
                Some(id) => Some(id),
                // No such model group, so no logs.
                None => return Ok(Json(json!([]))),
            },
        },
        status: non_empty(&q.status).map(str::to_string),
        since: time_bound(&q.start_date, "start_date", false)?,
        until: time_bound(&q.end_date, "end_date", true)?,
    };
    let mut logs = reader
        .search(TenantId(actor.principal().org), &filter, q.limit.unwrap_or(100).clamp(1, 10_000))
        .await
        .map_err(|e| ApiError::unavailable(e.to_string()))?;
    for log in &mut logs {
        let group = log["model_group_id"].as_u64().and_then(|id| st.registry.model_name(id));
        let deployment = log["model_id"].as_str().and_then(|id| id.parse().ok()).and_then(|id| st.registry.get(id));
        log["model_group"] = group.into();
        log["model"] = deployment.map(|d| d.deployment.litellm_model.clone()).into();
    }
    Ok(Json(Value::Array(logs)))
}

/// `/global/spend`: what every key and team spent, and what calls hold. Admins only.
pub async fn global_spend(State(st): State<AppState>, actor: Actor<Gateway>) -> Result<Json<Value>> {
    let s = st.dump(&actor).await?;
    let keys: u64 = s.keys.iter().fold(0, |acc, k| acc.saturating_add(k.spend));
    let reserved: u64 = s.reservations.iter().fold(0, |acc, r| acc.saturating_add(r.amount));
    Ok(Json(json!({ "spend": usd(keys), "reserved_spend": usd(reserved), "in_flight": s.reservations.len() })))
}

pub async fn liveliness() -> Json<Value> {
    Json(json!("I'm alive!"))
}

pub async fn readiness(State(st): State<AppState>) -> Json<Value> {
    Json(json!({
        "status": "healthy",
        "db": if matches!(*st.backend, Backend::Postgres(_)) { "connected" } else { "Not connected" },
        "litellm_version": concat!("h5i-ai-gateway ", env!("CARGO_PKG_VERSION")),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dates_are_utc_day_starts() {
        assert_eq!(day_start("1970-01-01"), Some(0));
        assert_eq!(day_start("2000-03-01"), Some(951_868_800));
        assert_eq!(day_start("2024-02-29"), Some(1_709_164_800));
        assert_eq!(day_start("2024-13-01"), None);
        assert_eq!(day_start("1969-12-31"), None);
        assert_eq!(day_start("today"), None);
        assert_eq!(time_bound(&Some("2024-02-29".into()), "end_date", true).unwrap(), Some(1_709_251_200));
        assert_eq!(time_bound(&Some("1700000000".into()), "end_date", true).unwrap(), Some(1_700_000_000));
        assert_eq!(time_bound(&Some(" ".into()), "start_date", false).unwrap(), None);
    }
}
