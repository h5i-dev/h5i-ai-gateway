//! Response caching, configured like LiteLLM's:
//!
//! ```yaml
//! litellm_settings:
//!   cache: true
//!   cache_params:
//!     type: local            # or redis (host, port, password, username, or url)
//!     ttl: 600               # seconds
//!     namespace: prod        # key prefix
//!     max_size_in_memory: 200
//!     mode: default_on       # default_off: only requests with cache: {use-cache: true}
//!     supported_call_types: [acompletion, aembedding]
//! ```
//!
//! The key is a SHA-256 of the call type, the model group (after aliases)
//! and every response-determining request field, as canonical JSON (object
//! keys sorted): not the API key, `user`, `stream`/`stream_options`,
//! `metadata`, guardrail and cache controls, or other gateway-only fields.
//! Responses are shared across keys, as in LiteLLM.
//!
//! Per request, `cache: {"no-cache": true}` skips the lookup,
//! `"no-store": true` skips storing, `"ttl": N` stores for N seconds,
//! `"s-maxage": N` accepts only entries at most N seconds old, and
//! `"namespace": "..."` prefixes the key.
//!
//! A hit is still admitted by the kernel and settled at zero tokens (see
//! `proxy::admit_cached`): key and team access, blocks, expiry, budgets and
//! RPM still apply, and a zero-cost spend log records the call.
//!
//! The cache never blocks a request: a backend failure is logged and treated
//! as a miss.

use crate::config::{ConfigError, resolve};
use gateway_providers::types::JsonObject;
use gateway_providers::{ChatRequest, EmbeddingRequest, GATEWAY_ONLY_FIELDS};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// The calls the cache can serve.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallType {
    Chat,
    Embeddings,
}

impl CallType {
    fn as_str(self) -> &'static str {
        match self {
            CallType::Chat => "chat",
            CallType::Embeddings => "embeddings",
        }
    }
}

/// Request fields that do not determine the response.
const NOT_KEYED: &[&str] = &[
    "user",
    "stream",
    "stream_options",
    "litellm_call_id",
    "litellm_trace_id",
    "request_timeout",
    "extra_headers",
];

/// A request's cache controls (`cache: {...}`).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Controls {
    pub no_cache: bool,
    pub no_store: bool,
    pub ttl: Option<f64>,
    pub s_maxage: Option<f64>,
    pub namespace: Option<String>,
    /// `use-cache`, for `mode: default_off`.
    pub use_cache: Option<bool>,
}

impl Controls {
    pub fn from_extra(extra: &JsonObject) -> Controls {
        let Some(Value::Object(c)) = extra.get("cache") else {
            return Controls::default();
        };
        let flag = |k: &str| {
            c.get(k)
                .is_some_and(|v| v.as_bool() == Some(true) || v.as_str() == Some("true"))
        };
        let num = |k: &str| {
            c.get(k).and_then(|v| {
                v.as_f64()
                    .or_else(|| v.as_str().and_then(|s| s.parse().ok()))
            })
        };
        Controls {
            no_cache: flag("no-cache"),
            no_store: flag("no-store"),
            ttl: num("ttl"),
            s_maxage: num("s-maxage").or_else(|| num("s-max-age")),
            namespace: c
                .get("namespace")
                .and_then(Value::as_str)
                .map(str::to_string),
            use_cache: c.get("use-cache").and_then(Value::as_bool),
        }
    }
}

/// The in-memory backend: bounded, least recently used out first, with TTLs.
pub struct Memory {
    map: HashMap<String, MemEntry>,
    /// Recency order: tick -> key.
    order: BTreeMap<u64, String>,
    tick: u64,
    max_items: usize,
}

struct MemEntry {
    value: String,
    expires: Option<Instant>,
    tick: u64,
}

/// Values larger than this are not kept in memory.
const MAX_ITEM_BYTES: usize = 1 << 20;

impl Memory {
    pub fn new(max_items: usize) -> Memory {
        Memory {
            map: HashMap::new(),
            order: BTreeMap::new(),
            tick: 0,
            max_items: max_items.max(1),
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn remove(&mut self, key: &str) {
        if let Some(e) = self.map.remove(key) {
            self.order.remove(&e.tick);
        }
    }

    pub fn get(&mut self, key: &str, now: Instant) -> Option<String> {
        let expired = self.map.get(key)?.expires.is_some_and(|t| now >= t);
        if expired {
            self.remove(key);
            return None;
        }
        self.tick += 1;
        let tick = self.tick;
        let e = self.map.get_mut(key)?;
        self.order.remove(&e.tick);
        e.tick = tick;
        self.order.insert(tick, key.to_string());
        Some(e.value.clone())
    }

    pub fn set(&mut self, key: &str, value: String, ttl: Option<Duration>, now: Instant) {
        if value.len() > MAX_ITEM_BYTES {
            return;
        }
        self.remove(key);
        if self.map.len() >= self.max_items {
            // Expired entries first, then the least recently used.
            let expired: Vec<String> = self
                .map
                .iter()
                .filter(|(_, e)| e.expires.is_some_and(|t| now >= t))
                .map(|(k, _)| k.clone())
                .collect();
            for k in expired {
                self.remove(&k);
            }
            while self.map.len() >= self.max_items {
                let Some((_, k)) = self.order.pop_first() else {
                    break;
                };
                self.map.remove(&k);
            }
        }
        self.tick += 1;
        self.order.insert(self.tick, key.to_string());
        self.map.insert(
            key.to_string(),
            MemEntry {
                value,
                expires: ttl.map(|d| now + d),
                tick: self.tick,
            },
        );
    }
}

enum Store {
    Memory(Mutex<Memory>),
    Redis(redis::aio::ConnectionManager),
}

/// The response cache.
pub struct Cache {
    store: Store,
    ttl: Option<Duration>,
    namespace: Option<String>,
    chat: bool,
    embeddings: bool,
    default_off: bool,
}

/// How long a Redis operation may take before it counts as a miss.
const REDIS_TIMEOUT: Duration = Duration::from_secs(2);

fn now_secs() -> f64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs_f64())
        .unwrap_or(0.0)
}

fn param_str(
    p: &serde_json::Map<String, Value>,
    k: &str,
    env: &dyn Fn(&str) -> Option<String>,
) -> Result<Option<String>, ConfigError> {
    match p.get(k) {
        Some(Value::String(s)) => resolve(s, env).map(Some),
        Some(Value::Number(n)) => Ok(Some(n.to_string())),
        _ => Ok(None),
    }
}

fn secs(v: Option<&Value>) -> Option<Duration> {
    let s = v.and_then(|v| {
        v.as_f64()
            .or_else(|| v.as_str().and_then(|s| s.parse().ok()))
    })?;
    (s > 0.0 && s.is_finite()).then(|| Duration::from_secs_f64(s))
}

impl Cache {
    /// The cache `litellm_settings` describes, if `cache: true`.
    pub async fn from_settings(
        enabled: bool,
        params: &serde_json::Map<String, Value>,
        env: &dyn Fn(&str) -> Option<String>,
    ) -> Result<Option<Cache>, ConfigError> {
        if !enabled {
            return Ok(None);
        }
        let kind = params
            .get("type")
            .and_then(Value::as_str)
            .unwrap_or("local");
        let (store, ttl) = match kind {
            "local" | "in-memory" | "memory" => {
                let max = params
                    .get("max_size_in_memory")
                    .and_then(Value::as_u64)
                    .unwrap_or(200) as usize;
                let ttl = secs(params.get("ttl"))
                    .or(secs(params.get("default_in_memory_ttl")))
                    .or(Some(Duration::from_secs(600)));
                (Store::Memory(Mutex::new(Memory::new(max))), ttl)
            }
            "redis" => {
                let url = redis_url(params, env)?;
                let client = redis::Client::open(url.as_str()).map_err(|e| {
                    ConfigError::Invalid(format!("cache_params: invalid Redis address: {e}"))
                })?;
                let conn = client.get_connection_manager().await.map_err(|e| {
                    ConfigError::Invalid(format!("cache_params: cannot connect to Redis: {e}"))
                })?;
                (
                    Store::Redis(conn),
                    secs(params.get("ttl")).or(secs(params.get("default_in_redis_ttl"))),
                )
            }
            other => {
                return Err(ConfigError::Invalid(format!(
                    "cache_params.type {other:?} is not supported (local or redis)"
                )));
            }
        };
        let (mut chat, mut embeddings) = (true, true);
        if let Some(Value::Array(types)) = params.get("supported_call_types") {
            let has = |names: &[&str]| {
                types
                    .iter()
                    .any(|t| t.as_str().is_some_and(|t| names.contains(&t)))
            };
            chat = has(&[
                "completion",
                "acompletion",
                "chat_completion",
                "anthropic_messages",
                "responses",
                "aresponses",
            ]);
            embeddings = has(&["embedding", "aembedding"]);
        }
        let mode = params
            .get("mode")
            .and_then(Value::as_str)
            .unwrap_or("default_on");
        Ok(Some(Cache {
            store,
            ttl,
            namespace: param_str(params, "namespace", env)?,
            chat,
            embeddings,
            default_off: mode == "default_off",
        }))
    }

    /// An in-memory cache, for tests and development.
    pub fn memory(max_items: usize, ttl: Option<Duration>) -> Cache {
        Cache {
            store: Store::Memory(Mutex::new(Memory::new(max_items))),
            ttl,
            namespace: None,
            chat: true,
            embeddings: true,
            default_off: false,
        }
    }

    pub fn backend(&self) -> &'static str {
        match self.store {
            Store::Memory(_) => "local",
            Store::Redis(_) => "redis",
        }
    }

    fn supports(&self, call: CallType) -> bool {
        match call {
            CallType::Chat => self.chat,
            CallType::Embeddings => self.embeddings,
        }
    }

    fn enabled(&self, c: &Controls) -> bool {
        !self.default_off || c.use_cache == Some(true)
    }

    /// Whether to look the request up.
    pub fn reads(&self, c: &Controls) -> bool {
        self.enabled(c) && !c.no_cache
    }

    /// Whether to store the response.
    pub fn writes(&self, c: &Controls) -> bool {
        self.enabled(c) && !c.no_store && c.ttl.is_none_or(|t| t > 0.0)
    }

    /// The key of a request body for `call` on model group `group`, or
    /// `None` if this call is not cached.
    pub fn key(&self, call: CallType, group: &str, body: &Value, c: &Controls) -> Option<String> {
        if !self.supports(call) || !(self.reads(c) || self.writes(c)) {
            return None;
        }
        let hash = key_hash(call, group, body);
        Some(match c.namespace.as_ref().or(self.namespace.as_ref()) {
            Some(ns) => format!("{ns}:{hash}"),
            None => hash,
        })
    }

    pub fn chat_key(&self, group: &str, req: &ChatRequest, c: &Controls) -> Option<String> {
        self.key(CallType::Chat, group, &serde_json::to_value(req).ok()?, c)
    }

    pub fn embedding_key(
        &self,
        group: &str,
        req: &EmbeddingRequest,
        c: &Controls,
    ) -> Option<String> {
        self.key(
            CallType::Embeddings,
            group,
            &serde_json::to_value(req).ok()?,
            c,
        )
    }

    /// The cached response under `key`, unless the controls skip the lookup
    /// or it is older than `s-maxage`.
    pub async fn get(&self, key: &str, c: &Controls) -> Option<Value> {
        if !self.reads(c) {
            return None;
        }
        let raw = match &self.store {
            Store::Memory(m) => m
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .get(key, Instant::now()),
            Store::Redis(conn) => {
                let mut conn = conn.clone();
                match tokio::time::timeout(
                    REDIS_TIMEOUT,
                    redis::cmd("GET")
                        .arg(key)
                        .query_async::<Option<String>>(&mut conn),
                )
                .await
                {
                    Ok(Ok(v)) => v,
                    Ok(Err(e)) => {
                        tracing::warn!(error = %e, "cache read failed");
                        None
                    }
                    Err(_) => {
                        tracing::warn!("cache read timed out");
                        None
                    }
                }
            }
        }?;
        let entry: Value = serde_json::from_str(&raw).ok()?;
        if let Some(max) = c.s_maxage {
            let at = entry
                .get("timestamp")
                .and_then(Value::as_f64)
                .unwrap_or(0.0);
            if now_secs() - at > max {
                return None;
            }
        }
        entry.get("response").cloned()
    }

    /// Store a response, unless the controls say not to.
    pub async fn put(&self, key: &str, response: &Value, c: &Controls) {
        if !self.writes(c) {
            return;
        }
        let ttl = c.ttl.map(Duration::from_secs_f64).or(self.ttl);
        let raw = json!({"timestamp": now_secs(), "response": response}).to_string();
        match &self.store {
            Store::Memory(m) => {
                m.lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .set(key, raw, ttl, Instant::now())
            }
            Store::Redis(conn) => {
                let mut conn = conn.clone();
                let mut cmd = redis::cmd("SET");
                cmd.arg(key).arg(raw);
                if let Some(t) = ttl {
                    cmd.arg("PX").arg(t.as_millis().max(1) as u64);
                }
                match tokio::time::timeout(REDIS_TIMEOUT, cmd.query_async::<()>(&mut conn)).await {
                    Ok(Ok(())) => {}
                    Ok(Err(e)) => tracing::warn!(error = %e, "cache write failed"),
                    Err(_) => tracing::warn!("cache write timed out"),
                }
            }
        }
    }
}

fn redis_url(
    p: &serde_json::Map<String, Value>,
    env: &dyn Fn(&str) -> Option<String>,
) -> Result<String, ConfigError> {
    if let Some(u) = param_str(p, "url", env)?
        .or(param_str(p, "redis_url", env)?)
        .or_else(|| env("REDIS_URL"))
    {
        return Ok(u);
    }
    if p.get("ssl").and_then(Value::as_bool) == Some(true) {
        return Err(ConfigError::Invalid(
            "cache_params.ssl is not supported; use a redis:// url to a TLS-terminating proxy"
                .into(),
        ));
    }
    let host = param_str(p, "host", env)?
        .or_else(|| env("REDIS_HOST"))
        .unwrap_or_else(|| "127.0.0.1".into());
    let port = param_str(p, "port", env)?
        .or_else(|| env("REDIS_PORT"))
        .unwrap_or_else(|| "6379".into());
    let password = param_str(p, "password", env)?.or_else(|| env("REDIS_PASSWORD"));
    let username = param_str(p, "username", env)?.or_else(|| env("REDIS_USERNAME"));
    let auth = match (username, password) {
        (Some(u), Some(pw)) => format!("{}:{}@", enc(&u), enc(&pw)),
        (None, Some(pw)) => format!(":{}@", enc(&pw)),
        _ => String::new(),
    };
    Ok(format!("redis://{auth}{host}:{port}/"))
}

/// Percent-encode a URL userinfo component.
fn enc(s: &str) -> String {
    s.bytes()
        .map(|b| match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' => {
                (b as char).to_string()
            }
            _ => format!("%{b:02X}"),
        })
        .collect()
}

/// SHA-256 (hex) of the call type, model group and the request's
/// response-determining fields, as canonical JSON.
pub fn key_hash(call: CallType, group: &str, body: &Value) -> String {
    let mut body = body.clone();
    if let Some(o) = body.as_object_mut() {
        for k in GATEWAY_ONLY_FIELDS
            .iter()
            .filter(|k| **k != "mock_response")
            .chain(NOT_KEYED)
        {
            o.remove(*k);
        }
        o.remove("model");
    }
    let mut material = format!("{}\n{}\n", call.as_str(), group);
    canonical(&body, &mut material);
    let digest = Sha256::digest(material.as_bytes());
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

/// JSON with object keys sorted and nulls in objects dropped (an absent
/// field and a `null` one mean the same).
pub fn canonical(v: &Value, out: &mut String) {
    match v {
        Value::Object(o) => {
            let mut keys: Vec<&String> = o
                .iter()
                .filter(|(_, v)| !v.is_null())
                .map(|(k, _)| k)
                .collect();
            keys.sort();
            out.push('{');
            for (i, k) in keys.into_iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&Value::String(k.clone()).to_string());
                out.push(':');
                canonical(&o[k], out);
            }
            out.push('}');
        }
        Value::Array(a) => {
            out.push('[');
            for (i, x) in a.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                canonical(x, out);
            }
            out.push(']');
        }
        other => out.push_str(&other.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn chat(v: Value) -> ChatRequest {
        serde_json::from_value(v).unwrap()
    }

    #[test]
    fn keys_are_canonical() {
        let c = Cache::memory(10, None);
        let none = Controls::default();
        let a = chat(
            json!({"model": "gpt", "messages": [{"role": "user", "content": "hi"}], "temperature": 0.5, "metadata": {"x": 1}, "user": "u1"}),
        );
        let b: ChatRequest = serde_json::from_str(r#"{"temperature":0.5,"user":"u2","stream":true,"messages":[{"content":"hi","role":"user"}],"model":"alias","guardrails":["g"],"cache":{"ttl":5}}"#).unwrap();
        // Same group, same response-determining fields: same key.
        assert_eq!(c.chat_key("gpt", &a, &none), c.chat_key("gpt", &b, &none));
        // A different group, prompt, parameter or mock response: different keys.
        assert_ne!(c.chat_key("gpt", &a, &none), c.chat_key("other", &a, &none));
        let mut d = a.clone();
        d.temperature = Some(0.7);
        assert_ne!(c.chat_key("gpt", &a, &none), c.chat_key("gpt", &d, &none));
        let mut d = a.clone();
        d.extra.insert("top_k".into(), json!(3));
        assert_ne!(c.chat_key("gpt", &a, &none), c.chat_key("gpt", &d, &none));
        let mut d = a.clone();
        d.mock_response = Some("x".into());
        assert_ne!(c.chat_key("gpt", &a, &none), c.chat_key("gpt", &d, &none));
        // Chat and embeddings never share keys.
        assert_ne!(
            key_hash(CallType::Chat, "m", &json!({"input": "x"})),
            key_hash(CallType::Embeddings, "m", &json!({"input": "x"}))
        );
        // Nested key order does not matter; nulls are dropped.
        let mut s1 = String::new();
        let mut s2 = String::new();
        canonical(
            &json!({"b": {"y": 1, "x": [1, {"q": 1, "p": null}]}, "a": null}),
            &mut s1,
        );
        canonical(&json!({"b": {"x": [1, {"q": 1}], "y": 1}}), &mut s2);
        assert_eq!(s1, s2);
        assert_eq!(s1, r#"{"b":{"x":[1,{"q":1}],"y":1}}"#);
        // A namespace prefixes the key.
        let ns = Controls {
            namespace: Some("team1".into()),
            ..Controls::default()
        };
        let k = c.chat_key("gpt", &a, &ns).unwrap();
        assert!(k.starts_with("team1:") && k.len() == 6 + 64, "{k}");
    }

    #[test]
    fn controls_parse() {
        let mut extra = JsonObject::new();
        assert_eq!(Controls::from_extra(&extra), Controls::default());
        extra.insert("cache".into(), json!({"no-cache": true, "no-store": "true", "ttl": 30, "s-maxage": "10", "namespace": "n", "use-cache": true}));
        let c = Controls::from_extra(&extra);
        assert_eq!(
            c,
            Controls {
                no_cache: true,
                no_store: true,
                ttl: Some(30.0),
                s_maxage: Some(10.0),
                namespace: Some("n".into()),
                use_cache: Some(true)
            }
        );
        let cache = Cache::memory(10, None);
        assert!(!cache.reads(&c) && !cache.writes(&c));
        assert_eq!(cache.key(CallType::Chat, "m", &json!({}), &c), None);
        let off = Cache {
            default_off: true,
            ..Cache::memory(10, None)
        };
        assert!(!off.reads(&Controls::default()));
        assert!(off.reads(&Controls {
            use_cache: Some(true),
            ..Controls::default()
        }));
    }

    #[test]
    fn memory_ttl_and_eviction() {
        let t0 = Instant::now();
        let mut m = Memory::new(2);
        m.set("a", "1".into(), Some(Duration::from_secs(10)), t0);
        assert_eq!(m.get("a", t0 + Duration::from_secs(9)), Some("1".into()));
        assert_eq!(m.get("a", t0 + Duration::from_secs(10)), None);
        assert!(m.is_empty());
        // Least recently used goes first.
        m.set("a", "1".into(), None, t0);
        m.set("b", "2".into(), None, t0);
        assert!(m.get("a", t0).is_some());
        m.set("c", "3".into(), None, t0);
        assert_eq!(m.len(), 2);
        assert_eq!(m.get("b", t0), None);
        assert!(m.get("a", t0).is_some() && m.get("c", t0).is_some());
        // Expired entries are evicted before live ones.
        let mut m = Memory::new(2);
        m.set("old", "x".into(), Some(Duration::from_secs(1)), t0);
        m.set("live", "y".into(), None, t0);
        m.set("new", "z".into(), None, t0 + Duration::from_secs(5));
        assert!(m.get("live", t0).is_some() && m.get("new", t0).is_some());
        // Overwrite keeps one entry; oversized values are not kept.
        m.set("live", "y2".into(), None, t0);
        assert_eq!(m.get("live", t0), Some("y2".into()));
        m.set("big", "x".repeat(MAX_ITEM_BYTES + 1), None, t0);
        assert_eq!(m.get("big", t0), None);
    }

    #[tokio::test]
    async fn get_put_honour_controls() {
        let c = Cache::memory(10, Some(Duration::from_secs(60)));
        let none = Controls::default();
        c.put("k", &json!({"v": 1}), &none).await;
        assert_eq!(c.get("k", &none).await, Some(json!({"v": 1})));
        assert_eq!(
            c.get(
                "k",
                &Controls {
                    no_cache: true,
                    ..none.clone()
                }
            )
            .await,
            None
        );
        // Older than s-maxage: not served.
        assert_eq!(
            c.get(
                "k",
                &Controls {
                    s_maxage: Some(-1.0),
                    ..none.clone()
                }
            )
            .await,
            None
        );
        assert!(
            c.get(
                "k",
                &Controls {
                    s_maxage: Some(60.0),
                    ..none.clone()
                }
            )
            .await
            .is_some()
        );
        c.put(
            "n",
            &json!(1),
            &Controls {
                no_store: true,
                ..none.clone()
            },
        )
        .await;
        assert_eq!(c.get("n", &none).await, None);
        // A per-request TTL.
        c.put(
            "t",
            &json!(1),
            &Controls {
                ttl: Some(0.05),
                ..none.clone()
            },
        )
        .await;
        assert!(c.get("t", &none).await.is_some());
        tokio::time::sleep(Duration::from_millis(80)).await;
        assert_eq!(c.get("t", &none).await, None);
    }

    #[tokio::test]
    async fn config_and_redis_url() {
        let env = |n: &str| (n == "RPW").then(|| "p@ss".to_string());
        let p = json!({"type": "redis", "host": "h", "port": 7000, "password": "os.environ/RPW"});
        assert_eq!(
            redis_url(p.as_object().unwrap(), &env).unwrap(),
            "redis://:p%40ss@h:7000/"
        );
        let p = json!({"url": "redis://x:1/2"});
        assert_eq!(
            redis_url(p.as_object().unwrap(), &env).unwrap(),
            "redis://x:1/2"
        );
        assert!(
            Cache::from_settings(false, &JsonObject::new(), &env)
                .await
                .unwrap()
                .is_none()
        );
        let p = json!({"type": "local", "supported_call_types": ["aembedding"], "namespace": "ns", "mode": "default_off"});
        let c = Cache::from_settings(true, p.as_object().unwrap(), &env)
            .await
            .unwrap()
            .unwrap();
        assert!(!c.chat && c.embeddings && c.default_off && c.backend() == "local");
        assert_eq!(c.ttl, Some(Duration::from_secs(600)));
        assert!(
            Cache::from_settings(true, json!({"type": "s3"}).as_object().unwrap(), &env)
                .await
                .is_err()
        );
    }
}
