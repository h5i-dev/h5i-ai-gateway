//! The kernel's place in the framework: the `Kernel` impl, the PostgreSQL
//! store, and the in-memory executor. Nothing here decides anything.

// `gateway_tables!` expands to the kernel's `&Vec` signatures.
#![allow(clippy::ptr_arg)]

use gateway_kernel as k;
use h5i_app_core::{Executed, Executor, Kernel, ReplyCodec, TenantId, Timestamp};
use h5i_app_pg::{DbError, Store, Tx, outbox};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// Marker type the framework's traits hang off.
pub struct Gateway;

impl Kernel for Gateway {
    type Principal = k::Principal;
    type Snapshot = k::Snapshot;
    type Command = k::Command;
    type WriteSet = Vec<k::Write>;
    type Reply = k::Reply;
    type Error = k::Error;

    fn tenant(actor: &k::Principal) -> TenantId {
        TenantId(actor.org)
    }

    fn transition(actor: &k::Principal, snap: &k::Snapshot, cmd: &k::Command) -> Result<(Vec<k::Write>, k::Reply), k::Error> {
        k::transition(actor, snap, cmd)
    }

    fn apply(snap: &k::Snapshot, ws: &Vec<k::Write>) -> k::Snapshot {
        k::apply(snap, ws)
    }

    /// The engine's time in the kernel's Unix seconds; budgets, windows and
    /// cooldowns are decided on it.
    fn stamp(actor: &mut k::Principal, now: Timestamp) {
        actor.now = now.secs();
    }

    /// Proven sound in `proofs/ReadOnly.lean`.
    fn read_only(cmd: &k::Command) -> bool {
        k::read_only(cmd)
    }
}

// The kernel's tables, from its `schema!` declaration.
gateway_kernel::gateway_tables!(Gateway);

/// The outbox destination of spend logs.
pub const SPEND_LOGS: u64 = 1;

pub struct GatewayStore;

impl Store<Gateway> for GatewayStore {
    fn ddl() -> Vec<String> {
        schema_ddl()
    }

    fn tables() -> Vec<&'static str> {
        schema_tables()
    }

    async fn load(tx: &Tx<'_>, t: TenantId) -> Result<k::Snapshot, DbError> {
        schema_load(tx, t).await
    }

    // Table writes go through the kernel's `sql_writes` (`proofs/Storage.lean`).
    // Spend logs go to the outbox in the same transaction, so a log exists
    // exactly when the charge it records commits.
    async fn write(tx: &Tx<'_>, t: TenantId, ws: &Vec<k::Write>) -> Result<(), DbError> {
        schema_store(tx, t, ws).await?;
        // One outbox row for all the commit's spend logs, in order.
        let logs: Vec<&k::SpendLog> = ws
            .iter()
            .filter_map(|w| match w {
                k::Write::Emit(log) => Some(log),
                _ => None,
            })
            .collect();
        if !logs.is_empty() {
            outbox::enqueue(tx, t, SPEND_LOGS, &crate::spend::payload(t, logs)).await?;
        }
        Ok(())
    }
}

/// Where spend logs from the in-memory executor go.
pub type SpendSink = Box<dyn Fn(TenantId, &k::SpendLog) + Send + Sync>;

/// Runs commands one at a time in memory, at the system clock, never letting
/// a tenant's time go back (like the engine's `monotonic`). It behaves like
/// h5i-app's `MemoryEngine`, and also hands committed spend logs to a sink.
/// For development and tests: nothing survives a restart.
pub struct MemoryExecutor {
    tenants: Mutex<HashMap<TenantId, (k::Snapshot, Timestamp)>>,
    clock: Box<dyn Fn() -> Timestamp + Send + Sync>,
    sink: SpendSink,
}

impl MemoryExecutor {
    pub fn new(sink: SpendSink) -> Self {
        Self::with_clock(sink, Box::new(Timestamp::now))
    }

    pub fn with_clock(sink: SpendSink, clock: Box<dyn Fn() -> Timestamp + Send + Sync>) -> Self {
        MemoryExecutor { tenants: Mutex::new(HashMap::new()), clock, sink }
    }

    pub fn run(&self, actor: &k::Principal, cmd: &k::Command) -> Result<k::Reply, k::Error> {
        let tenant = Gateway::tenant(actor);
        let mut tenants = self.tenants.lock().unwrap_or_else(|e| e.into_inner());
        let (snap, last) = tenants.entry(tenant).or_default();
        let now = (self.clock)().max(*last);
        let mut actor = *actor;
        Gateway::stamp(&mut actor, now);
        let (ws, reply) = Gateway::transition(&actor, snap, cmd)?;
        *snap = Gateway::apply(snap, &ws);
        *last = now;
        for w in &ws {
            if let k::Write::Emit(log) = w {
                (self.sink)(tenant, log);
            }
        }
        Ok(reply)
    }

    pub fn snapshot(&self, tenant: TenantId) -> k::Snapshot {
        self.tenants.lock().unwrap_or_else(|e| e.into_inner()).get(&tenant).map(|t| t.0.clone()).unwrap_or_default()
    }
}

#[derive(Debug, thiserror::Error)]
#[error("in-memory executor: {0}")]
pub struct MemoryError(String);

impl Executor<Gateway> for MemoryExecutor {
    type Error = MemoryError;

    fn is_idempotency_conflict(_: &MemoryError) -> bool {
        false
    }

    async fn execute(&self, actor: &k::Principal, cmd: &k::Command) -> Executed<Gateway, MemoryError> {
        Ok(self.run(actor, cmd))
    }

    async fn execute_idempotent<C: ReplyCodec<Gateway>>(&self, _: &k::Principal, _: &str, _: &k::Command) -> Executed<Gateway, MemoryError> {
        Err(MemoryError("idempotency keys need the PostgreSQL engine".into()))
    }

    async fn snapshot_for(&self, actor: &k::Principal, _: &k::Command) -> Result<k::Snapshot, MemoryError> {
        Ok(self.snapshot(Gateway::tenant(actor)))
    }
}

/// The engine behind the gateway: PostgreSQL, or memory for development.
pub enum Backend {
    /// PostgreSQL, with admissions and settlements group-committed by the batcher.
    Postgres(Arc<h5i_app_pg::Engine<Gateway, GatewayStore>>, Option<crate::batcher::Batcher>),
    Memory(MemoryExecutor),
}

/// The engine could not run the command (the database is unreachable, say).
/// Distinct from a refusal, which is the kernel's answer.
#[derive(Debug, thiserror::Error)]
#[error("{0}")]
pub struct Unavailable(pub String);

impl Backend {
    /// PostgreSQL; `batch_max > 1` group-commits up to that many admissions
    /// and settlements per transaction.
    pub fn postgres(engine: h5i_app_pg::Engine<Gateway, GatewayStore>, batch_max: usize) -> Self {
        let engine = Arc::new(engine);
        let batcher = (batch_max > 1).then(|| crate::batcher::Batcher::new(engine.clone(), batch_max));
        Backend::Postgres(engine, batcher)
    }

    /// Run a command: the kernel's reply or refusal, or `Unavailable`.
    pub async fn run(&self, actor: &k::Principal, cmd: &k::Command) -> Result<Result<k::Reply, k::Error>, Unavailable> {
        match self {
            Backend::Postgres(e, batcher) => match (batcher, crate::batcher::Batcher::item(actor, cmd)) {
                (Some(b), Some(item)) => b.run(actor.org, item).await,
                _ => e.execute(actor, cmd).await.map_err(|e| Unavailable(e.to_string())),
            },
            Backend::Memory(m) => Ok(m.run(actor, cmd)),
        }
    }
}
