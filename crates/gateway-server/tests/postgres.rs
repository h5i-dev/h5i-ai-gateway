//! The PostgreSQL engine against the in-memory executor (which runs the
//! kernel's `apply`): same replies, same final state, and the outbox holds
//! exactly the committed spend logs. Then concurrent admissions against one
//! budget. Needs H5I_APP_TEST_DATABASE_URL; skips otherwise.

use gateway_kernel as k;
use gateway_server::kernel::{Gateway, GatewayStore, MemoryExecutor};
use gateway_server::spend::{self, SpendFilter, SpendReader};
use h5i_app_core::{TenantId, Timestamp};
use h5i_app_pg::{Clock, Engine, EngineConfig, ManualClock, pool, with_schema};
use std::sync::{Arc, Mutex};

fn rng(state: &mut u64, n: u64) -> u64 {
    *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    (*state >> 33) % n
}

/// Rows in key order; the order of rows in a table means nothing.
fn normalize(mut s: k::Snapshot) -> k::Snapshot {
    s.teams.sort_by_key(|x| x.id);
    s.keys.sort_by_key(|x| x.id);
    s.models.sort_by_key(|x| x.id);
    s.deployments.sort_by_key(|x| x.id);
    s.key_models.sort_by_key(|x| (x.key, x.model));
    s.team_models.sort_by_key(|x| (x.team, x.model));
    s.usage.sort_by_key(|x| (x.scope, x.id));
    s.reservations.sort_by_key(|x| x.id);
    s
}

fn normalize_reply(r: Result<k::Reply, k::Error>) -> Result<k::Reply, k::Error> {
    match r {
        Ok(k::Reply::State(s)) => Ok(k::Reply::State(normalize(s))),
        Ok(k::Reply::Models(mut m)) => {
            m.sort_by_key(|x| x.id);
            Ok(k::Reply::Models(m))
        }
        Ok(k::Reply::KeyInfo { key, mut models, reserved }) => {
            models.sort();
            Ok(k::Reply::KeyInfo { key, models, reserved })
        }
        Ok(k::Reply::TeamInfo { team, mut models, reserved }) => {
            models.sort();
            Ok(k::Reply::TeamInfo { team, models, reserved })
        }
        r => r,
    }
}

fn url() -> Option<String> {
    match std::env::var("H5I_APP_TEST_DATABASE_URL") {
        Ok(u) => Some(u),
        Err(_) => {
            eprintln!("H5I_APP_TEST_DATABASE_URL not set; skipping");
            None
        }
    }
}

fn fresh_org() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos() as u64 % (1 << 50)
}

const NONE_PATCH: k::KeyPatch = k::KeyPatch {
    max_budget: None,
    rpm: None,
    tpm: None,
    max_parallel: None,
    expires_at: None,
    budget_duration: None,
    blocked: None,
    all_models: None,
};

fn random_command(s: &mut u64, master: bool, open: &[u64]) -> k::Command {
    let reservation = |s: &mut u64| if !open.is_empty() && rng(s, 4) != 0 { open[rng(s, open.len() as u64) as usize] } else { rng(s, 40) };
    let names = [b"gpt".to_vec(), b"claude".to_vec(), b"nope".to_vec()];
    let name = |s: &mut u64| names[rng(s, 3) as usize].clone();
    let small = |s: &mut u64| if rng(s, 10) == 0 { k::UNLIMITED } else { rng(s, 400_000) };
    match rng(s, if master { 14 } else { 6 }) {
        0 | 1 => k::Command::Admit {
            model: name(s),
            prompt_tokens: rng(s, 50),
            max_tokens: rng(s, 50),
            exclude: if rng(s, 4) == 0 { vec![100] } else { vec![] },
        },
        2 | 3 => k::Command::Settle {
            reservation: reservation(s),
            prompt_tokens: rng(s, 60),
            completion_tokens: rng(s, 60),
            status: [k::CallStatus::Success, k::CallStatus::Failure, k::CallStatus::Retryable][rng(s, 3) as usize],
        },
        4 => k::Command::Expire { reservation: reservation(s) },
        5 => k::Command::KeyInfo { id: rng(s, 40) },
        6 => k::Command::CreateKey {
            spec: k::KeySpec {
                team: if rng(s, 2) == 0 { 0 } else { rng(s, 40) },
                user: 1,
                max_budget: small(s),
                rpm: if rng(s, 3) == 0 { rng(s, 4) } else { k::UNLIMITED },
                tpm: k::UNLIMITED,
                max_parallel: if rng(s, 3) == 0 { rng(s, 3) } else { k::UNLIMITED },
                expires_at: k::UNLIMITED,
                budget_duration: if rng(s, 3) == 0 { 120 } else { 0 },
                admin: false,
                all_models: rng(s, 2) == 0,
            },
            models: vec![name(s)],
        },
        7 => k::Command::CreateTeam {
            spec: k::TeamSpec { max_budget: small(s), rpm: k::UNLIMITED, tpm: k::UNLIMITED, budget_duration: 0, all_models: rng(s, 2) == 0 },
            models: vec![b"gpt".to_vec()],
        },
        8 => k::Command::UpdateKey { id: rng(s, 40), patch: k::KeyPatch { blocked: Some(rng(s, 4) == 0), max_budget: Some(small(s)), ..NONE_PATCH } },
        9 => k::Command::DeleteKey { id: rng(s, 40) },
        10 => k::Command::DeleteTeam { id: rng(s, 40) },
        11 => k::Command::SetKeyModels { id: rng(s, 40), models: vec![name(s)] },
        12 => k::Command::TeamInfo { id: rng(s, 40) },
        _ => k::Command::Dump,
    }
}

#[tokio::test]
async fn store_agrees_with_apply_and_the_outbox_holds_the_spend_logs() {
    let Some(url) = url() else { return };
    let clock = ManualClock::new(Timestamp::from_secs(1_000));
    let config = EngineConfig { clock: Clock::Manual(clock.clone()), monotonic: true, ..EngineConfig::default() };
    let schema_url = with_schema(&url, "gateway_test").unwrap();
    let pg = Engine::<Gateway, GatewayStore>::new(pool(&schema_url, 4).unwrap(), config);
    pg.install_schema().await.unwrap();
    let logs = Arc::new(Mutex::new(Vec::<k::SpendLog>::new()));
    let sink = logs.clone();
    let c2 = clock.clone();
    let mem = MemoryExecutor::with_clock(Box::new(move |_, l| sink.lock().unwrap().push(*l)), Box::new(move || c2.get()));
    let org = fresh_org();
    let master = k::Principal { org, key: 0, master: true, now: 0 };

    let setup = [
        k::Command::Configure { allowed_fails: 1, cooldown_secs: 30, reservation_ttl: 60 },
        k::Command::UpsertDeployment {
            model: b"gpt".to_vec(),
            spec: k::DeploymentSpec { id: 100, input_cost: 1_000, output_cost: 2_000, rpm: 50, tpm: k::UNLIMITED, priority: 0, enabled: true },
        },
        k::Command::UpsertDeployment {
            model: b"gpt".to_vec(),
            spec: k::DeploymentSpec { id: 101, input_cost: 3_000, output_cost: 3_000, rpm: k::UNLIMITED, tpm: 10_000, priority: 1, enabled: true },
        },
        k::Command::UpsertDeployment {
            model: b"claude".to_vec(),
            spec: k::DeploymentSpec { id: 200, input_cost: 500, output_cost: 500, rpm: k::UNLIMITED, tpm: k::UNLIMITED, priority: 0, enabled: true },
        },
    ];
    for c in &setup {
        assert_eq!(pg.execute(&master, c).await.unwrap(), mem.run(&master, c));
    }

    let mut s = 11;
    let mut accepted = [0usize; 3];
    let mut open: Vec<u64> = Vec::new();
    for step in 0..1_500 {
        if rng(&mut s, 5) == 0 {
            clock.set(Timestamp::from_secs(clock.get().secs() + rng(&mut s, 40)));
        }
        let is_master = rng(&mut s, 3) == 0;
        let actor = if is_master { master } else { k::Principal { org, key: 1 + rng(&mut s, 40), master: false, now: 0 } };
        let cmd = random_command(&mut s, is_master, &open);
        let got = normalize_reply(pg.execute(&actor, &cmd).await.unwrap());
        let want = normalize_reply(mem.run(&actor, &cmd));
        assert_eq!(got, want, "step {step}: {actor:?} {cmd:?}");
        if let Ok(k::Reply::Admitted { reservation, .. }) = &got {
            open.push(*reservation);
        }
        if got.is_ok() {
            match cmd {
                k::Command::Admit { .. } => accepted[0] += 1,
                k::Command::Settle { .. } => accepted[1] += 1,
                k::Command::CreateKey { .. } => accepted[2] += 1,
                _ => {}
            }
        }
    }
    assert!(accepted.iter().all(|n| *n >= 5), "the run should exercise admits, settles and keys: {accepted:?}");
    let a = normalize(pg.snapshot(TenantId(org)).await.unwrap());
    let b = normalize(mem.snapshot(TenantId(org)));
    assert_eq!(a, b);

    // The outbox holds one spend log per committed settle or expire, in order.
    let (client, conn) = tokio_postgres::connect(&schema_url, tokio_postgres::NoTls).await.unwrap();
    tokio::spawn(conn);
    let rows = client.query("SELECT payload FROM h5i_outbox WHERE tenant_id = $1 ORDER BY id", &[&(org as i64)]).await.unwrap();
    let logs = logs.lock().unwrap().clone();
    // One outbox row per committing command, holding its logs in order.
    let stored: Vec<serde_json::Value> = rows.iter().flat_map(|row| spend::logs_of(row.get::<_, &[u8]>(0))).collect();
    assert_eq!(stored.len(), logs.len());
    for (v, log) in stored.iter().zip(logs.iter()) {
        assert_eq!(v["request_id"], log.reservation.to_string());
        assert_eq!(v["spend_nano_usd"], log.cost);
    }
    assert!(!logs.is_empty());

    // `/spend/logs` filters in SQL exactly as `SpendFilter::matches` does.
    let reader = SpendReader::connect(&schema_url).await.unwrap();
    let all: Vec<serde_json::Value> = logs.iter().rev().map(|l| spend::json(TenantId(org), l)).collect();
    let first = logs[0];
    let mid_time = logs[logs.len() / 2].at;
    let filters = [
        SpendFilter::default(),
        SpendFilter { key: Some(first.key), ..Default::default() },
        SpendFilter { team: Some(first.team), ..Default::default() },
        SpendFilter { model_group: Some(first.model), ..Default::default() },
        SpendFilter { status: Some("failure".into()), ..Default::default() },
        SpendFilter { status: Some("success".into()), key: Some(first.key), ..Default::default() },
        SpendFilter { since: Some(mid_time), ..Default::default() },
        SpendFilter { until: Some(mid_time), model_group: Some(first.model), ..Default::default() },
        SpendFilter { key: Some(u64::MAX >> 1), ..Default::default() },
    ];
    for f in &filters {
        let got: Vec<String> =
            reader.search(TenantId(org), f, 25).await.unwrap().iter().map(|v| v["request_id"].as_str().unwrap().to_string()).collect();
        let want: Vec<String> = all.iter().filter(|v| f.matches(v)).take(25).map(|v| v["request_id"].as_str().unwrap().to_string()).collect();
        assert_eq!(got, want, "{f:?}");
    }
}

#[tokio::test]
async fn concurrent_admissions_never_overcommit_a_budget() {
    let Some(url) = url() else { return };
    let pg = Arc::new(Engine::<Gateway, GatewayStore>::new(
        pool(&with_schema(&url, "gateway_test").unwrap(), 16).unwrap(),
        EngineConfig::default().database_time(),
    ));
    pg.install_schema().await.unwrap();
    let org = fresh_org();
    let master = k::Principal { org, key: 0, master: true, now: 0 };
    let dep = k::DeploymentSpec { id: 1, input_cost: 1_000, output_cost: 1_000, rpm: k::UNLIMITED, tpm: k::UNLIMITED, priority: 0, enabled: true };
    pg.execute(&master, &k::Command::UpsertDeployment { model: b"m".to_vec(), spec: dep }).await.unwrap().unwrap();
    // Each call reserves (10 + 10) * 1000 = 20_000; the budget covers 7 of them.
    let spec = k::KeySpec {
        team: 0,
        user: 1,
        max_budget: 150_000,
        rpm: k::UNLIMITED,
        tpm: k::UNLIMITED,
        max_parallel: k::UNLIMITED,
        expires_at: k::UNLIMITED,
        budget_duration: 0,
        admin: false,
        all_models: true,
    };
    let key = match pg.execute(&master, &k::Command::CreateKey { spec, models: vec![] }).await.unwrap().unwrap() {
        k::Reply::Created(id) => id,
        r => panic!("{r:?}"),
    };
    let actor = k::Principal { org, key, master: false, now: 0 };
    let tasks: Vec<_> = (0..32)
        .map(|_| {
            let pg = pg.clone();
            tokio::spawn(async move {
                let cmd = k::Command::Admit { model: b"m".to_vec(), prompt_tokens: 10, max_tokens: 10, exclude: vec![] };
                pg.execute(&actor, &cmd).await.unwrap()
            })
        })
        .collect();
    let mut admitted = 0;
    for t in tasks {
        match t.await.unwrap() {
            Ok(k::Reply::Admitted { .. }) => admitted += 1,
            Err(k::Error::KeyBudgetExceeded) => {}
            other => panic!("{other:?}"),
        }
    }
    assert_eq!(admitted, 7);
    let s = pg.snapshot(TenantId(org)).await.unwrap();
    assert_eq!(k::reserved_by_key(&s.reservations, key), 140_000);
}

#[tokio::test]
async fn group_commit_answers_like_single_commands_in_fewer_transactions() {
    use gateway_server::kernel::Backend;
    use std::sync::atomic::Ordering;
    let Some(url) = url() else { return };
    let engine =
        Engine::<Gateway, GatewayStore>::new(pool(&with_schema(&url, "gateway_test").unwrap(), 16).unwrap(), EngineConfig::default().database_time());
    engine.install_schema().await.unwrap();
    let backend = Arc::new(Backend::postgres(engine, 256));
    let org = fresh_org();
    let master = k::Principal { org, key: 0, master: true, now: 0 };
    let dep = k::DeploymentSpec { id: 1, input_cost: 1_000, output_cost: 1_000, rpm: k::UNLIMITED, tpm: k::UNLIMITED, priority: 0, enabled: true };
    backend.run(&master, &k::Command::UpsertDeployment { model: b"m".to_vec(), spec: dep }).await.unwrap().unwrap();
    // Each call reserves 20_000; the budget covers 7 of them.
    let spec = k::KeySpec {
        team: 0,
        user: 1,
        max_budget: 150_000,
        rpm: k::UNLIMITED,
        tpm: k::UNLIMITED,
        max_parallel: k::UNLIMITED,
        expires_at: k::UNLIMITED,
        budget_duration: 0,
        admin: false,
        all_models: true,
    };
    let key = match backend.run(&master, &k::Command::CreateKey { spec, models: vec![] }).await.unwrap().unwrap() {
        k::Reply::Created(id) => id,
        r => panic!("{r:?}"),
    };
    let actor = k::Principal { org, key, master: false, now: 0 };
    let Backend::Postgres(engine, _) = &*backend else { unreachable!() };
    let before = engine.stats.commits.load(Ordering::Relaxed);
    let admits: Vec<_> = (0..64)
        .map(|_| {
            let backend = backend.clone();
            tokio::spawn(async move {
                let cmd = k::Command::Admit { model: b"m".to_vec(), prompt_tokens: 10, max_tokens: 10, exclude: vec![] };
                backend.run(&actor, &cmd).await.unwrap()
            })
        })
        .collect();
    let mut reservations = Vec::new();
    for t in admits {
        match t.await.unwrap() {
            Ok(k::Reply::Admitted { reservation, .. }) => reservations.push(reservation),
            Err(k::Error::KeyBudgetExceeded) => {}
            other => panic!("{other:?}"),
        }
    }
    assert_eq!(reservations.len(), 7);
    let transactions = engine.stats.commits.load(Ordering::Relaxed) - before;
    assert!(transactions < 64, "64 admissions took {transactions} transactions");
    // Settlements batch too, and each charges its own cost once.
    let settles: Vec<_> = reservations
        .iter()
        .map(|&reservation| {
            let backend = backend.clone();
            tokio::spawn(async move {
                let cmd = k::Command::Settle { reservation, prompt_tokens: 10, completion_tokens: 5, status: k::CallStatus::Success };
                backend.run(&actor, &cmd).await.unwrap()
            })
        })
        .collect();
    for t in settles {
        assert_eq!(t.await.unwrap(), Ok(k::Reply::Settled { cost: 15_000 }));
    }
    let s = engine.snapshot(TenantId(org)).await.unwrap();
    assert_eq!(k::find_key(&s.keys, key).unwrap().spend, 7 * 15_000);
    assert!(s.reservations.is_empty());
}

/// A batch item: an admission or a settlement, by a key or the master key.
fn random_item(s: &mut u64, keys: u64, open: &[u64]) -> k::BatchItem {
    let master = rng(s, 8) == 0;
    let key = if master { 0 } else { 1 + rng(s, keys) };
    let op = if open.is_empty() || rng(s, 2) == 0 {
        k::BatchOp::Admit {
            model: [b"gpt".to_vec(), b"claude".to_vec(), b"nope".to_vec()][rng(s, 3) as usize].clone(),
            prompt_tokens: rng(s, 30),
            max_tokens: rng(s, 30),
            exclude: vec![],
        }
    } else {
        k::BatchOp::Settle {
            reservation: open[rng(s, open.len() as u64) as usize],
            prompt_tokens: rng(s, 30),
            completion_tokens: rng(s, 30),
            status: [k::CallStatus::Success, k::CallStatus::Retryable][rng(s, 2) as usize],
        }
    };
    k::BatchItem { key, master, op }
}

/// The PostgreSQL engine loads, for admissions, settlements, expiries, the
/// read commands and batches, only the rows `read_plan` names. In a tenant
/// with many keys and teams it must answer exactly like the in-memory
/// executor, which runs every command on the whole tenant, and reach the
/// same state.
#[tokio::test]
async fn planned_loads_agree_with_whole_snapshots_in_a_large_tenant() {
    let Some(url) = url() else { return };
    let clock = ManualClock::new(Timestamp::from_secs(10_000));
    let config = EngineConfig { clock: Clock::Manual(clock.clone()), monotonic: true, ..EngineConfig::default() };
    // Its own tables: with the other tests' tenants in the same small tables,
    // SERIALIZABLE predicate locks make their commands retry.
    let pg = Engine::<Gateway, GatewayStore>::new(pool(&with_schema(&url, "gateway_plan_test").unwrap(), 4).unwrap(), config);
    pg.install_schema().await.unwrap();
    let c2 = clock.clone();
    let mem = MemoryExecutor::with_clock(Box::new(|_, _| {}), Box::new(move || c2.get()));
    let org = fresh_org();
    let master = k::Principal { org, key: 0, master: true, now: 0 };
    let both = |actor: k::Principal, cmd: k::Command| {
        let (pg, mem) = (&pg, &mem);
        async move {
            let got = normalize_reply(pg.execute(&actor, &cmd).await.unwrap());
            let want = normalize_reply(mem.run(&actor, &cmd));
            assert_eq!(got, want, "{actor:?} {cmd:?}");
            got
        }
    };

    let mut s = 7;
    both(master, k::Command::Configure { allowed_fails: 1, cooldown_secs: 30, reservation_ttl: 60 }).await.unwrap();
    for (id, m, priority, rpm) in [(100, "gpt", 0, 30), (101, "gpt", 1, k::UNLIMITED), (200, "claude", 0, k::UNLIMITED)] {
        let spec = k::DeploymentSpec { id, input_cost: 1_000, output_cost: 2_000, rpm, tpm: k::UNLIMITED, priority, enabled: true };
        both(master, k::Command::UpsertDeployment { model: m.as_bytes().to_vec(), spec }).await.unwrap();
    }
    // 40 teams, then 400 keys, most of them in a team.
    let mut teams = Vec::new();
    for _ in 0..40 {
        let spec = k::TeamSpec { max_budget: 2_000_000, rpm: 40, tpm: k::UNLIMITED, budget_duration: 0, all_models: rng(&mut s, 3) != 0 };
        match both(master, k::Command::CreateTeam { spec, models: vec![b"claude".to_vec()] }).await {
            Ok(k::Reply::Created(id)) => teams.push(id),
            r => panic!("{r:?}"),
        }
    }
    let mut last = 0;
    for i in 0..400 {
        let spec = k::KeySpec {
            team: if rng(&mut s, 4) == 0 { 0 } else { teams[rng(&mut s, teams.len() as u64) as usize] },
            user: 1,
            max_budget: if rng(&mut s, 3) == 0 { 300_000 } else { k::UNLIMITED },
            rpm: if rng(&mut s, 4) == 0 { 3 } else { k::UNLIMITED },
            tpm: k::UNLIMITED,
            max_parallel: if rng(&mut s, 4) == 0 { 2 } else { k::UNLIMITED },
            expires_at: k::UNLIMITED,
            budget_duration: if rng(&mut s, 5) == 0 { 120 } else { 0 },
            admin: i % 97 == 5,
            all_models: rng(&mut s, 2) == 0,
        };
        match both(master, k::Command::CreateKey { spec, models: vec![b"gpt".to_vec()] }).await {
            Ok(k::Reply::Created(id)) => last = id,
            r => panic!("{r:?}"),
        }
    }
    // Ids above the last key name no key, or a team or reservation.
    let top = last + 5;

    let mut open: Vec<u64> = Vec::new();
    let mut accepted = [0usize; 4];
    for _ in 0..1_200 {
        if rng(&mut s, 6) == 0 {
            clock.set(Timestamp::from_secs(clock.get().secs() + rng(&mut s, 30)));
        }
        let actor = if rng(&mut s, 6) == 0 { master } else { k::Principal { org, key: 1 + rng(&mut s, top), master: false, now: 0 } };
        let any_res = |s: &mut u64| if !open.is_empty() && rng(s, 5) != 0 { open[rng(s, open.len() as u64) as usize] } else { rng(s, 2 * top) };
        let (actor, cmd) = match rng(&mut s, 20) {
            0..=5 => (
                actor,
                k::Command::Admit {
                    model: [b"gpt".to_vec(), b"claude".to_vec(), b"nope".to_vec()][rng(&mut s, 3) as usize].clone(),
                    prompt_tokens: rng(&mut s, 40),
                    max_tokens: rng(&mut s, 40),
                    exclude: if rng(&mut s, 5) == 0 { vec![100] } else { vec![] },
                },
            ),
            6..=8 => (
                actor,
                k::Command::Settle {
                    reservation: any_res(&mut s),
                    prompt_tokens: rng(&mut s, 50),
                    completion_tokens: rng(&mut s, 50),
                    status: [k::CallStatus::Success, k::CallStatus::Failure, k::CallStatus::Retryable][rng(&mut s, 3) as usize],
                },
            ),
            9 => (actor, k::Command::Expire { reservation: any_res(&mut s) }),
            10 => (actor, k::Command::KeyInfo { id: 1 + rng(&mut s, top) }),
            11 => {
                let id = if rng(&mut s, 2) == 0 { 1 + rng(&mut s, top) } else { teams[rng(&mut s, teams.len() as u64) as usize] };
                (actor, k::Command::TeamInfo { id })
            }
            12 => (actor, k::Command::ListModels),
            // Batches run as the master key; their items settle open
            // reservations and ones admitted earlier in the same batch.
            13..=16 => {
                let next = mem.snapshot(TenantId(org)).settings.next_id;
                let mut targets = open.clone();
                let mut items = Vec::new();
                for _ in 0..1 + rng(&mut s, 40) {
                    let it = random_item(&mut s, top, &targets);
                    if let k::BatchOp::Admit { .. } = it.op {
                        // The id this admission gets if it and the ones before it succeed.
                        targets.push(next + 1 + items.iter().filter(|i: &&k::BatchItem| matches!(i.op, k::BatchOp::Admit { .. })).count() as u64);
                    }
                    items.push(it);
                }
                (master, k::Command::Batch { items })
            }
            17 => {
                let patch = k::KeyPatch { blocked: Some(rng(&mut s, 3) == 0), max_budget: Some(rng(&mut s, 2_000_000)), ..NONE_PATCH };
                (master, k::Command::UpdateKey { id: 1 + rng(&mut s, top), patch })
            }
            18 => (master, k::Command::DeleteKey { id: 1 + rng(&mut s, top) }),
            _ => {
                let models = vec![[b"gpt".to_vec(), b"claude".to_vec()][rng(&mut s, 2) as usize].clone()];
                (master, k::Command::SetKeyModels { id: 1 + rng(&mut s, top), models })
            }
        };
        match (&cmd, both(actor, cmd.clone()).await) {
            (k::Command::Admit { .. }, Ok(k::Reply::Admitted { reservation, .. })) => {
                open.push(reservation);
                accepted[0] += 1;
            }
            (k::Command::Settle { .. }, Ok(_)) => accepted[1] += 1,
            (k::Command::KeyInfo { .. } | k::Command::TeamInfo { .. }, Ok(_)) => accepted[2] += 1,
            (k::Command::Batch { .. }, Ok(k::Reply::Batch(outs))) => {
                for o in outs {
                    if let k::ItemOutcome::Admitted { reservation, .. } = o {
                        open.push(reservation);
                        accepted[3] += 1;
                    }
                }
            }
            _ => {}
        }
    }
    assert!(accepted.iter().all(|n| *n >= 10), "the run should exercise admits, settles, reads and batches: {accepted:?}");
    assert_eq!(normalize(pg.snapshot(TenantId(org)).await.unwrap()), normalize(mem.snapshot(TenantId(org))));
}
