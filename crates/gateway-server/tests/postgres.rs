//! The PostgreSQL engine against the in-memory executor (which runs the
//! kernel's `apply`): same replies, same final state, and the outbox holds
//! exactly the committed spend logs. Then concurrent admissions against one
//! budget. Needs H5I_APP_TEST_DATABASE_URL; skips otherwise.

use gateway_kernel as k;
use gateway_server::kernel::{Gateway, GatewayStore, MemoryExecutor};
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

const NONE_PATCH: k::KeyPatch =
    k::KeyPatch { max_budget: None, rpm: None, tpm: None, max_parallel: None, expires_at: None, budget_duration: None, blocked: None, all_models: None };

fn random_command(s: &mut u64, master: bool, open: &[u64]) -> k::Command {
    let reservation = |s: &mut u64| if !open.is_empty() && rng(s, 4) != 0 { open[rng(s, open.len() as u64) as usize] } else { rng(s, 40) };
    let names = [b"gpt".to_vec(), b"claude".to_vec(), b"nope".to_vec()];
    let name = |s: &mut u64| names[rng(s, 3) as usize].clone();
    let small = |s: &mut u64| if rng(s, 10) == 0 { k::UNLIMITED } else { rng(s, 400_000) };
    match rng(s, if master { 14 } else { 6 }) {
        0 | 1 => k::Command::Admit { model: name(s), prompt_tokens: rng(s, 50), max_tokens: rng(s, 50), exclude: if rng(s, 4) == 0 { vec![100] } else { vec![] } },
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
    let logs = logs.lock().unwrap();
    assert_eq!(rows.len(), logs.len());
    for (row, log) in rows.iter().zip(logs.iter()) {
        let v: serde_json::Value = serde_json::from_slice(row.get::<_, &[u8]>(0)).unwrap();
        assert_eq!(v["request_id"], log.reservation.to_string());
        assert_eq!(v["spend_nano_usd"], log.cost);
    }
    assert!(!logs.is_empty());
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
