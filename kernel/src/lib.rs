//! The verified control plane of h5i-ai-gateway, a Rust port of the LiteLLM
//! proxy.
//!
//! Every decision the gateway makes about a request is made here: whether a
//! virtual key may call a model, whether its key and team are within their
//! budgets and rate limits, which deployment serves the call, and what the
//! call cost once the provider answered. The HTTP shell around it talks to the
//! providers and decides nothing.
//!
//! A completion is two commands. `Admit` checks the policy, picks a
//! deployment and reserves the call's worst-case cost against the key's and
//! the team's budgets. The shell then calls the provider, outside any
//! transaction, and `Settle` replaces the reservation with the actual cost of
//! the tokens the provider reported, and emits a spend log through the
//! outbox. `Expire` releases a reservation whose call never settled.
//!
//! The kernel is written in the Rust subset Aeneas translates to Lean (no
//! `?`, no `String`, no iterators, `while` loops over indices). The proofs in
//! `proofs/` are about this code.
//!
//! Money is in nano-dollars (1e-9 USD) and prices are nano-dollars per token,
//! so $2.50 per million tokens is 2500. A limit of `UNLIMITED` (`u64::MAX`)
//! never refuses. Times are Unix seconds, from the engine's clock.

// The Aeneas subset: `&Vec` parameters, index loops, explicit matches.
#![allow(clippy::ptr_arg, clippy::needless_range_loop, clippy::manual_map, clippy::question_mark, clippy::single_match, clippy::collapsible_if, clippy::collapsible_else_if, clippy::needless_return, clippy::collapsible_match, clippy::vec_init_then_push, clippy::match_like_matches_macro)]

/// Who is calling. The shell builds it from a verified credential and the
/// engine stamps `now`; no field comes from the request body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Principal {
    /// The tenant: every row the kernel sees belongs to it.
    pub org: u64,
    /// The virtual key the request authenticated with (0 for the master key).
    pub key: u64,
    /// Authenticated with the operator's master key.
    pub master: bool,
    /// Unix seconds, from the engine's clock.
    pub now: u64,
}

/// A limit that never refuses.
pub const UNLIMITED: u64 = u64::MAX;

/// Rate limits count requests and tokens in fixed windows of this many seconds.
pub const WINDOW: u64 = 60;

/// `Usage::scope` of a key's, a team's and a deployment's counters.
pub const SCOPE_KEY: u64 = 0;
pub const SCOPE_TEAM: u64 = 1;
pub const SCOPE_DEPLOYMENT: u64 = 2;

h5i_app_schema::schema! {
    mapping gateway_tables for gateway_kernel, writes Write, lean "../proofs/generated/Schema.lean";

    /// One tenant's state.
    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct Snapshot {
        settings: Settings,
        teams: Vec<Team>,
        keys: Vec<Key>,
        models: Vec<Model>,
        deployments: Vec<Deployment>,
        key_models: Vec<KeyModel>,
        team_models: Vec<TeamModel>,
        usage: Vec<Usage>,
        reservations: Vec<Reservation>,
    }

    /// Router settings and the id counter. Ids of teams, keys, models and
    /// reservations are `next_id` after the increment, so 0 is never an id.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
    pub struct Settings in "settings" {
        key {}
        next_id: u64,
        /// Retryable failures a deployment may have in one window before it
        /// cools down (LiteLLM's `allowed_fails`).
        allowed_fails: u64,
        /// How long a deployment cools down (LiteLLM's `cooldown_time`).
        cooldown_secs: u64,
        /// After this long an unsettled reservation may be expired.
        reservation_ttl: u64,
    }

    /// A team: a budget and rate limits shared by its keys.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Team in "teams" {
        key { id: u64 }
        max_budget: u64,
        spend: u64,
        rpm: u64,
        tpm: u64,
        /// 0: the budget never resets. Otherwise the spend returns to 0 at
        /// `budget_reset_at`, which then moves this far ahead.
        budget_duration: u64,
        budget_reset_at: u64,
        blocked: bool,
        /// Every model, rather than the ones in `team_models`.
        all_models: bool,
    }

    /// A virtual key (LiteLLM's `sk-...`).
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Key in "keys" {
        key { id: u64 }
        /// 0: no team.
        team: u64,
        /// The user the key was issued to; informational.
        user: u64,
        max_budget: u64,
        spend: u64,
        rpm: u64,
        tpm: u64,
        /// Unsettled calls the key may have at once (LiteLLM's `max_parallel_requests`).
        max_parallel: u64,
        /// The key stops working at this time; `UNLIMITED` never.
        expires_at: u64,
        budget_duration: u64,
        budget_reset_at: u64,
        blocked: bool,
        /// May manage the gateway, like the master key (LiteLLM's proxy admin).
        admin: bool,
        all_models: bool,
    }

    /// A model group: the name clients ask for, served by deployments.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Model in "models" {
        key { id: u64 }
        name: Vec<u8>,
    }

    /// One upstream that serves a model group. Its credentials and endpoint
    /// live in the operator's configuration, under the same id.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Deployment in "deployments" {
        key { id: u64 }
        model: u64,
        input_cost: u64,
        output_cost: u64,
        rpm: u64,
        tpm: u64,
        /// Lower is tried first (LiteLLM's `order`).
        priority: u64,
        enabled: bool,
        /// Retryable failures in the window `fail_window`.
        fails: u64,
        fail_window: u64,
        /// Not routed to before this time.
        cooldown_until: u64,
    }

    /// Key `key` may call model `model`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct KeyModel in "key_models" {
        key { key: u64, model: u64 }
    }

    /// Team `team` may call model `model`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct TeamModel in "team_models" {
        key { team: u64, model: u64 }
    }

    /// Requests and tokens of one key, team or deployment in window `window`
    /// (Unix seconds / `WINDOW`).
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Usage in "usage" {
        key { scope: u64, id: u64 }
        window: u64,
        requests: u64,
        tokens: u64,
    }

    /// The worst-case cost of an admitted call, held against the key's and
    /// the team's budgets until the call settles. Prices are copied from the
    /// deployment, so the call is charged what was quoted at admission.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Reservation in "reservations" {
        key { id: u64 }
        key_id: u64,
        team: u64,
        deployment: u64,
        model: u64,
        input_cost: u64,
        output_cost: u64,
        amount: u64,
        created_at: u64,
    }
}

/// How a call to a provider ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallStatus {
    Success,
    /// The provider refused the request itself (a bad request, say); the
    /// deployment is healthy.
    Failure,
    /// The deployment failed (a timeout, a 5xx, a 429); counts towards its cooldown.
    Retryable,
    /// Never settled; released by `Expire`.
    Expired,
}

/// A spend log, sent through the outbox when a reservation is settled or
/// expired (LiteLLM's `LiteLLM_SpendLogs` row).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpendLog {
    pub reservation: u64,
    pub key: u64,
    pub team: u64,
    pub deployment: u64,
    pub model: u64,
    pub prompt_tokens: u64,
    pub completion_tokens: u64,
    pub cost: u64,
    pub at: u64,
    pub status: CallStatus,
}

/// Optional changes to a key; `None` keeps the field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KeyPatch {
    pub max_budget: Option<u64>,
    pub rpm: Option<u64>,
    pub tpm: Option<u64>,
    pub max_parallel: Option<u64>,
    pub expires_at: Option<u64>,
    pub budget_duration: Option<u64>,
    pub blocked: Option<bool>,
    pub all_models: Option<bool>,
}

/// Optional changes to a team; `None` keeps the field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TeamPatch {
    pub max_budget: Option<u64>,
    pub rpm: Option<u64>,
    pub tpm: Option<u64>,
    pub budget_duration: Option<u64>,
    pub blocked: Option<bool>,
    pub all_models: Option<bool>,
}

/// The limits of a new key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KeySpec {
    pub team: u64,
    pub user: u64,
    pub max_budget: u64,
    pub rpm: u64,
    pub tpm: u64,
    pub max_parallel: u64,
    pub expires_at: u64,
    pub budget_duration: u64,
    pub admin: bool,
    pub all_models: bool,
}

/// The limits of a new team.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TeamSpec {
    pub max_budget: u64,
    pub rpm: u64,
    pub tpm: u64,
    pub budget_duration: u64,
    pub all_models: bool,
}

/// A deployment as the operator configures it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeploymentSpec {
    pub id: u64,
    pub input_cost: u64,
    pub output_cost: u64,
    pub rpm: u64,
    pub tpm: u64,
    pub priority: u64,
    pub enabled: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    // The master key or an admin key.
    Configure { allowed_fails: u64, cooldown_secs: u64, reservation_ttl: u64 },
    CreateTeam { spec: TeamSpec, models: Vec<Vec<u8>> },
    UpdateTeam { id: u64, patch: TeamPatch },
    /// Refused while a key belongs to the team.
    DeleteTeam { id: u64 },
    SetTeamModels { id: u64, models: Vec<Vec<u8>> },
    CreateKey { spec: KeySpec, models: Vec<Vec<u8>> },
    UpdateKey { id: u64, patch: KeyPatch },
    DeleteKey { id: u64 },
    SetKeyModels { id: u64, models: Vec<Vec<u8>> },
    /// Set the key's spend back to 0.
    ResetKeySpend { id: u64 },
    /// Create or replace deployment `spec.id` of the model named `model`,
    /// creating the model group if needed. Keeps its health.
    UpsertDeployment { model: Vec<u8>, spec: DeploymentSpec },
    DeleteDeployment { id: u64 },
    /// Every row of the tenant.
    Dump,

    // Any valid key.
    /// Reserve a call of up to `prompt_tokens` + `max_tokens` tokens to the
    /// model named `model`, on a deployment not in `exclude` (those already
    /// tried for this request).
    Admit { model: Vec<u8>, prompt_tokens: u64, max_tokens: u64, exclude: Vec<u64> },
    /// The provider answered (or failed) the call of `reservation`.
    Settle { reservation: u64, prompt_tokens: u64, completion_tokens: u64, status: CallStatus },
    /// Release a reservation older than the reservation TTL.
    Expire { reservation: u64 },
    /// A key: itself, or any key for an admin.
    KeyInfo { id: u64 },
    /// A team: one's own, or any team for an admin.
    TeamInfo { id: u64 },
    /// The models the caller may call.
    ListModels,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Write {
    SetSettings(Settings),
    PutTeam(Team),
    DelTeam(u64),
    PutKey(Key),
    DelKey(u64),
    PutModel(Model),
    PutDeployment(Deployment),
    DelDeployment(u64),
    PutKeyModel(KeyModel),
    DelKeyModel(u64, u64),
    PutTeamModel(TeamModel),
    DelTeamModel(u64, u64),
    PutUsage(Usage),
    PutReservation(Reservation),
    DelReservation(u64),
    /// A spend log for the outbox; changes no table.
    Emit(SpendLog),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reply {
    Created(u64),
    Done,
    /// Call deployment `deployment`, then settle reservation `reservation`.
    Admitted { reservation: u64, deployment: u64, amount: u64 },
    Settled { cost: u64 },
    KeyInfo { key: Key, models: Vec<u64>, reserved: u64 },
    TeamInfo { team: Team, models: Vec<u64>, reserved: u64 },
    Models(Vec<Model>),
    State(Snapshot),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not exist (any more).
    Unauthorized,
    Forbidden,
    NotFound,
    KeyBlocked,
    KeyExpired,
    TeamBlocked,
    ModelNotFound,
    ModelNotAllowed,
    KeyRateLimited,
    TeamRateLimited,
    KeyParallelLimit,
    KeyBudgetExceeded,
    TeamBudgetExceeded,
    /// No deployment of the model is enabled, cool, untried and under its limits.
    NoDeployment,
    NotExpired,
    InUse,
    Overflow,
}

type Outcome = Result<(Vec<Write>, Reply), Error>;

// ---------------------------------------------------------------------------
// Arithmetic

/// `a + b`, or `u64::MAX` if it does not fit.
pub fn sat_add(a: u64, b: u64) -> u64 {
    if a > u64::MAX - b { u64::MAX } else { a + b }
}

/// `a * b`, or `u64::MAX` if it does not fit.
pub fn sat_mul(a: u64, b: u64) -> u64 {
    if b != 0 && a > u64::MAX / b { u64::MAX } else { a * b }
}

/// What a call costs: prompt tokens at the input price plus completion
/// tokens at the output price, capped at `u64::MAX`.
pub fn cost(input_cost: u64, output_cost: u64, prompt_tokens: u64, completion_tokens: u64) -> u64 {
    sat_add(sat_mul(prompt_tokens, input_cost), sat_mul(completion_tokens, output_cost))
}

/// `spend + reserved + amount` stays within `max_budget`. With
/// `max_budget = UNLIMITED` this always holds.
pub fn within_budget(spend: u64, reserved: u64, amount: u64, max_budget: u64) -> bool {
    sat_add(sat_add(spend, reserved), amount) <= max_budget
}

/// The rate-limit window of a time.
pub fn window_of(now: u64) -> u64 {
    now / WINDOW
}

// ---------------------------------------------------------------------------
// Lookups

pub fn bytes_eq(a: &Vec<u8>, b: &Vec<u8>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

pub fn contains(v: &Vec<u64>, x: u64) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

pub fn find_team(v: &Vec<Team>, id: u64) -> Option<Team> {
    let mut i = 0;
    while i < v.len() {
        if v[i].id == id {
            return Some(v[i]);
        }
        i += 1;
    }
    None
}

pub fn find_key(v: &Vec<Key>, id: u64) -> Option<Key> {
    let mut i = 0;
    while i < v.len() {
        if v[i].id == id {
            return Some(v[i]);
        }
        i += 1;
    }
    None
}

pub fn find_deployment(v: &Vec<Deployment>, id: u64) -> Option<Deployment> {
    let mut i = 0;
    while i < v.len() {
        if v[i].id == id {
            return Some(v[i]);
        }
        i += 1;
    }
    None
}

pub fn find_reservation(v: &Vec<Reservation>, id: u64) -> Option<Reservation> {
    let mut i = 0;
    while i < v.len() {
        if v[i].id == id {
            return Some(v[i]);
        }
        i += 1;
    }
    None
}

/// The id of the model named `name`.
pub fn find_model(v: &Vec<Model>, name: &Vec<u8>) -> Option<u64> {
    let mut i = 0;
    while i < v.len() {
        if bytes_eq(&v[i].name, name) {
            return Some(v[i].id);
        }
        i += 1;
    }
    None
}

pub fn find_usage(v: &Vec<Usage>, scope: u64, id: u64) -> Option<Usage> {
    let mut i = 0;
    while i < v.len() {
        if v[i].scope == scope && v[i].id == id {
            return Some(v[i]);
        }
        i += 1;
    }
    None
}

pub fn key_may(v: &Vec<KeyModel>, key: u64, model: u64) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i].key == key && v[i].model == model {
            return true;
        }
        i += 1;
    }
    false
}

pub fn team_may(v: &Vec<TeamModel>, team: u64, model: u64) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i].team == team && v[i].model == model {
            return true;
        }
        i += 1;
    }
    false
}

/// The models key `key` is granted one by one.
pub fn models_of_key(v: &Vec<KeyModel>, key: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < v.len() {
        if v[i].key == key {
            out.push(v[i].model);
        }
        i += 1;
    }
    out
}

/// The models team `team` is granted one by one.
pub fn models_of_team(v: &Vec<TeamModel>, team: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < v.len() {
        if v[i].team == team {
            out.push(v[i].model);
        }
        i += 1;
    }
    out
}

/// Whether some key belongs to team `team`.
pub fn team_in_use(v: &Vec<Key>, team: u64) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i].team == team {
            return true;
        }
        i += 1;
    }
    false
}

/// The ids of the models named in `names`, or `ModelNotFound`.
pub fn resolve_models(v: &Vec<Model>, names: &Vec<Vec<u8>>) -> Result<Vec<u64>, Error> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < names.len() {
        match find_model(v, &names[i]) {
            Some(id) => out.push(id),
            None => return Err(Error::ModelNotFound),
        }
        i += 1;
    }
    Ok(out)
}

/// The number of key `key`'s unsettled calls.
pub fn in_flight(v: &Vec<Reservation>, key: u64) -> u64 {
    let mut n = 0;
    let mut i = 0;
    while i < v.len() {
        if v[i].key_id == key {
            n = sat_add(n, 1);
        }
        i += 1;
    }
    n
}

/// The amount reserved by key `key`'s unsettled calls (capped at `u64::MAX`).
pub fn reserved_by_key(v: &Vec<Reservation>, key: u64) -> u64 {
    let mut total = 0;
    let mut i = 0;
    while i < v.len() {
        if v[i].key_id == key {
            total = sat_add(total, v[i].amount);
        }
        i += 1;
    }
    total
}

/// The amount reserved by team `team`'s unsettled calls (capped at `u64::MAX`).
pub fn reserved_by_team(v: &Vec<Reservation>, team: u64) -> u64 {
    let mut total = 0;
    let mut i = 0;
    while i < v.len() {
        if v[i].team == team {
            total = sat_add(total, v[i].amount);
        }
        i += 1;
    }
    total
}

// ---------------------------------------------------------------------------
// Rate-limit windows

/// Requests and tokens counted for `(scope, id)` in window `w` so far.
pub fn used(v: &Vec<Usage>, scope: u64, id: u64, w: u64) -> (u64, u64) {
    match find_usage(v, scope, id) {
        Some(u) => {
            if u.window == w { (u.requests, u.tokens) } else { (0, 0) }
        }
        None => (0, 0),
    }
}

/// The counters of `(scope, id)` in window `w` after one more request.
pub fn count_request(v: &Vec<Usage>, scope: u64, id: u64, w: u64) -> Usage {
    let (r, t) = used(v, scope, id, w);
    Usage { scope, id, window: w, requests: sat_add(r, 1), tokens: t }
}

/// The counters of `(scope, id)` in window `w` after `n` more tokens.
pub fn count_tokens(v: &Vec<Usage>, scope: u64, id: u64, w: u64, n: u64) -> Usage {
    let (r, t) = used(v, scope, id, w);
    Usage { scope, id, window: w, requests: r, tokens: sat_add(t, n) }
}

/// Requests and tokens both under their limits.
pub fn under_limits(requests: u64, tokens: u64, rpm: u64, tpm: u64) -> bool {
    requests < rpm && tokens < tpm
}

// ---------------------------------------------------------------------------
// Budget periods

/// The key at time `now`: a budget period that ended starts again with no spend.
pub fn key_now(k: Key, now: u64) -> Key {
    if k.budget_duration != 0 && now >= k.budget_reset_at {
        let mut k2 = k;
        k2.spend = 0;
        k2.budget_reset_at = sat_add(now, k.budget_duration);
        k2
    } else {
        k
    }
}

/// The team at time `now`, as `key_now`.
pub fn team_now(t: Team, now: u64) -> Team {
    if t.budget_duration != 0 && now >= t.budget_reset_at {
        let mut t2 = t;
        t2.spend = 0;
        t2.budget_reset_at = sat_add(now, t.budget_duration);
        t2
    } else {
        t
    }
}

// ---------------------------------------------------------------------------
// Routing

/// Deployment `d` may serve a call to `model` at `now`: it serves the model,
/// is enabled, is not cooling down, has not been tried for this request, and
/// is under its own rate limits.
pub fn eligible(d: &Deployment, usage: &Vec<Usage>, model: u64, now: u64, exclude: &Vec<u64>) -> bool {
    if d.model != model || !d.enabled || now < d.cooldown_until || contains(exclude, d.id) {
        return false;
    }
    let (r, t) = used(usage, SCOPE_DEPLOYMENT, d.id, window_of(now));
    under_limits(r, t, d.rpm, d.tpm)
}

/// The order in which deployments are preferred: lower priority first, then
/// fewer requests in the current window (least busy), then lower id.
pub fn before(p1: u64, l1: u64, id1: u64, p2: u64, l2: u64, id2: u64) -> bool {
    p1 < p2 || (p1 == p2 && (l1 < l2 || (l1 == l2 && id1 < id2)))
}

/// The eligible deployment that comes first in `before`'s order, if any.
pub fn route(deps: &Vec<Deployment>, usage: &Vec<Usage>, model: u64, now: u64, exclude: &Vec<u64>) -> Option<Deployment> {
    let w = window_of(now);
    let mut best: Option<Deployment> = None;
    let mut best_load = 0;
    let mut i = 0;
    while i < deps.len() {
        let d = deps[i];
        if eligible(&d, usage, model, now, exclude) {
            let (load, _) = used(usage, SCOPE_DEPLOYMENT, d.id, w);
            match best {
                None => {
                    best = Some(d);
                    best_load = load;
                }
                Some(b) => {
                    if before(d.priority, load, d.id, b.priority, best_load, b.id) {
                        best = Some(d);
                        best_load = load;
                    }
                }
            }
        }
        i += 1;
    }
    best
}

/// Deployment `d` after one more retryable failure at `now`: past
/// `allowed_fails` failures in one window, it cools down for `cooldown_secs`.
pub fn record_failure(d: Deployment, allowed_fails: u64, cooldown_secs: u64, now: u64) -> Deployment {
    let w = window_of(now);
    let fails = if d.fail_window == w { sat_add(d.fails, 1) } else { 1 };
    let mut d2 = d;
    d2.fail_window = w;
    if fails > allowed_fails {
        d2.fails = 0;
        d2.cooldown_until = sat_add(now, cooldown_secs);
    } else {
        d2.fails = fails;
    }
    d2
}

// ---------------------------------------------------------------------------
// Who may do what

/// The master key, or an admin key that is neither blocked nor expired.
pub fn is_admin(a: &Principal, s: &Snapshot) -> bool {
    if a.master {
        return true;
    }
    match find_key(&s.keys, a.key) {
        Some(k) => k.admin && !k.blocked && a.now < k.expires_at,
        None => false,
    }
}

/// Key `k` (of team `t`, if any) may call model `model`.
pub fn may_call(s: &Snapshot, k: &Key, t: &Option<Team>, model: u64) -> bool {
    if !k.all_models {
        if !key_may(&s.key_models, k.id, model) {
            return false;
        }
    }
    match *t {
        Some(team) => {
            if team.all_models {
                true
            } else {
                team_may(&s.team_models, team.id, model)
            }
        }
        None => true,
    }
}

/// The next id, or `Overflow` once the counter is exhausted.
pub fn fresh(s: &Snapshot) -> Result<u64, Error> {
    if s.settings.next_id == u64::MAX { Err(Error::Overflow) } else { Ok(s.settings.next_id + 1) }
}

fn with_next_id(st: Settings, id: u64) -> Settings {
    Settings { next_id: id, allowed_fails: st.allowed_fails, cooldown_secs: st.cooldown_secs, reservation_ttl: st.reservation_ttl }
}

fn one(w: Write) -> Vec<Write> {
    let mut ws = Vec::new();
    ws.push(w);
    ws
}

// ---------------------------------------------------------------------------
// Admission and settlement

/// Admit a call by the master key: no key or team limits, only routing.
fn admit_master(a: &Principal, s: &Snapshot, model: u64, prompt_tokens: u64, max_tokens: u64, exclude: &Vec<u64>) -> Outcome {
    let d = match route(&s.deployments, &s.usage, model, a.now, exclude) {
        None => return Err(Error::NoDeployment),
        Some(d) => d,
    };
    let amount = cost(d.input_cost, d.output_cost, prompt_tokens, max_tokens);
    let id = match fresh(s) {
        Err(e) => return Err(e),
        Ok(id) => id,
    };
    let w = window_of(a.now);
    let r = Reservation {
        id,
        key_id: 0,
        team: 0,
        deployment: d.id,
        model,
        input_cost: d.input_cost,
        output_cost: d.output_cost,
        amount,
        created_at: a.now,
    };
    let mut ws = Vec::new();
    ws.push(Write::PutUsage(count_request(&s.usage, SCOPE_DEPLOYMENT, d.id, w)));
    ws.push(Write::PutReservation(r));
    ws.push(Write::SetSettings(with_next_id(s.settings, id)));
    Ok((ws, Reply::Admitted { reservation: id, deployment: d.id, amount }))
}

/// Admit a call by a virtual key: the key and its team must be active, allowed
/// the model, under their rate limits, and able to cover the call's worst-case
/// cost on top of what they spent and reserved.
fn admit_key(a: &Principal, s: &Snapshot, model: u64, prompt_tokens: u64, max_tokens: u64, exclude: &Vec<u64>) -> Outcome {
    let now = a.now;
    let w = window_of(now);
    let k = match find_key(&s.keys, a.key) {
        None => return Err(Error::Unauthorized),
        Some(k) => k,
    };
    if k.blocked {
        return Err(Error::KeyBlocked);
    }
    if now >= k.expires_at {
        return Err(Error::KeyExpired);
    }
    let team = if k.team == 0 {
        None
    } else {
        match find_team(&s.teams, k.team) {
            None => return Err(Error::NotFound),
            Some(t) => {
                if t.blocked {
                    return Err(Error::TeamBlocked);
                }
                Some(t)
            }
        }
    };
    if !may_call(s, &k, &team, model) {
        return Err(Error::ModelNotAllowed);
    }
    let (kr, kt) = used(&s.usage, SCOPE_KEY, k.id, w);
    if !under_limits(kr, kt, k.rpm, k.tpm) {
        return Err(Error::KeyRateLimited);
    }
    if in_flight(&s.reservations, k.id) >= k.max_parallel {
        return Err(Error::KeyParallelLimit);
    }
    match team {
        Some(t) => {
            let (tr, tt) = used(&s.usage, SCOPE_TEAM, t.id, w);
            if !under_limits(tr, tt, t.rpm, t.tpm) {
                return Err(Error::TeamRateLimited);
            }
        }
        None => {}
    }
    let d = match route(&s.deployments, &s.usage, model, now, exclude) {
        None => return Err(Error::NoDeployment),
        Some(d) => d,
    };
    let amount = cost(d.input_cost, d.output_cost, prompt_tokens, max_tokens);
    let k2 = key_now(k, now);
    if !within_budget(k2.spend, reserved_by_key(&s.reservations, k.id), amount, k2.max_budget) {
        return Err(Error::KeyBudgetExceeded);
    }
    let team2 = match team {
        Some(t) => {
            let t2 = team_now(t, now);
            if !within_budget(t2.spend, reserved_by_team(&s.reservations, t.id), amount, t2.max_budget) {
                return Err(Error::TeamBudgetExceeded);
            }
            Some(t2)
        }
        None => None,
    };
    let id = match fresh(s) {
        Err(e) => return Err(e),
        Ok(id) => id,
    };
    let r = Reservation {
        id,
        key_id: k.id,
        team: k.team,
        deployment: d.id,
        model,
        input_cost: d.input_cost,
        output_cost: d.output_cost,
        amount,
        created_at: now,
    };
    let mut ws = Vec::new();
    ws.push(Write::PutKey(k2));
    ws.push(Write::PutUsage(count_request(&s.usage, SCOPE_KEY, k.id, w)));
    match team2 {
        Some(t2) => {
            ws.push(Write::PutTeam(t2));
            ws.push(Write::PutUsage(count_request(&s.usage, SCOPE_TEAM, t2.id, w)));
        }
        None => {}
    }
    ws.push(Write::PutUsage(count_request(&s.usage, SCOPE_DEPLOYMENT, d.id, w)));
    ws.push(Write::PutReservation(r));
    ws.push(Write::SetSettings(with_next_id(s.settings, id)));
    Ok((ws, Reply::Admitted { reservation: id, deployment: d.id, amount }))
}

pub fn admit(a: &Principal, s: &Snapshot, model: &Vec<u8>, prompt_tokens: u64, max_tokens: u64, exclude: &Vec<u64>) -> Outcome {
    let m = match find_model(&s.models, model) {
        None => return Err(Error::ModelNotFound),
        Some(m) => m,
    };
    if a.master {
        admit_master(a, s, m, prompt_tokens, max_tokens, exclude)
    } else {
        admit_key(a, s, m, prompt_tokens, max_tokens, exclude)
    }
}

/// The caller may settle or expire reservation `r`: it is the key that made
/// it, or an admin.
pub fn may_close(a: &Principal, s: &Snapshot, r: &Reservation) -> bool {
    (!a.master && r.key_id == a.key) || is_admin(a, s)
}

/// Replace reservation `id` with the cost of the tokens the provider
/// reported, at the prices quoted at admission. Charges the key and the team,
/// counts the tokens, records a retryable failure against the deployment,
/// and logs the spend.
pub fn settle(a: &Principal, s: &Snapshot, id: u64, prompt_tokens: u64, completion_tokens: u64, status: CallStatus) -> Outcome {
    let r = match find_reservation(&s.reservations, id) {
        None => return Err(Error::NotFound),
        Some(r) => r,
    };
    if !may_close(a, s, &r) {
        return Err(Error::Forbidden);
    }
    let now = a.now;
    let w = window_of(now);
    let c = cost(r.input_cost, r.output_cost, prompt_tokens, completion_tokens);
    let tokens = sat_add(prompt_tokens, completion_tokens);
    let mut ws = Vec::new();
    ws.push(Write::DelReservation(id));
    if r.key_id != 0 {
        match find_key(&s.keys, r.key_id) {
            Some(k) => {
                let mut k2 = key_now(k, now);
                k2.spend = sat_add(k2.spend, c);
                ws.push(Write::PutKey(k2));
                ws.push(Write::PutUsage(count_tokens(&s.usage, SCOPE_KEY, k.id, w, tokens)));
            }
            None => {}
        }
    }
    if r.team != 0 {
        match find_team(&s.teams, r.team) {
            Some(t) => {
                let mut t2 = team_now(t, now);
                t2.spend = sat_add(t2.spend, c);
                ws.push(Write::PutTeam(t2));
                ws.push(Write::PutUsage(count_tokens(&s.usage, SCOPE_TEAM, t.id, w, tokens)));
            }
            None => {}
        }
    }
    ws.push(Write::PutUsage(count_tokens(&s.usage, SCOPE_DEPLOYMENT, r.deployment, w, tokens)));
    if status == CallStatus::Retryable {
        match find_deployment(&s.deployments, r.deployment) {
            Some(d) => ws.push(Write::PutDeployment(record_failure(d, s.settings.allowed_fails, s.settings.cooldown_secs, now))),
            None => {}
        }
    }
    ws.push(Write::Emit(SpendLog {
        reservation: id,
        key: r.key_id,
        team: r.team,
        deployment: r.deployment,
        model: r.model,
        prompt_tokens,
        completion_tokens,
        cost: c,
        at: now,
        status,
    }));
    Ok((ws, Reply::Settled { cost: c }))
}

/// Release a reservation that outlived the reservation TTL, charging nothing.
pub fn expire(a: &Principal, s: &Snapshot, id: u64) -> Outcome {
    let r = match find_reservation(&s.reservations, id) {
        None => return Err(Error::NotFound),
        Some(r) => r,
    };
    if !may_close(a, s, &r) {
        return Err(Error::Forbidden);
    }
    if a.now < sat_add(r.created_at, s.settings.reservation_ttl) {
        return Err(Error::NotExpired);
    }
    let mut ws = Vec::new();
    ws.push(Write::DelReservation(id));
    ws.push(Write::Emit(SpendLog {
        reservation: id,
        key: r.key_id,
        team: r.team,
        deployment: r.deployment,
        model: r.model,
        prompt_tokens: 0,
        completion_tokens: 0,
        cost: 0,
        at: a.now,
        status: CallStatus::Expired,
    }));
    Ok((ws, Reply::Settled { cost: 0 }))
}

// ---------------------------------------------------------------------------
// Management (admins only; `transition` checks)

fn configure(s: &Snapshot, allowed_fails: u64, cooldown_secs: u64, reservation_ttl: u64) -> Outcome {
    let st = Settings { next_id: s.settings.next_id, allowed_fails, cooldown_secs, reservation_ttl };
    Ok((one(Write::SetSettings(st)), Reply::Done))
}

fn create_team(a: &Principal, s: &Snapshot, spec: &TeamSpec, names: &Vec<Vec<u8>>) -> Outcome {
    let ids = match resolve_models(&s.models, names) {
        Err(e) => return Err(e),
        Ok(ids) => ids,
    };
    let id = match fresh(s) {
        Err(e) => return Err(e),
        Ok(id) => id,
    };
    let t = Team {
        id,
        max_budget: spec.max_budget,
        spend: 0,
        rpm: spec.rpm,
        tpm: spec.tpm,
        budget_duration: spec.budget_duration,
        budget_reset_at: sat_add(a.now, spec.budget_duration),
        blocked: false,
        all_models: spec.all_models,
    };
    let mut ws = Vec::new();
    ws.push(Write::PutTeam(t));
    let mut i = 0;
    while i < ids.len() {
        ws.push(Write::PutTeamModel(TeamModel { team: id, model: ids[i] }));
        i += 1;
    }
    ws.push(Write::SetSettings(with_next_id(s.settings, id)));
    Ok((ws, Reply::Created(id)))
}

fn update_team(a: &Principal, s: &Snapshot, id: u64, p: &TeamPatch) -> Outcome {
    let t = match find_team(&s.teams, id) {
        None => return Err(Error::NotFound),
        Some(t) => t,
    };
    let mut t2 = t;
    match p.max_budget {
        Some(v) => t2.max_budget = v,
        None => {}
    }
    match p.rpm {
        Some(v) => t2.rpm = v,
        None => {}
    }
    match p.tpm {
        Some(v) => t2.tpm = v,
        None => {}
    }
    match p.budget_duration {
        Some(v) => {
            t2.budget_duration = v;
            t2.budget_reset_at = sat_add(a.now, v);
        }
        None => {}
    }
    match p.blocked {
        Some(v) => t2.blocked = v,
        None => {}
    }
    match p.all_models {
        Some(v) => t2.all_models = v,
        None => {}
    }
    Ok((one(Write::PutTeam(t2)), Reply::Done))
}

/// Writes that remove every model grant of team `team`.
fn clear_team_models(v: &Vec<TeamModel>, team: u64, ws: &mut Vec<Write>) {
    let mut i = 0;
    while i < v.len() {
        if v[i].team == team {
            ws.push(Write::DelTeamModel(team, v[i].model));
        }
        i += 1;
    }
}

/// Writes that remove every model grant of key `key`.
fn clear_key_models(v: &Vec<KeyModel>, key: u64, ws: &mut Vec<Write>) {
    let mut i = 0;
    while i < v.len() {
        if v[i].key == key {
            ws.push(Write::DelKeyModel(key, v[i].model));
        }
        i += 1;
    }
}

fn delete_team(s: &Snapshot, id: u64) -> Outcome {
    match find_team(&s.teams, id) {
        None => return Err(Error::NotFound),
        Some(_) => {}
    }
    if team_in_use(&s.keys, id) {
        return Err(Error::InUse);
    }
    let mut ws = Vec::new();
    clear_team_models(&s.team_models, id, &mut ws);
    ws.push(Write::DelTeam(id));
    Ok((ws, Reply::Done))
}

fn set_team_models(s: &Snapshot, id: u64, names: &Vec<Vec<u8>>) -> Outcome {
    match find_team(&s.teams, id) {
        None => return Err(Error::NotFound),
        Some(_) => {}
    }
    let ids = match resolve_models(&s.models, names) {
        Err(e) => return Err(e),
        Ok(ids) => ids,
    };
    let mut ws = Vec::new();
    clear_team_models(&s.team_models, id, &mut ws);
    let mut i = 0;
    while i < ids.len() {
        ws.push(Write::PutTeamModel(TeamModel { team: id, model: ids[i] }));
        i += 1;
    }
    Ok((ws, Reply::Done))
}

fn create_key(a: &Principal, s: &Snapshot, spec: &KeySpec, names: &Vec<Vec<u8>>) -> Outcome {
    if spec.team != 0 {
        match find_team(&s.teams, spec.team) {
            None => return Err(Error::NotFound),
            Some(_) => {}
        }
    }
    let ids = match resolve_models(&s.models, names) {
        Err(e) => return Err(e),
        Ok(ids) => ids,
    };
    let id = match fresh(s) {
        Err(e) => return Err(e),
        Ok(id) => id,
    };
    let k = Key {
        id,
        team: spec.team,
        user: spec.user,
        max_budget: spec.max_budget,
        spend: 0,
        rpm: spec.rpm,
        tpm: spec.tpm,
        max_parallel: spec.max_parallel,
        expires_at: spec.expires_at,
        budget_duration: spec.budget_duration,
        budget_reset_at: sat_add(a.now, spec.budget_duration),
        blocked: false,
        admin: spec.admin,
        all_models: spec.all_models,
    };
    let mut ws = Vec::new();
    ws.push(Write::PutKey(k));
    let mut i = 0;
    while i < ids.len() {
        ws.push(Write::PutKeyModel(KeyModel { key: id, model: ids[i] }));
        i += 1;
    }
    ws.push(Write::SetSettings(with_next_id(s.settings, id)));
    Ok((ws, Reply::Created(id)))
}

fn update_key(a: &Principal, s: &Snapshot, id: u64, p: &KeyPatch) -> Outcome {
    let k = match find_key(&s.keys, id) {
        None => return Err(Error::NotFound),
        Some(k) => k,
    };
    let mut k2 = k;
    match p.max_budget {
        Some(v) => k2.max_budget = v,
        None => {}
    }
    match p.rpm {
        Some(v) => k2.rpm = v,
        None => {}
    }
    match p.tpm {
        Some(v) => k2.tpm = v,
        None => {}
    }
    match p.max_parallel {
        Some(v) => k2.max_parallel = v,
        None => {}
    }
    match p.expires_at {
        Some(v) => k2.expires_at = v,
        None => {}
    }
    match p.budget_duration {
        Some(v) => {
            k2.budget_duration = v;
            k2.budget_reset_at = sat_add(a.now, v);
        }
        None => {}
    }
    match p.blocked {
        Some(v) => k2.blocked = v,
        None => {}
    }
    match p.all_models {
        Some(v) => k2.all_models = v,
        None => {}
    }
    Ok((one(Write::PutKey(k2)), Reply::Done))
}

fn delete_key(s: &Snapshot, id: u64) -> Outcome {
    match find_key(&s.keys, id) {
        None => return Err(Error::NotFound),
        Some(_) => {}
    }
    let mut ws = Vec::new();
    clear_key_models(&s.key_models, id, &mut ws);
    ws.push(Write::DelKey(id));
    Ok((ws, Reply::Done))
}

fn set_key_models(s: &Snapshot, id: u64, names: &Vec<Vec<u8>>) -> Outcome {
    match find_key(&s.keys, id) {
        None => return Err(Error::NotFound),
        Some(_) => {}
    }
    let ids = match resolve_models(&s.models, names) {
        Err(e) => return Err(e),
        Ok(ids) => ids,
    };
    let mut ws = Vec::new();
    clear_key_models(&s.key_models, id, &mut ws);
    let mut i = 0;
    while i < ids.len() {
        ws.push(Write::PutKeyModel(KeyModel { key: id, model: ids[i] }));
        i += 1;
    }
    Ok((ws, Reply::Done))
}

fn reset_key_spend(s: &Snapshot, id: u64) -> Outcome {
    match find_key(&s.keys, id) {
        None => Err(Error::NotFound),
        Some(k) => {
            let mut k2 = k;
            k2.spend = 0;
            Ok((one(Write::PutKey(k2)), Reply::Done))
        }
    }
}

fn upsert_deployment(s: &Snapshot, name: &Vec<u8>, spec: &DeploymentSpec) -> Outcome {
    let mut ws = Vec::new();
    let model = match find_model(&s.models, name) {
        Some(m) => m,
        None => {
            let id = match fresh(s) {
                Err(e) => return Err(e),
                Ok(id) => id,
            };
            ws.push(Write::PutModel(Model { id, name: name.clone() }));
            ws.push(Write::SetSettings(with_next_id(s.settings, id)));
            id
        }
    };
    let d = match find_deployment(&s.deployments, spec.id) {
        Some(old) => Deployment {
            id: spec.id,
            model,
            input_cost: spec.input_cost,
            output_cost: spec.output_cost,
            rpm: spec.rpm,
            tpm: spec.tpm,
            priority: spec.priority,
            enabled: spec.enabled,
            fails: old.fails,
            fail_window: old.fail_window,
            cooldown_until: old.cooldown_until,
        },
        None => Deployment {
            id: spec.id,
            model,
            input_cost: spec.input_cost,
            output_cost: spec.output_cost,
            rpm: spec.rpm,
            tpm: spec.tpm,
            priority: spec.priority,
            enabled: spec.enabled,
            fails: 0,
            fail_window: 0,
            cooldown_until: 0,
        },
    };
    ws.push(Write::PutDeployment(d));
    Ok((ws, Reply::Created(model)))
}

fn delete_deployment(s: &Snapshot, id: u64) -> Outcome {
    match find_deployment(&s.deployments, id) {
        None => Err(Error::NotFound),
        Some(_) => Ok((one(Write::DelDeployment(id)), Reply::Done)),
    }
}

// ---------------------------------------------------------------------------
// Reads

fn key_info(a: &Principal, s: &Snapshot, id: u64) -> Outcome {
    if !(is_admin(a, s) || (!a.master && a.key == id)) {
        return Err(Error::Forbidden);
    }
    match find_key(&s.keys, id) {
        None => Err(Error::NotFound),
        Some(k) => Ok((
            Vec::new(),
            Reply::KeyInfo { key: k, models: models_of_key(&s.key_models, id), reserved: reserved_by_key(&s.reservations, id) },
        )),
    }
}

fn team_info(a: &Principal, s: &Snapshot, id: u64) -> Outcome {
    if !is_admin(a, s) {
        if a.master {
            return Err(Error::Forbidden);
        }
        match find_key(&s.keys, a.key) {
            Some(k) => {
                if k.team != id {
                    return Err(Error::Forbidden);
                }
            }
            None => return Err(Error::Forbidden),
        }
    }
    match find_team(&s.teams, id) {
        None => Err(Error::NotFound),
        Some(t) => Ok((
            Vec::new(),
            Reply::TeamInfo { team: t, models: models_of_team(&s.team_models, id), reserved: reserved_by_team(&s.reservations, id) },
        )),
    }
}

fn list_models(a: &Principal, s: &Snapshot) -> Outcome {
    if is_admin(a, s) {
        return Ok((Vec::new(), Reply::Models(s.models.clone())));
    }
    let k = match find_key(&s.keys, a.key) {
        None => return Err(Error::Unauthorized),
        Some(k) => k,
    };
    let team = if k.team == 0 { None } else { find_team(&s.teams, k.team) };
    let mut out = Vec::new();
    let mut i = 0;
    while i < s.models.len() {
        if may_call(s, &k, &team, s.models[i].id) {
            out.push(s.models[i].clone());
        }
        i += 1;
    }
    Ok((Vec::new(), Reply::Models(out)))
}

// ---------------------------------------------------------------------------
// The kernel

/// The gateway's logic: a command's writes and reply, or a refusal that
/// commits nothing.
pub fn transition(a: &Principal, s: &Snapshot, cmd: &Command) -> Outcome {
    match cmd {
        Command::Admit { model, prompt_tokens, max_tokens, exclude } => admit(a, s, model, *prompt_tokens, *max_tokens, exclude),
        Command::Settle { reservation, prompt_tokens, completion_tokens, status } => {
            settle(a, s, *reservation, *prompt_tokens, *completion_tokens, *status)
        }
        Command::Expire { reservation } => expire(a, s, *reservation),
        Command::KeyInfo { id } => key_info(a, s, *id),
        Command::TeamInfo { id } => team_info(a, s, *id),
        Command::ListModels => list_models(a, s),
        _ => {
            if !is_admin(a, s) {
                return Err(Error::Forbidden);
            }
            manage(a, s, cmd)
        }
    }
}

/// The management commands, once the caller is known to be an admin.
fn manage(a: &Principal, s: &Snapshot, cmd: &Command) -> Outcome {
    match cmd {
        Command::Configure { allowed_fails, cooldown_secs, reservation_ttl } => configure(s, *allowed_fails, *cooldown_secs, *reservation_ttl),
        Command::CreateTeam { spec, models } => create_team(a, s, spec, models),
        Command::UpdateTeam { id, patch } => update_team(a, s, *id, patch),
        Command::DeleteTeam { id } => delete_team(s, *id),
        Command::SetTeamModels { id, models } => set_team_models(s, *id, models),
        Command::CreateKey { spec, models } => create_key(a, s, spec, models),
        Command::UpdateKey { id, patch } => update_key(a, s, *id, patch),
        Command::DeleteKey { id } => delete_key(s, *id),
        Command::SetKeyModels { id, models } => set_key_models(s, *id, models),
        Command::ResetKeySpend { id } => reset_key_spend(s, *id),
        Command::UpsertDeployment { model, spec } => upsert_deployment(s, model, spec),
        Command::DeleteDeployment { id } => delete_deployment(s, *id),
        Command::Dump => Ok((Vec::new(), Reply::State(s.clone()))),
        // Handled by `transition`.
        _ => Err(Error::Forbidden),
    }
}

/// Commands that never write; engines may run them without a write transaction.
pub fn read_only(cmd: &Command) -> bool {
    match cmd {
        Command::Dump => true,
        Command::KeyInfo { .. } => true,
        Command::TeamInfo { .. } => true,
        Command::ListModels => true,
        _ => false,
    }
}

/// What one write does to the state; `schema!` builds `apply` from it.
fn apply_write(s: &mut Snapshot, w: Write) {
    match w {
        Write::SetSettings(x) => s.settings = x,
        Write::PutTeam(x) => Team::put(&mut s.teams, x),
        Write::DelTeam(id) => s.teams = Team::del(&s.teams, id),
        Write::PutKey(x) => Key::put(&mut s.keys, x),
        Write::DelKey(id) => s.keys = Key::del(&s.keys, id),
        Write::PutModel(x) => Model::put(&mut s.models, x),
        Write::PutDeployment(x) => Deployment::put(&mut s.deployments, x),
        Write::DelDeployment(id) => s.deployments = Deployment::del(&s.deployments, id),
        Write::PutKeyModel(x) => KeyModel::put(&mut s.key_models, x),
        Write::DelKeyModel(k, m) => s.key_models = KeyModel::del(&s.key_models, k, m),
        Write::PutTeamModel(x) => TeamModel::put(&mut s.team_models, x),
        Write::DelTeamModel(t, m) => s.team_models = TeamModel::del(&s.team_models, t, m),
        Write::PutUsage(x) => Usage::put(&mut s.usage, x),
        Write::PutReservation(x) => Reservation::put(&mut s.reservations, x),
        Write::DelReservation(id) => s.reservations = Reservation::del(&s.reservations, id),
        // Spend logs leave through the outbox; they change no table.
        Write::Emit(_) => {}
    }
}

/// The table writes one write makes; a spend log makes none.
fn sql_write(w: &Write, out: &mut Vec<h5i_app_sql::Write>) {
    match w {
        Write::SetSettings(x) => out.push(x.sql_put()),
        Write::PutTeam(x) => out.push(x.sql_put()),
        Write::DelTeam(id) => out.push(Team::sql_del(*id)),
        Write::PutKey(x) => out.push(x.sql_put()),
        Write::DelKey(id) => out.push(Key::sql_del(*id)),
        Write::PutModel(x) => out.push(x.sql_put()),
        Write::PutDeployment(x) => out.push(x.sql_put()),
        Write::DelDeployment(id) => out.push(Deployment::sql_del(*id)),
        Write::PutKeyModel(x) => out.push(x.sql_put()),
        Write::DelKeyModel(k, m) => out.push(KeyModel::sql_del(*k, *m)),
        Write::PutTeamModel(x) => out.push(x.sql_put()),
        Write::DelTeamModel(t, m) => out.push(TeamModel::sql_del(*t, *m)),
        Write::PutUsage(x) => out.push(x.sql_put()),
        Write::PutReservation(x) => out.push(x.sql_put()),
        Write::DelReservation(id) => out.push(Reservation::sql_del(*id)),
        Write::Emit(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MASTER: Principal = Principal { org: 1, key: 0, master: true, now: 1_000 };

    fn as_key(key: u64, now: u64) -> Principal {
        Principal { org: 1, key, master: false, now }
    }

    fn run(s: &Snapshot, a: &Principal, c: Command) -> (Snapshot, Result<Reply, Error>) {
        match transition(a, s, &c) {
            Ok((ws, r)) => (apply(s, &ws), Ok(r)),
            Err(e) => (s.clone(), Err(e)),
        }
    }

    fn ok(s: &Snapshot, a: &Principal, c: Command) -> (Snapshot, Reply) {
        let (s2, r) = run(s, a, c);
        (s2, r.expect("command refused"))
    }

    fn created(r: Reply) -> u64 {
        match r {
            Reply::Created(id) => id,
            r => panic!("expected Created, got {r:?}"),
        }
    }

    fn admitted(r: Result<Reply, Error>) -> (u64, u64, u64) {
        match r {
            Ok(Reply::Admitted { reservation, deployment, amount }) => (reservation, deployment, amount),
            r => panic!("expected Admitted, got {r:?}"),
        }
    }

    fn dep(id: u64, priority: u64) -> DeploymentSpec {
        DeploymentSpec { id, input_cost: 1_000, output_cost: 2_000, rpm: UNLIMITED, tpm: UNLIMITED, priority, enabled: true }
    }

    fn key_spec(team: u64, max_budget: u64) -> KeySpec {
        KeySpec {
            team,
            user: 7,
            max_budget,
            rpm: UNLIMITED,
            tpm: UNLIMITED,
            max_parallel: UNLIMITED,
            expires_at: UNLIMITED,
            budget_duration: 0,
            admin: false,
            all_models: true,
        }
    }

    fn admit_cmd(model: &str, prompt: u64, max: u64) -> Command {
        Command::Admit { model: model.as_bytes().to_vec(), prompt_tokens: prompt, max_tokens: max, exclude: Vec::new() }
    }

    /// Two deployments of "gpt", one of "claude", and one key with a budget.
    fn setup(max_budget: u64) -> (Snapshot, u64) {
        let s = Snapshot::default();
        let (s, _) = ok(&s, &MASTER, Command::Configure { allowed_fails: 1, cooldown_secs: 30, reservation_ttl: 600 });
        let (s, _) = ok(&s, &MASTER, Command::UpsertDeployment { model: b"gpt".to_vec(), spec: dep(100, 0) });
        let (s, _) = ok(&s, &MASTER, Command::UpsertDeployment { model: b"gpt".to_vec(), spec: dep(101, 1) });
        let (s, _) = ok(&s, &MASTER, Command::UpsertDeployment { model: b"claude".to_vec(), spec: dep(200, 0) });
        let (s, r) = ok(&s, &MASTER, Command::CreateKey { spec: key_spec(0, max_budget), models: Vec::new() });
        (s, created(r))
    }

    #[test]
    fn admit_settle_charges_actual_cost() {
        let (s, k) = setup(UNLIMITED);
        let (s, r) = run(&s, &as_key(k, 1_000), admit_cmd("gpt", 10, 20));
        let (res, d, amount) = admitted(r);
        assert_eq!(d, 100);
        assert_eq!(amount, 10 * 1_000 + 20 * 2_000);
        assert_eq!(reserved_by_key(&s.reservations, k), amount);
        let settle = Command::Settle { reservation: res, prompt_tokens: 10, completion_tokens: 5, status: CallStatus::Success };
        let (s, r) = ok(&s, &as_key(k, 1_001), settle.clone());
        assert_eq!(r, Reply::Settled { cost: 10 * 1_000 + 5 * 2_000 });
        assert_eq!(find_key(&s.keys, k).unwrap().spend, 20_000);
        assert_eq!(reserved_by_key(&s.reservations, k), 0);
        // A reservation settles once.
        assert_eq!(run(&s, &as_key(k, 1_002), settle).1, Err(Error::NotFound));
    }

    #[test]
    fn budget_counts_reservations() {
        // Each call may cost up to 50_000.
        let (s, k) = setup(120_000);
        let (s, r) = run(&s, &as_key(k, 1_000), admit_cmd("gpt", 10, 20));
        admitted(r);
        let (s, r) = run(&s, &as_key(k, 1_000), admit_cmd("gpt", 10, 20));
        admitted(r);
        assert_eq!(run(&s, &as_key(k, 1_000), admit_cmd("gpt", 10, 20)).1, Err(Error::KeyBudgetExceeded));
    }

    #[test]
    fn rate_limit_resets_with_the_window() {
        let (s, k) = setup(UNLIMITED);
        let patch = KeyPatch { max_budget: None, rpm: Some(1), tpm: None, max_parallel: None, expires_at: None, budget_duration: None, blocked: None, all_models: None };
        let (s, _) = ok(&s, &MASTER, Command::UpdateKey { id: k, patch });
        let (s, r) = run(&s, &as_key(k, 60), admit_cmd("gpt", 1, 1));
        admitted(r);
        assert_eq!(run(&s, &as_key(k, 119), admit_cmd("gpt", 1, 1)).1, Err(Error::KeyRateLimited));
        admitted(run(&s, &as_key(k, 120), admit_cmd("gpt", 1, 1)).1);
    }

    #[test]
    fn retryable_failures_cool_a_deployment_down() {
        let (s, k) = setup(UNLIMITED);
        let mut s = s;
        // allowed_fails = 1: the second failure in a window cools deployment 100 down.
        for _ in 0..2 {
            let (s2, r) = run(&s, &as_key(k, 1_000), admit_cmd("gpt", 1, 1));
            let (res, d, _) = admitted(r);
            assert_eq!(d, 100);
            let settle = Command::Settle { reservation: res, prompt_tokens: 0, completion_tokens: 0, status: CallStatus::Retryable };
            s = ok(&s2, &as_key(k, 1_000), settle).0;
        }
        let (_, r) = run(&s, &as_key(k, 1_010), admit_cmd("gpt", 1, 1));
        assert_eq!(admitted(r).1, 101);
        let (_, r) = run(&s, &as_key(k, 1_030), admit_cmd("gpt", 1, 1));
        assert_eq!(admitted(r).1, 100);
    }

    #[test]
    fn fallback_excludes_tried_deployments() {
        let (s, k) = setup(UNLIMITED);
        let c = Command::Admit { model: b"gpt".to_vec(), prompt_tokens: 1, max_tokens: 1, exclude: vec![100] };
        assert_eq!(admitted(run(&s, &as_key(k, 1_000), c).1).1, 101);
        let c = Command::Admit { model: b"gpt".to_vec(), prompt_tokens: 1, max_tokens: 1, exclude: vec![100, 101] };
        assert_eq!(run(&s, &as_key(k, 1_000), c).1, Err(Error::NoDeployment));
    }

    #[test]
    fn model_access_and_teams() {
        let (s, _) = setup(UNLIMITED);
        let team = TeamSpec { max_budget: UNLIMITED, rpm: UNLIMITED, tpm: UNLIMITED, budget_duration: 0, all_models: false };
        let (s, r) = ok(&s, &MASTER, Command::CreateTeam { spec: team, models: vec![b"claude".to_vec()] });
        let t = created(r);
        let (s, r) = ok(&s, &MASTER, Command::CreateKey { spec: key_spec(t, UNLIMITED), models: Vec::new() });
        let k = created(r);
        assert_eq!(run(&s, &as_key(k, 1_000), admit_cmd("gpt", 1, 1)).1, Err(Error::ModelNotAllowed));
        admitted(run(&s, &as_key(k, 1_000), admit_cmd("claude", 1, 1)).1);
        assert_eq!(run(&s, &as_key(k, 1_000), admit_cmd("nope", 1, 1)).1, Err(Error::ModelNotFound));
        match run(&s, &as_key(k, 1_000), Command::ListModels).1 {
            Ok(Reply::Models(ms)) => assert_eq!(ms.len(), 1),
            r => panic!("{r:?}"),
        }
        assert_eq!(run(&s, &MASTER, Command::DeleteTeam { id: t }).1, Err(Error::InUse));
        // Keys cannot manage the gateway or read other keys.
        assert_eq!(run(&s, &as_key(k, 1_000), Command::DeleteTeam { id: t }).1, Err(Error::Forbidden));
        assert_eq!(run(&s, &as_key(k, 1_000), Command::KeyInfo { id: k + 100 }).1, Err(Error::Forbidden));
    }

    #[test]
    fn blocked_expired_and_parallel_keys() {
        let (s, k) = setup(UNLIMITED);
        let none = KeyPatch { max_budget: None, rpm: None, tpm: None, max_parallel: None, expires_at: None, budget_duration: None, blocked: None, all_models: None };
        let (s1, _) = ok(&s, &MASTER, Command::UpdateKey { id: k, patch: KeyPatch { blocked: Some(true), ..none } });
        assert_eq!(run(&s1, &as_key(k, 1_000), admit_cmd("gpt", 1, 1)).1, Err(Error::KeyBlocked));
        let (s2, _) = ok(&s, &MASTER, Command::UpdateKey { id: k, patch: KeyPatch { expires_at: Some(1_000), ..none } });
        assert_eq!(run(&s2, &as_key(k, 1_000), admit_cmd("gpt", 1, 1)).1, Err(Error::KeyExpired));
        let (s3, _) = ok(&s, &MASTER, Command::UpdateKey { id: k, patch: KeyPatch { max_parallel: Some(1), ..none } });
        let (s3, r) = run(&s3, &as_key(k, 1_000), admit_cmd("gpt", 1, 1));
        admitted(r);
        assert_eq!(run(&s3, &as_key(k, 1_000), admit_cmd("gpt", 1, 1)).1, Err(Error::KeyParallelLimit));
        assert_eq!(run(&s, &as_key(k + 1, 1_000), admit_cmd("gpt", 1, 1)).1, Err(Error::Unauthorized));
    }

    #[test]
    fn budget_periods_reset_spend() {
        let (s, _) = setup(UNLIMITED);
        let spec = KeySpec { budget_duration: 100, ..key_spec(0, 60_000) };
        let (s, r) = ok(&s, &MASTER, Command::CreateKey { spec, models: Vec::new() });
        let k = created(r);
        let (s, r) = run(&s, &as_key(k, 1_000), admit_cmd("gpt", 10, 20));
        let (res, _, _) = admitted(r);
        let settle = Command::Settle { reservation: res, prompt_tokens: 10, completion_tokens: 20, status: CallStatus::Success };
        let (s, _) = ok(&s, &as_key(k, 1_001), settle);
        assert_eq!(run(&s, &as_key(k, 1_050), admit_cmd("gpt", 10, 20)).1, Err(Error::KeyBudgetExceeded));
        // The period started at 1_000 and lasts 100 seconds.
        admitted(run(&s, &as_key(k, 1_100), admit_cmd("gpt", 10, 20)).1);
    }

    #[test]
    fn expire_releases_old_reservations() {
        let (s, k) = setup(UNLIMITED);
        let (s, r) = run(&s, &as_key(k, 1_000), admit_cmd("gpt", 1, 1));
        let (res, _, _) = admitted(r);
        assert_eq!(run(&s, &as_key(k, 1_599), Command::Expire { reservation: res }).1, Err(Error::NotExpired));
        let (s, r) = ok(&s, &as_key(k, 1_600), Command::Expire { reservation: res });
        assert_eq!(r, Reply::Settled { cost: 0 });
        assert!(s.reservations.is_empty());
    }

    #[test]
    fn master_key_calls_without_limits() {
        let (s, _) = setup(0);
        let (s, r) = run(&s, &MASTER, admit_cmd("claude", 1, 1));
        let (res, d, _) = admitted(r);
        assert_eq!(d, 200);
        let settle = Command::Settle { reservation: res, prompt_tokens: 1, completion_tokens: 1, status: CallStatus::Success };
        ok(&s, &MASTER, settle);
    }

    #[test]
    fn least_busy_breaks_priority_ties() {
        let s = Snapshot::default();
        let (s, _) = ok(&s, &MASTER, Command::UpsertDeployment { model: b"m".to_vec(), spec: dep(1, 0) });
        let (s, _) = ok(&s, &MASTER, Command::UpsertDeployment { model: b"m".to_vec(), spec: dep(2, 0) });
        let (s, r) = run(&s, &MASTER, admit_cmd("m", 1, 1));
        assert_eq!(admitted(r).1, 1);
        let (_, r) = run(&s, &MASTER, admit_cmd("m", 1, 1));
        assert_eq!(admitted(r).1, 2);
    }
}
