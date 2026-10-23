import GatewayKernel
import Schema
import H5iAppLib
/-!
# What the gateway should do

The file to review. It restates the gateway's policy on plain lists and
natural numbers, with no loops and no machine integers: what a call costs,
when a budget or a rate limit admits a call, which deployment a call is
routed to, who counts as an admin, and what committing a write means. The
other files prove that the extracted Rust agrees with these definitions.

Money is in nano-dollars and saturates at `MAX`; a limit equal to `MAX`
never refuses.
-/
open Aeneas Aeneas.Std gateway_kernel

namespace gateway_kernel.Spec

/-! ## Numbers -/

/-- The largest `u64`. A budget or limit of `MAX` never refuses. -/
abbrev MAX : Nat := 2 ^ 64 - 1

/-- Addition and multiplication as the kernel does them: capped at `MAX`. -/
def sat (n : Nat) : Nat := min n MAX

/-- What a call costs: prompt tokens at the input price plus completion
tokens at the output price, each product and the sum capped at `MAX`. -/
def price (inputCost outputCost prompt completion : Nat) : Nat :=
  sat (sat (prompt * inputCost) + sat (completion * outputCost))

/-- A budget of `maxBudget` admits `amount` more on top of `spend` and
`reserved`: it is unlimited, or the three fit in it. -/
def Within (spend reserved amount maxBudget : Nat) : Prop :=
  maxBudget = MAX ∨ spend + reserved + amount ≤ maxBudget

/-- The fixed rate-limit window a time falls in (60 seconds each). -/
def window (now : Nat) : Nat := now / 60

/-- The spend of a budget at time `now`: a period that has ended (`duration`
non-zero and `resetAt` reached) starts again from zero. -/
def spendAt (spend duration resetAt now : Nat) : Nat :=
  if duration ≠ 0 ∧ resetAt ≤ now then 0 else spend

/-! ## State -/

/-- One tenant's rows as lists. -/
structure St where
  settings : Settings
  teams : List Team
  keys : List Key
  models : List Model
  deployments : List Deployment
  keyModels : List KeyModel
  teamModels : List TeamModel
  usage : List Usage
  reservations : List Reservation

def Snapshot.toSt (s : Snapshot) : St :=
  ⟨s.settings, s.teams.val, s.keys.val, s.models.val, s.deployments.val, s.key_models.val,
    s.team_models.val, s.usage.val, s.reservations.val⟩

def findKey (st : St) (id : Nat) : Option Key := st.keys.find? (fun k => k.id.val = id)
def findTeam (st : St) (id : Nat) : Option Team := st.teams.find? (fun t => t.id.val = id)
def findDeployment (st : St) (id : Nat) : Option Deployment :=
  st.deployments.find? (fun d => d.id.val = id)
def findReservation (st : St) (id : Nat) : Option Reservation :=
  st.reservations.find? (fun r => r.id.val = id)

/-- The id of the model group named `name`. -/
def findModel (st : St) (nm : List U8) : Option Nat :=
  (st.models.find? (fun m => m.name.val = nm)).map (fun m => m.id.val)

/-- Requests and tokens counted for `(scope, id)` in window `w`. A counter
from an earlier window counts as zero. -/
def usedIn (st : St) (scope id w : Nat) : Nat × Nat :=
  match st.usage.find? (fun u => u.scope.val = scope ∧ u.id.val = id) with
  | some u => if u.window.val = w then (u.requests.val, u.tokens.val) else (0, 0)
  | none => (0, 0)

/-- The reservations of key `k` and of team `t`. -/
def reservationsOfKey (st : St) (k : Nat) : List Reservation := st.reservations.filter (fun r => r.key_id.val = k)
def reservationsOfTeam (st : St) (t : Nat) : List Reservation := st.reservations.filter (fun r => r.team.val = t)

/-- The amount held by a key's or a team's unsettled calls, capped at `MAX`. -/
def reservedKey (st : St) (k : Nat) : Nat := sat ((reservationsOfKey st k).map (fun r => r.amount.val)).sum
def reservedTeam (st : St) (t : Nat) : Nat := sat ((reservationsOfTeam st t).map (fun r => r.amount.val)).sum

/-- The number of a key's unsettled calls, capped at `MAX`. -/
def inFlight (st : St) (k : Nat) : Nat := sat (reservationsOfKey st k).length

/-! ## Who may do what -/

/-- The master key, or an admin key that is neither blocked nor expired. -/
def IsAdmin (st : St) (a : Principal) : Prop :=
  a.master = true ∨
    ∃ k, findKey st a.key.val = some k ∧ k.admin = true ∧ k.blocked = false ∧ a.now.val < k.expires_at.val

/-- Key `k`, of team `t` if any, may call model `m`: the key is granted
every model or this one, and so is the team. -/
def MayCall (st : St) (k : Key) (t : Option Team) (m : Nat) : Prop :=
  (k.all_models = true ∨ ∃ g ∈ st.keyModels, g.key = k.id ∧ g.model.val = m) ∧
  ∀ team, t = some team → team.all_models = true ∨ ∃ g ∈ st.teamModels, g.team = team.id ∧ g.model.val = m

/-! ## Routing -/

/-- Deployment `d` may serve a call to model `m` at `now` without trying the
deployments in `exclude`: it serves `m`, is enabled, is not cooling down, was
not tried, and is under its own limits in the current window. -/
def Eligible (st : St) (now m : Nat) (exclude : List Nat) (d : Deployment) : Prop :=
  d.model.val = m ∧ d.enabled = true ∧ d.cooldown_until.val ≤ now ∧ d.id.val ∉ exclude ∧
    (usedIn st 2 d.id.val (window now)).1 < d.rpm.val ∧ (usedIn st 2 d.id.val (window now)).2 < d.tpm.val

/-- Requests a deployment served in the current window. -/
def load (st : St) (now : Nat) (d : Deployment) : Nat := (usedIn st 2 d.id.val (window now)).1

/-- `d` is preferred to `e`: lower priority, then less busy, then lower id. -/
def Prefers (st : St) (now : Nat) (d e : Deployment) : Prop :=
  d.priority.val < e.priority.val ∨
    (d.priority.val = e.priority.val ∧
      (load st now d < load st now e ∨ (load st now d = load st now e ∧ d.id.val < e.id.val)))

/-- `d` is where a call to `m` goes: an eligible deployment that no eligible
deployment is preferred to. -/
def Best (st : St) (now m : Nat) (exclude : List Nat) (d : Deployment) : Prop :=
  d ∈ st.deployments ∧ Eligible st now m exclude d ∧
    ∀ e ∈ st.deployments, Eligible st now m exclude e → ¬ Prefers st now e d

/-! ## Admission

`AdmitByKey` is the whole policy for a call by a virtual key, in the order a
reader would check it. The proofs show that `Admit` succeeds exactly when it
holds (and ids are not exhausted), reserving `amount` on deployment `d`. -/

structure AdmitByKey (st : St) (a : Principal) (m prompt maxTokens : Nat) (exclude : List Nat)
    (k : Key) (t : Option Team) (d : Deployment) (amount : Nat) : Prop where
  not_master : a.master = false
  key : findKey st a.key.val = some k
  unblocked : k.blocked = false
  unexpired : a.now.val < k.expires_at.val
  no_team : k.team.val = 0 → t = none
  team : k.team.val ≠ 0 → ∃ team, findTeam st k.team.val = some team ∧ team.blocked = false ∧ t = some team
  may_call : MayCall st k t m
  key_rpm : (usedIn st 0 k.id.val (window a.now.val)).1 < k.rpm.val
  key_tpm : (usedIn st 0 k.id.val (window a.now.val)).2 < k.tpm.val
  parallel : inFlight st k.id.val < k.max_parallel.val
  team_limits : ∀ team, t = some team →
    (usedIn st 1 team.id.val (window a.now.val)).1 < team.rpm.val ∧
    (usedIn st 1 team.id.val (window a.now.val)).2 < team.tpm.val
  best : Best st a.now.val m exclude d
  priced : amount = price d.input_cost.val d.output_cost.val prompt maxTokens
  key_budget : Within (spendAt k.spend.val k.budget_duration.val k.budget_reset_at.val a.now.val)
    (reservedKey st k.id.val) amount k.max_budget.val
  team_budget : ∀ team, t = some team →
    Within (spendAt team.spend.val team.budget_duration.val team.budget_reset_at.val a.now.val)
      (reservedTeam st team.id.val) amount team.max_budget.val

/-! ## Committing writes -/

/-- What one write does to the state. `H5iAppLib.upsert` replaces the row
with the same key or appends it; a spend log changes no table. -/
def applyWrite (st : St) : Write → St
  | .SetSettings x => { st with settings := x }
  | .PutTeam x => { st with teams := H5iAppLib.upsert (·.id) x st.teams }
  | .DelTeam id => { st with teams := st.teams.filter (fun t => t.id ≠ id) }
  | .PutKey x => { st with keys := H5iAppLib.upsert (·.id) x st.keys }
  | .DelKey id => { st with keys := st.keys.filter (fun k => k.id ≠ id) }
  | .PutModel x => { st with models := H5iAppLib.upsert (·.id) x st.models }
  | .PutDeployment x => { st with deployments := H5iAppLib.upsert (·.id) x st.deployments }
  | .DelDeployment id => { st with deployments := st.deployments.filter (fun d => d.id ≠ id) }
  | .PutKeyModel x => { st with keyModels := H5iAppLib.upsert (fun g => (g.key, g.model)) x st.keyModels }
  | .DelKeyModel k m => { st with keyModels := st.keyModels.filter (fun g => ¬ (g.key = k ∧ g.model = m)) }
  | .PutTeamModel x => { st with teamModels := H5iAppLib.upsert (fun g => (g.team, g.model)) x st.teamModels }
  | .DelTeamModel t m => { st with teamModels := st.teamModels.filter (fun g => ¬ (g.team = t ∧ g.model = m)) }
  | .PutUsage x => { st with usage := H5iAppLib.upsert (fun u => (u.scope, u.id)) x st.usage }
  | .PutReservation x => { st with reservations := H5iAppLib.upsert (·.id) x st.reservations }
  | .DelReservation id => { st with reservations := st.reservations.filter (fun r => r.id ≠ id) }
  | .Emit _ => st

def applyAll (st : St) (ws : List Write) : St := ws.foldl applyWrite st

def init : St := ⟨⟨0#u64, 0#u64, 0#u64, 0#u64⟩, [], [], [], [], [], [], [], []⟩

/-- The states reachable from an empty gateway by successful commands. -/
inductive Reachable : St → Prop
  | init : Reachable init
  | step {a s c ws r} : Reachable (Snapshot.toSt s) → transition a s c = .ok (.Ok (ws, r)) →
      Reachable (applyAll (Snapshot.toSt s) ws.val)

/-! ## Invariants

Structural facts every reachable state satisfies: ids are unique within
each table, every id (and every id a reservation refers to) was handed out
by the counter, so a new id is fresh, and every key's team exists. -/

structure Inv (st : St) : Prop where
  keys_nodup : (st.keys.map (·.id)).Nodup
  teams_nodup : (st.teams.map (·.id)).Nodup
  models_nodup : (st.models.map (·.id)).Nodup
  deployments_nodup : (st.deployments.map (·.id)).Nodup
  reservations_nodup : (st.reservations.map (·.id)).Nodup
  keys_fresh : ∀ k ∈ st.keys, 0 < k.id.val ∧ k.id.val ≤ st.settings.next_id.val
  teams_fresh : ∀ t ∈ st.teams, 0 < t.id.val ∧ t.id.val ≤ st.settings.next_id.val
  models_fresh : ∀ m ∈ st.models, m.id.val ≤ st.settings.next_id.val
  reservations_fresh : ∀ r ∈ st.reservations,
    r.id.val ≤ st.settings.next_id.val ∧ r.key_id.val ≤ st.settings.next_id.val ∧ r.team.val ≤ st.settings.next_id.val
  key_team : ∀ k ∈ st.keys, k.team.val ≠ 0 → ∃ t ∈ st.teams, t.id = k.team

/-! ## Budgets

The kernel reserves a call's worst-case cost when it admits the call, and
charges the actual cost when it settles. Budgets can therefore only be
overrun by a provider that reports more tokens than the call reserved, or
by an admin who lowers a budget below what is already spent. `Honest`
excludes exactly those two steps. -/

/-- The key's and the team's budgets hold what they spent plus what they reserved. -/
def KeyWithin (st : St) (k : Key) : Prop :=
  Within k.spend.val (reservedKey st k.id.val) 0 k.max_budget.val

def TeamWithin (st : St) (t : Team) : Prop :=
  Within t.spend.val (reservedTeam st t.id.val) 0 t.max_budget.val

/-- A step that cannot overrun a budget: a settlement charges at most what
its reservation held, and a new budget covers what is spent and reserved. -/
def Honest (st : St) : Command → Prop
  | .Settle rid prompt completion _ =>
    ∀ r, findReservation st rid.val = some r →
      price r.input_cost.val r.output_cost.val prompt.val completion.val ≤ r.amount.val
  | .UpdateKey id patch =>
    ∀ v k, patch.max_budget = some v → findKey st id.val = some k →
      Within k.spend.val (reservedKey st id.val) 0 v.val
  | .UpdateTeam id patch =>
    ∀ v t, patch.max_budget = some v → findTeam st id.val = some t →
      Within t.spend.val (reservedTeam st id.val) 0 v.val
  | _ => True

/-- The states reachable by honest steps. -/
inductive ReachableHonest : St → Prop
  | init : ReachableHonest init
  | step {a s c ws r} : ReachableHonest (Snapshot.toSt s) → Honest (Snapshot.toSt s) c →
      transition a s c = .ok (.Ok (ws, r)) → ReachableHonest (applyAll (Snapshot.toSt s) ws.val)

/-! ## What a key can do without being an admin -/

/-- The fields of a key that only an admin may change. -/
def SameKeyLimits (k k' : Key) : Prop :=
  k'.id = k.id ∧ k'.team = k.team ∧ k'.user = k.user ∧ k'.max_budget = k.max_budget ∧ k'.rpm = k.rpm ∧
    k'.tpm = k.tpm ∧ k'.max_parallel = k.max_parallel ∧ k'.expires_at = k.expires_at ∧
    k'.budget_duration = k.budget_duration ∧ k'.blocked = k.blocked ∧ k'.admin = k.admin ∧
    k'.all_models = k.all_models

def SameTeamLimits (t t' : Team) : Prop :=
  t'.id = t.id ∧ t'.max_budget = t.max_budget ∧ t'.rpm = t.rpm ∧ t'.tpm = t.tpm ∧
    t'.budget_duration = t.budget_duration ∧ t'.blocked = t.blocked ∧ t'.all_models = t.all_models

def SameDeploymentConfig (d d' : Deployment) : Prop :=
  d'.id = d.id ∧ d'.model = d.model ∧ d'.input_cost = d.input_cost ∧ d'.output_cost = d.output_cost ∧
    d'.rpm = d.rpm ∧ d'.tpm = d.tpm ∧ d'.priority = d.priority ∧ d'.enabled = d.enabled

/-- The writes a command by a non-admin key `a` may make: its own key's
spend and its team's spend (never their limits), usage counters, its own
reservations, the id counter, a deployment's health, and spend logs. -/
def KeyMayWrite (st : St) (a : Principal) : Write → Prop
  | .PutKey k => k.id = a.key ∧ ∃ old, findKey st k.id.val = some old ∧ SameKeyLimits old k
  | .PutTeam t => (∃ old, findTeam st t.id.val = some old ∧ SameTeamLimits old t) ∧
      ((∃ k, findKey st a.key.val = some k ∧ k.team = t.id) ∨
        ∃ r ∈ st.reservations, r.key_id = a.key ∧ r.team = t.id)
  | .PutUsage _ => True
  | .PutReservation r => r.key_id = a.key ∧ findReservation st r.id.val = none
  | .DelReservation id => ∃ r, findReservation st id.val = some r ∧ r.key_id = a.key
  | .SetSettings x => x.allowed_fails = st.settings.allowed_fails ∧ x.cooldown_secs = st.settings.cooldown_secs ∧
      x.reservation_ttl = st.settings.reservation_ttl
  | .PutDeployment d => ∃ old, findDeployment st d.id.val = some old ∧ SameDeploymentConfig old d
  | .Emit _ => True
  | _ => False

end gateway_kernel.Spec
