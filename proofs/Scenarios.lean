import Helpers
/-!
# Scenarios

Concrete runs of the extracted `transition`: the theorems' hypotheses can be
met, and the kernel accepts what a refusal-happy kernel would refuse (and
refuses what it should).

The snapshots have one model group, "gpt" (id 1), served by deployment 100
(priority 0) and deployment 101 (priority 1), both at 1000 nano-dollars per
prompt token and 2000 per completion token, and a virtual key 2 with no team.
The id counter is at 10, so the next id is 11. Calls are made at time 1000,
in rate-limit window 16.
-/
open Aeneas Aeneas.Std Result gateway_kernel gateway_kernel.Spec gateway_kernel.Helpers H5iAppLib

namespace gateway_kernel.Scenarios

/-! ## Evaluation -/

theorem max_val : core.num.U64.MAX.val = 18446744073709551615 := by
  simp [core.num.U64.MAX, U64.rMax]

theorem u64_eq_iff' (x y : U64) : x = y ↔ x.val = y.val := (u64_val_eq x y).symm

theorem usage_eq_iff (u v : Usage) : u = v ↔
    u.scope = v.scope ∧ u.id = v.id ∧ u.window = v.window ∧ u.requests = v.requests ∧ u.tokens = v.tokens := by
  cases u; cases v; simp

/-- Simplify after a step: substitute what can be, evaluate the concrete
data, and split the conjunctions and disjunctions of the posts. -/
macro "gw_clean" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (try subst_vars) <;> (simp -failIfUnchanged [$ls,*] at *) <;> (try casesm* _ ∧ _, _ ∨ _) <;>
    (try subst_vars) <;> (simp -failIfUnchanged [$ls,*] at *)))

/-- Run a concrete extracted call: step through it with the `Helpers` specs,
pruning each branch on the concrete data as soon as it is taken. -/
macro "gw_run" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  repeat' (first
    | (step <;> gw_clean [MayCall, EligibleL, usedL, PrefersL, loadL, window, Snapshot.toSt, sat, price,
        SCOPE_KEY, SCOPE_DEPLOYMENT, SCOPE_TEAM, spendAt, max_val, U64.rMax, MAX, Within, vecOf, $ls,*])
    | (split <;> gw_clean [MayCall, EligibleL, usedL, PrefersL, loadL, window, Snapshot.toSt, sat, price,
        SCOPE_KEY, SCOPE_DEPLOYMENT, SCOPE_TEAM, spendAt, max_val, U64.rMax, MAX, Within, vecOf, $ls,*]))
  all_goals (try simp_all [u64_eq_iff', usage_eq_iff, -gateway_kernel.Schema.u64_val_eq])
  all_goals (try and_intros)
  all_goals (try scalar_tac)))

/-- A refusal, as an equation on the extracted code. -/
theorem err_of_spec {m : Result (core.result.Result (alloc.vec.Vec Write × Reply) Error)} {e : Error}
    (h : m ⦃ o => o = .Err e ⦄) : m = ok (.Err e) := by
  obtain ⟨o, ho, rfl⟩ := (WP.spec_equiv_exists _ _).1 h
  exact ho

/-- An acceptance with its writes, as an equation on the extracted code. -/
theorem ok_of_spec {m : Result (core.result.Result (alloc.vec.Vec Write × Reply) Error)} {r : Reply}
    {l : List Write} (h : m ⦃ o => ∃ ws, o = .Ok (ws, r) ∧ ws.val = l ⦄) :
    ∃ ws, m = ok (.Ok (ws, r)) ∧ ws.val = l := by
  obtain ⟨o, ho, ws, rfl, hl⟩ := (WP.spec_equiv_exists _ _).1 h
  exact ⟨ws, ho, hl⟩

/-! ## The snapshots -/

/-- `UNLIMITED`. -/
abbrev UNL : U64 := core.num.U64.MAX

def gpt : alloc.vec.Vec U8 := vecOf [103#u8, 112#u8, 116#u8]
def nope : alloc.vec.Vec U8 := vecOf [110#u8, 111#u8, 112#u8, 101#u8]

def settings0 : Settings := ⟨10#u64, 1#u64, 30#u64, 600#u64⟩
def mGpt : Model := ⟨1#u64, gpt⟩

/-- Deployment `id` of "gpt" with priority `prio`, cooling down until `cool`. -/
def dep (id prio cool : U64) : Deployment :=
  ⟨id, 1#u64, 1000#u64, 2000#u64, UNL, UNL, prio, true, 0#u64, 0#u64, cool⟩

def d100 : Deployment := dep 100#u64 0#u64 0#u64
def d101 : Deployment := dep 101#u64 1#u64 0#u64

/-- Key `id` with budget `budget` and no other limit, allowed every model. -/
def key (id budget : U64) : Key :=
  ⟨id, 0#u64, 7#u64, budget, 0#u64, UNL, UNL, UNL, UNL, 0#u64, 0#u64, false, false, true⟩

/-- The snapshot with keys `ks`, deployments `ds`, usage rows `us` and reservations `rs`. -/
def snap (ks : List Key) (ds : List Deployment) (us : List Usage) (rs : List Reservation)
    (hk : ks.length ≤ Usize.max := by simp only [List.length_cons, List.length_nil]; scalar_tac)
    (hd : ds.length ≤ Usize.max := by simp only [List.length_cons, List.length_nil]; scalar_tac)
    (hu : us.length ≤ Usize.max := by simp only [List.length_cons, List.length_nil]; scalar_tac)
    (hr : rs.length ≤ Usize.max := by simp only [List.length_cons, List.length_nil]; scalar_tac) : Snapshot :=
  ⟨settings0, vecOf [], vecOf ks hk, vecOf [mGpt], vecOf ds hd, vecOf [], vecOf [], vecOf us hu, vecOf rs hr⟩

/-- Key `k` at time `now`. -/
def asKey (k now : U64) : Principal := ⟨1#u64, k, false, now⟩
/-- The master key at time `now`. -/
def master (now : U64) : Principal := ⟨1#u64, 0#u64, true, now⟩

/-- The basic gateway: key 2 with an unlimited budget, both deployments up. -/
def s0 : Snapshot := snap [key 2#u64 UNL] [d100, d101] [] []

/-- The writes of an admission of key 2 (no team) on deployment `d` with
reservation 11 of `amount`, at time `now` (in window 16), from usage rows that count
nothing in window 16. -/
def admitWrites (k : Key) (d amount : U64) (now : U64 := 1000#u64) : List Write :=
  [.PutKey k, .PutUsage ⟨0#u64, 2#u64, 16#u64, 1#u64, 0#u64⟩, .PutUsage ⟨2#u64, d, 16#u64, 1#u64, 0#u64⟩,
    .PutReservation ⟨11#u64, 2#u64, 0#u64, d, 1#u64, 1000#u64, 2000#u64, amount, now⟩,
    .SetSettings ⟨11#u64, 1#u64, 30#u64, 600#u64⟩]

macro "gw_admit" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  unfold transition admit admit_key key_now
  gw_run [snap, gpt, nope, mGpt, dep, d100, d101, key, settings0, asKey, admitWrites, $ls,*]))

/-! ## 1. Routing by priority -/

/-- Key 2 asks for 10 prompt tokens and up to 20 completion tokens of "gpt":
the call goes to deployment 100, the one with the lower priority, and
reserves its worst case, `10 * 1000 + 20 * 2000`, as reservation 11. -/
theorem admit_routes_to_priority :
    ∃ ws, transition (asKey 2#u64 1000#u64) s0 (.Admit gpt 10#u64 20#u64 (vecOf [])) =
        ok (.Ok (ws, .Admitted 11#u64 100#u64 50000#u64)) ∧
      ws.val = admitWrites (key 2#u64 UNL) 100#u64 50000#u64 := by
  apply ok_of_spec
  gw_admit [s0]

/-! ## 2. Fallbacks skip the deployments already tried -/

/-- Having tried deployment 100, the call goes to 101; having tried both,
there is no deployment left. -/
theorem admit_excludes_tried :
    (∃ ws, transition (asKey 2#u64 1000#u64) s0 (.Admit gpt 10#u64 20#u64 (vecOf [100#u64])) =
        ok (.Ok (ws, .Admitted 11#u64 101#u64 50000#u64)) ∧
      ws.val = admitWrites (key 2#u64 UNL) 101#u64 50000#u64) ∧
    transition (asKey 2#u64 1000#u64) s0 (.Admit gpt 10#u64 20#u64 (vecOf [100#u64, 101#u64])) =
      ok (.Err .NoDeployment) := by
  constructor
  · apply ok_of_spec
    gw_admit [s0]
  · apply err_of_spec
    gw_admit [s0]

/-! ## 3. A cooling deployment is skipped -/

/-- Deployment 100 cools down until 2000. -/
def sCool : Snapshot := snap [key 2#u64 UNL] [dep 100#u64 0#u64 2000#u64, d101] [] []

theorem cooling_deployment_skipped :
    ∃ ws, transition (asKey 2#u64 1000#u64) sCool (.Admit gpt 10#u64 20#u64 (vecOf [])) =
        ok (.Ok (ws, .Admitted 11#u64 101#u64 50000#u64)) ∧
      ws.val = admitWrites (key 2#u64 UNL) 101#u64 50000#u64 := by
  apply ok_of_spec
  gw_admit [sCool]

/-! ## 4. Budgets count reservations -/

/-- Key 2's earlier call to deployment 100, admitted at 900, still holds 50000. -/
def res5 : Reservation := ⟨5#u64, 2#u64, 0#u64, 100#u64, 1#u64, 1000#u64, 2000#u64, 50000#u64, 900#u64⟩

/-- Key 2 has a budget of 80000 and spent nothing, but 50000 is reserved. -/
def sTight : Snapshot := snap [key 2#u64 80000#u64] [d100, d101] [] [res5]
/-- The same with an unlimited budget. -/
def sLoose : Snapshot := snap [key 2#u64 UNL] [d100, d101] [] [res5]

/-- Another call of up to 50000 would bring the reserved amount to 100000,
over the budget of 80000 although nothing is spent yet; with `UNLIMITED` the
same call is admitted. -/
theorem budget_counts_reservations :
    transition (asKey 2#u64 1000#u64) sTight (.Admit gpt 10#u64 20#u64 (vecOf [])) =
      ok (.Err .KeyBudgetExceeded) ∧
    (∃ ws, transition (asKey 2#u64 1000#u64) sLoose (.Admit gpt 10#u64 20#u64 (vecOf [])) =
        ok (.Ok (ws, .Admitted 11#u64 100#u64 50000#u64)) ∧
      ws.val = admitWrites (key 2#u64 UNL) 100#u64 50000#u64) := by
  constructor
  · apply err_of_spec
    gw_admit [sTight, res5]
  · apply ok_of_spec
    gw_admit [sLoose, res5]

/-! ## 5. Rate limits -/

/-- Key 2 may make 3 requests a minute and made 3 in window `w`. -/
def sBusy (w : U64) : Snapshot :=
  snap [{ key 2#u64 UNL with rpm := 3#u64 }] [d100, d101] [⟨0#u64, 2#u64, w, 3#u64, 0#u64⟩] []

/-- At time 1000 (window 16), 3 requests in window 16 hit the limit of 3;
3 requests in window 15 count for nothing. -/
theorem rate_limited :
    transition (asKey 2#u64 1000#u64) (sBusy 16#u64) (.Admit gpt 10#u64 20#u64 (vecOf [])) =
      ok (.Err .KeyRateLimited) ∧
    (∃ ws, transition (asKey 2#u64 1000#u64) (sBusy 15#u64) (.Admit gpt 10#u64 20#u64 (vecOf [])) =
        ok (.Ok (ws, .Admitted 11#u64 100#u64 50000#u64)) ∧
      ws.val = admitWrites { key 2#u64 UNL with rpm := 3#u64 } 100#u64 50000#u64) := by
  constructor
  · apply err_of_spec
    gw_admit [sBusy]
  · apply ok_of_spec
    gw_admit [sBusy]

/-! ## 6. Settlement charges the actual cost -/

h5i_derive_eq CallStatus CallStatus.Insts.CoreCmpPartialEqCallStatus.eq

/-- Key 2's call on deployment 100 holds reservation 5; key 3 is another key. -/
def sR : Snapshot := snap [key 2#u64 UNL, key 3#u64 UNL] [d100, d101] [] [res5]

/-- `sR` after reservation 5 settled at 1001 for 10 prompt and 5 completion tokens. -/
def sR' : Snapshot :=
  snap [{ key 2#u64 UNL with spend := 20000#u64 }, key 3#u64 UNL] [d100, d101]
    [⟨0#u64, 2#u64, 16#u64, 0#u64, 15#u64⟩, ⟨2#u64, 100#u64, 16#u64, 0#u64, 15#u64⟩] []

/-- The reservation goes, the key is charged 20000, the key's and the
deployment's token counters count 15, and the spend is logged. -/
def settleWrites : List Write :=
  [.DelReservation 5#u64, .PutKey { key 2#u64 UNL with spend := 20000#u64 },
    .PutUsage ⟨0#u64, 2#u64, 16#u64, 0#u64, 15#u64⟩, .PutUsage ⟨2#u64, 100#u64, 16#u64, 0#u64, 15#u64⟩,
    .Emit ⟨5#u64, 2#u64, 0#u64, 100#u64, 1#u64, 10#u64, 5#u64, 20000#u64, 1001#u64, .Success⟩]

macro "gw_settle" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  unfold transition settle may_close key_now
  gw_run [snap, dep, d100, d101, key, settings0, asKey, res5, IsAdmin, findKey, $ls,*]))

/-- Settling for 10 prompt and 5 completion tokens charges
`10 * 1000 + 5 * 2000 = 20000`, not the 50000 reserved. -/
theorem settle_charges_actual :
    ∃ ws, transition (asKey 2#u64 1001#u64) sR (.Settle 5#u64 10#u64 5#u64 .Success) =
        ok (.Ok (ws, .Settled 20000#u64)) ∧ ws.val = settleWrites := by
  apply ok_of_spec
  gw_settle [sR, settleWrites]

/-- Committing the settlement leads to `sR'`. -/
theorem settle_applies : applyAll (Snapshot.toSt sR) settleWrites = Snapshot.toSt sR' := by
  simp [applyAll, applyWrite, settleWrites, sR, sR', snap, Snapshot.toSt, vecOf, upsert, res5, key]

/-- A reservation settles once: on the state after the settlement it is gone. -/
theorem settle_twice :
    transition (asKey 2#u64 1002#u64) sR' (.Settle 5#u64 10#u64 5#u64 .Success) = ok (.Err .NotFound) := by
  apply err_of_spec
  gw_settle [sR']

/-- Key 3, not an admin, may not settle key 2's call. -/
theorem settle_other_key :
    transition (asKey 3#u64 1001#u64) sR (.Settle 5#u64 10#u64 5#u64 .Success) = ok (.Err .Forbidden) := by
  apply err_of_spec
  gw_settle [sR]

/-! ## 7. Keys cannot manage the gateway -/

def newKey : KeySpec := ⟨0#u64, 7#u64, 100000#u64, UNL, UNL, UNL, UNL, 0#u64, false, true⟩
def budgetPatch : KeyPatch := ⟨some 100000#u64, none, none, none, none, none, none, none⟩

/-- `create_key`'s loop over the granted models, with none granted. -/
@[local step] theorem create_key_loop1_nil (ids : alloc.vec.Vec U64) (h : ids.val = []) (id : U64)
    (ws : alloc.vec.Vec Write) : create_key_loop1 ids id ws 0#usize ⦃ r => r = ws ⦄ := by
  unfold create_key_loop1
  rw [loop.eq_def]
  simp [create_key_loop1.body, alloc.vec.Vec.len, h]

macro "gw_manage" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  unfold transition manage create_key update_key
  gw_run [snap, dep, d100, d101, key, settings0, asKey, master, IsAdmin, findKey, newKey, budgetPatch,
    resolveL, $ls,*]))

/-- Key 2 (not an admin) may neither create a key nor raise its own budget. -/
theorem key_cannot_manage :
    transition (asKey 2#u64 1000#u64) s0 (.CreateKey newKey (vecOf [])) = ok (.Err .Forbidden) ∧
    transition (asKey 2#u64 1000#u64) s0 (.UpdateKey 2#u64 budgetPatch) = ok (.Err .Forbidden) := by
  constructor
  · apply err_of_spec
    gw_manage [s0]
  · apply err_of_spec
    gw_manage [s0]

/-- The master key may do both: the new key gets id 11. -/
theorem master_manages :
    (∃ ws, transition (master 1000#u64) s0 (.CreateKey newKey (vecOf [])) = ok (.Ok (ws, .Created 11#u64)) ∧
      ws.val = [.PutKey ⟨11#u64, 0#u64, 7#u64, 100000#u64, 0#u64, UNL, UNL, UNL, UNL, 0#u64, 1000#u64,
          false, false, true⟩,
        .SetSettings ⟨11#u64, 1#u64, 30#u64, 600#u64⟩]) ∧
    (∃ ws, transition (master 1000#u64) s0 (.UpdateKey 2#u64 budgetPatch) = ok (.Ok (ws, .Done)) ∧
      ws.val = [.PutKey { key 2#u64 UNL with max_budget := 100000#u64 }]) := by
  constructor
  · apply ok_of_spec
    gw_manage [s0]
  · apply ok_of_spec
    gw_manage [s0]

/-! ## 8. Model access -/

/-- Key 2 is granted neither every model nor "gpt". -/
def sNoGrant : Snapshot := snap [{ key 2#u64 UNL with all_models := false }] [d100, d101] [] []

theorem model_not_allowed :
    transition (asKey 2#u64 1000#u64) sNoGrant (.Admit gpt 10#u64 20#u64 (vecOf [])) =
      ok (.Err .ModelNotAllowed) := by
  apply err_of_spec
  gw_admit [sNoGrant]

/-- No model group is named "nope". -/
theorem model_not_found :
    transition (asKey 2#u64 1000#u64) s0 (.Admit nope 10#u64 20#u64 (vecOf [])) =
      ok (.Err .ModelNotFound) := by
  apply err_of_spec
  gw_admit [s0]

/-! ## 9. Blocked and expired keys -/

def sBlocked : Snapshot := snap [{ key 2#u64 UNL with blocked := true }] [d100, d101] [] []
/-- Key 2 expires at 1000. -/
def sExpiring : Snapshot := snap [{ key 2#u64 UNL with expires_at := 1000#u64 }] [d100, d101] [] []

/-- A blocked key is refused; a key expiring at 1000 is refused at 1000 and
admitted at 999. -/
theorem blocked_and_expired :
    transition (asKey 2#u64 1000#u64) sBlocked (.Admit gpt 10#u64 20#u64 (vecOf [])) = ok (.Err .KeyBlocked) ∧
    transition (asKey 2#u64 1000#u64) sExpiring (.Admit gpt 10#u64 20#u64 (vecOf [])) = ok (.Err .KeyExpired) ∧
    (∃ ws, transition (asKey 2#u64 999#u64) sExpiring (.Admit gpt 10#u64 20#u64 (vecOf [])) =
        ok (.Ok (ws, .Admitted 11#u64 100#u64 50000#u64)) ∧
      ws.val = admitWrites { key 2#u64 UNL with expires_at := 1000#u64 } 100#u64 50000#u64 999#u64) := by
  refine ⟨?_, ?_, ?_⟩
  · apply err_of_spec
    gw_admit [sBlocked]
  · apply err_of_spec
    gw_admit [sExpiring]
  · apply ok_of_spec
    gw_admit [sExpiring]


end gateway_kernel.Scenarios
