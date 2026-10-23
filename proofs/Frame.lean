import Plan
import Theorems
/-!
# Frame theorem: the read plans load enough

`frame`: for every principal, snapshot and command with a plan,
`transition` on `Snapshot.load (readsA a c) s` (what the server loads,
`Schema.decode_load`) gives the same result, writes and reply or refusal,
as on the whole tenant `s`. For a `Batch` this needs that the snapshot keeps
the invariant (`Spec.Inv`: a new reservation id is fresh) and leaves room in
its vectors (`Commands.Fits`, as `transition_total`).

The argument has two layers.

* Slices (`Slice K st' st`): `st'` keeps, of each table of `st`, the rows a
  predicate `K` keeps, in order, and the same settings. Each lookup of the
  kernel answers on a slice as on the whole state when the slice keeps every
  row the lookup can return (`find_key_slice`, ..., `route_slice`), so each
  command does (`admit_slice`, `settle_slice`, ...) when the slice keeps the
  rows it reads (`KeyNeeds`, `SettleNeeds`, ...). Committing writes keeps a
  slice a slice as long as the rows written are rows `K` keeps (`slice_apply`).
* The plans: what `Snapshot.load` keeps of each table is a slice by the
  plan's predicates evaluated on `s` (`load_slice`), and those predicates keep
  what each command reads (`plan_*`). A batch runs its items on the states
  its earlier items leave; those states differ from `s`, but only in rows the
  plan keeps: every row an item writes is one the plan's predicates keep (the
  reservation an admission inserts has the item's key, the key and team rows
  it updates are the item key's), so each item runs on a slice of the full
  run's state (`lift_run`).
-/
open Classical Aeneas Aeneas.Std Result gateway_kernel gateway_kernel.Schema gateway_kernel.Spec gateway_kernel.Helpers
  gateway_kernel.Commands gateway_kernel.Plan H5iAppLib H5iAppLib.Query

namespace gateway_kernel.Frame

attribute [local simp] Schema.u64_val_eq

/-! ## Slices -/

/-- Which rows of each table a slice keeps. -/
structure Keep where
  teams : Team → Bool
  keys : Key → Bool
  models : Model → Bool
  deployments : Deployment → Bool
  keyModels : KeyModel → Bool
  teamModels : TeamModel → Bool
  usage : Usage → Bool
  reservations : Reservation → Bool

/-- `st'` holds the rows of `st` that `K` keeps, in the same order, and the
same settings. -/
structure Slice (K : Keep) (st' st : St) : Prop where
  settings : st'.settings = st.settings
  teams : st'.teams = st.teams.filter K.teams
  keys : st'.keys = st.keys.filter K.keys
  models : st'.models = st.models.filter K.models
  deployments : st'.deployments = st.deployments.filter K.deployments
  keyModels : st'.keyModels = st.keyModels.filter K.keyModels
  teamModels : st'.teamModels = st.teamModels.filter K.teamModels
  usage : st'.usage = st.usage.filter K.usage
  reservations : st'.reservations = st.reservations.filter K.reservations

/-- Two computations with deterministic postconditions that agree. -/
theorem det {α : Type} {m1 m2 : Result α} {P1 P2 : α → Prop} (h1 : m1 ⦃ P1 ⦄) (h2 : m2 ⦃ P2 ⦄)
    (hu : ∀ a b, P1 a → P2 b → a = b) : m1 = m2 := by
  obtain ⟨a, ha⟩ := ok_of h1
  obtain ⟨b, hb⟩ := ok_of h2
  rw [ha, hb, hu a b (post_of_ok h1 ha) (post_of_ok h2 hb)]

/-! ## Lookups on a slice -/

section Lookups
variable {K : Keep} {s' s : Snapshot} (hs : Slice K (Snapshot.toSt s') (Snapshot.toSt s))
include hs

theorem settings_eq : s'.settings = s.settings := hs.settings

theorem find_key_slice (id : U64) (hk : ∀ x ∈ s.keys.val, x.id = id → K.keys x = true) :
    find_key s'.keys id = find_key s.keys id := by
  rw [eq_ok_of_spec (find_key_spec _ _), eq_ok_of_spec (find_key_spec _ _)]
  have e : s'.keys.val = s.keys.val.filter K.keys := hs.keys
  rw [e, find?_slice _ _ _ (fun x hx hp => hk x hx (by simpa using hp))]

theorem find_team_slice (id : U64) (hk : ∀ x ∈ s.teams.val, x.id = id → K.teams x = true) :
    find_team s'.teams id = find_team s.teams id := by
  rw [eq_ok_of_spec (find_team_spec _ _), eq_ok_of_spec (find_team_spec _ _)]
  have e : s'.teams.val = s.teams.val.filter K.teams := hs.teams
  rw [e, find?_slice _ _ _ (fun x hx hp => hk x hx (by simpa using hp))]

theorem find_reservation_slice (id : U64) (hk : ∀ x ∈ s.reservations.val, x.id = id → K.reservations x = true) :
    find_reservation s'.reservations id = find_reservation s.reservations id := by
  rw [eq_ok_of_spec (find_reservation_spec _ _), eq_ok_of_spec (find_reservation_spec _ _)]
  have e : s'.reservations.val = s.reservations.val.filter K.reservations := hs.reservations
  rw [e, find?_slice _ _ _ (fun x hx hp => hk x hx (by simpa using hp))]

theorem find_model_slice (nm : alloc.vec.Vec U8) (hk : ∀ x ∈ s.models.val, x.name.val = nm.val → K.models x = true) :
    find_model s'.models nm = find_model s.models nm := by
  rw [eq_ok_of_spec (find_model_spec _ _), eq_ok_of_spec (find_model_spec _ _)]
  have e : s'.models.val = s.models.val.filter K.models := hs.models
  rw [e, find?_slice _ _ _ (fun x hx hp => hk x hx (by simpa using hp))]

theorem find_usage_slice (sc id : U64) (hk : ∀ u ∈ s.usage.val, u.scope = sc → u.id = id → K.usage u = true) :
    find_usage s'.usage sc id = find_usage s.usage sc id := by
  rw [eq_ok_of_spec (find_usage_spec _ _ _), eq_ok_of_spec (find_usage_spec _ _ _)]
  have e : s'.usage.val = s.usage.val.filter K.usage := hs.usage
  rw [e, find?_slice _ _ _ (fun u hu hp => by simp only [decide_eq_true_eq, Schema.u64_val_eq] at hp; exact hk u hu hp.1 hp.2)]

theorem used_slice (sc id : U64) (hk : ∀ u ∈ s.usage.val, u.scope = sc → u.id = id → K.usage u = true) (w : U64) :
    used s'.usage sc id w = used s.usage sc id w := by
  unfold used; rw [find_usage_slice hs sc id hk]

theorem count_request_slice (sc id : U64) (hk : ∀ u ∈ s.usage.val, u.scope = sc → u.id = id → K.usage u = true)
    (w : U64) : count_request s'.usage sc id w = count_request s.usage sc id w := by
  unfold count_request; rw [used_slice hs sc id hk]

theorem count_tokens_slice (sc id : U64) (hk : ∀ u ∈ s.usage.val, u.scope = sc → u.id = id → K.usage u = true)
    (w n : U64) : count_tokens s'.usage sc id w n = count_tokens s.usage sc id w n := by
  unfold count_tokens; rw [used_slice hs sc id hk]

theorem key_may_slice (key model : U64) (hk : ∀ g ∈ s.key_models.val, g.key = key → K.keyModels g = true) :
    key_may s'.key_models key model = key_may s.key_models key model := by
  apply det (key_may_spec _ _ _) (key_may_spec _ _ _)
  intro a b ha hb
  have e : s'.key_models.val = s.key_models.val.filter K.keyModels := hs.keyModels
  apply Bool.eq_iff_iff.2
  rw [ha, hb, e]
  constructor
  · rintro ⟨g, hg, h1, h2⟩; exact ⟨g, (List.mem_filter.1 hg).1, h1, h2⟩
  · rintro ⟨g, hg, h1, h2⟩; exact ⟨g, List.mem_filter.2 ⟨hg, hk g hg h1⟩, h1, h2⟩

theorem team_may_slice (team model : U64) (hk : ∀ g ∈ s.team_models.val, g.team = team → K.teamModels g = true) :
    team_may s'.team_models team model = team_may s.team_models team model := by
  apply det (team_may_spec _ _ _) (team_may_spec _ _ _)
  intro a b ha hb
  have e : s'.team_models.val = s.team_models.val.filter K.teamModels := hs.teamModels
  apply Bool.eq_iff_iff.2
  rw [ha, hb, e]
  constructor
  · rintro ⟨g, hg, h1, h2⟩; exact ⟨g, (List.mem_filter.1 hg).1, h1, h2⟩
  · rintro ⟨g, hg, h1, h2⟩; exact ⟨g, List.mem_filter.2 ⟨hg, hk g hg h1⟩, h1, h2⟩

theorem models_of_key_slice (key : U64) (hk : ∀ g ∈ s.key_models.val, g.key = key → K.keyModels g = true) :
    models_of_key s'.key_models key = models_of_key s.key_models key := by
  apply det (models_of_key_spec _ _) (models_of_key_spec _ _)
  intro a b ha hb
  have e : s'.key_models.val = s.key_models.val.filter K.keyModels := hs.keyModels
  apply alloc.vec.Vec.ext
  rw [ha, hb, e, filter_slice _ _ _ (fun g hg hp => hk g hg (by simpa using hp))]

theorem models_of_team_slice (team : U64) (hk : ∀ g ∈ s.team_models.val, g.team = team → K.teamModels g = true) :
    models_of_team s'.team_models team = models_of_team s.team_models team := by
  apply det (models_of_team_spec _ _) (models_of_team_spec _ _)
  intro a b ha hb
  have e : s'.team_models.val = s.team_models.val.filter K.teamModels := hs.teamModels
  apply alloc.vec.Vec.ext
  rw [ha, hb, e, filter_slice _ _ _ (fun g hg hp => hk g hg (by simpa using hp))]

theorem in_flight_slice (key : U64) (hk : ∀ r ∈ s.reservations.val, r.key_id = key → K.reservations r = true) :
    in_flight s'.reservations key = in_flight s.reservations key := by
  apply det (in_flight_spec _ _) (in_flight_spec _ _)
  intro a b ha hb
  have e : s'.reservations.val = s.reservations.val.filter K.reservations := hs.reservations
  apply (Schema.u64_val_eq _ _).1
  rw [ha, hb, e, filter_slice _ _ _ (fun r hr hp => hk r hr (by simpa using hp))]

theorem reserved_by_key_slice (key : U64) (hk : ∀ r ∈ s.reservations.val, r.key_id = key → K.reservations r = true) :
    reserved_by_key s'.reservations key = reserved_by_key s.reservations key := by
  apply det (reserved_by_key_spec _ _) (reserved_by_key_spec _ _)
  intro a b ha hb
  have e : s'.reservations.val = s.reservations.val.filter K.reservations := hs.reservations
  apply (Schema.u64_val_eq _ _).1
  rw [ha, hb, e, filter_slice _ _ _ (fun r hr hp => hk r hr (by simpa using hp))]

theorem reserved_by_team_slice (team : U64) (hk : ∀ r ∈ s.reservations.val, r.team = team → K.reservations r = true) :
    reserved_by_team s'.reservations team = reserved_by_team s.reservations team := by
  apply det (reserved_by_team_spec _ _) (reserved_by_team_spec _ _)
  intro a b ha hb
  have e : s'.reservations.val = s.reservations.val.filter K.reservations := hs.reservations
  apply (Schema.u64_val_eq _ _).1
  rw [ha, hb, e, filter_slice _ _ _ (fun r hr hp => hk r hr (by simpa using hp))]

theorem deployments_eq (hd : ∀ d ∈ s.deployments.val, K.deployments d = true) : s'.deployments = s.deployments := by
  apply alloc.vec.Vec.ext
  have e : s'.deployments.val = s.deployments.val.filter K.deployments := hs.deployments
  rw [e, List.filter_eq_self.2 hd]

theorem models_eq (hm : ∀ m ∈ s.models.val, K.models m = true) : s'.models = s.models := by
  apply alloc.vec.Vec.ext
  have e : s'.models.val = s.models.val.filter K.models := hs.models
  rw [e, List.filter_eq_self.2 hm]

theorem route_slice (hd : ∀ d ∈ s.deployments.val, K.deployments d = true)
    (hu : ∀ u ∈ s.usage.val, u.scope = 2#u64 → K.usage u = true) (m now : U64) (ex : alloc.vec.Vec U64) :
    route s'.deployments s'.usage m now ex = route s.deployments s.usage m now ex := by
  have hused : ∀ id w, used s'.usage SCOPE_DEPLOYMENT id w = used s.usage SCOPE_DEPLOYMENT id w :=
    fun id w => used_slice hs _ id (fun u hm h1 _ => hu u hm (by simpa [SCOPE_DEPLOYMENT] using h1)) w
  have helig : ∀ d m now ex, eligible d s'.usage m now ex = eligible d s.usage m now ex := by
    intro d m now ex; unfold eligible; simp only [hused]
  rw [deployments_eq hs hd]
  unfold route route_loop route_loop.body
  simp only [helig, hused]

theorem may_call_slice (k : Key) (t : Option Team) (m : U64)
    (hkm : ∀ g ∈ s.key_models.val, g.key = k.id → K.keyModels g = true)
    (htm : ∀ team, t = some team → ∀ g ∈ s.team_models.val, g.team = team.id → K.teamModels g = true) :
    may_call s' k t m = may_call s k t m := by
  unfold may_call
  rw [key_may_slice hs _ _ hkm]
  cases t with
  | none => rfl
  | some team =>
    simp only []
    rw [team_may_slice hs _ _ (htm team rfl)]

theorem is_admin_slice (a : Principal) (hk : a.master = false → ∀ x ∈ s.keys.val, x.id = a.key → K.keys x = true) :
    is_admin a s' = is_admin a s := by
  unfold is_admin
  cases hm : a.master
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [find_key_slice hs _ (hk hm)]
  · rfl

theorem fresh_slice : fresh s' = fresh s := by
  unfold fresh; rw [settings_eq hs]

theorem may_close_slice (a : Principal) (r : Reservation)
    (hk : a.master = false → ∀ x ∈ s.keys.val, x.id = a.key → K.keys x = true) :
    may_close a s' r = may_close a s r := by
  unfold may_close; rw [is_admin_slice hs a hk]

end Lookups

/-! ## Commands on a slice -/

/-- What every admission and settlement reads of the deployments: all of
them, and their usage counters. -/
structure Common (K : Keep) (s : Snapshot) : Prop where
  deployments : ∀ d ∈ s.deployments.val, K.deployments d = true
  dep_usage : ∀ u ∈ s.usage.val, u.scope = 2#u64 → K.usage u = true

/-- What an admission by key `kid` reads beyond `Common`: the key and, if
it exists, its grants, its team and the team's grants, their counters, and
their reservations. -/
structure KeyNeeds (K : Keep) (s : Snapshot) (kid : U64) : Prop where
  key : ∀ x ∈ s.keys.val, x.id = kid → K.keys x = true
  grants : ∀ k ∈ s.keys.val, k.id = kid → ∀ g ∈ s.key_models.val, g.key = k.id → K.keyModels g = true
  team : ∀ k ∈ s.keys.val, k.id = kid → ∀ x ∈ s.teams.val, x.id = k.team → K.teams x = true
  team_grants : ∀ k ∈ s.keys.val, k.id = kid → ∀ g ∈ s.team_models.val, g.team = k.team → K.teamModels g = true
  key_usage : ∀ k ∈ s.keys.val, k.id = kid → ∀ u ∈ s.usage.val, u.scope = 0#u64 → u.id = k.id → K.usage u = true
  team_usage : ∀ k ∈ s.keys.val, k.id = kid → ∀ u ∈ s.usage.val, u.scope = 1#u64 → u.id = k.team → K.usage u = true
  key_res : ∀ k ∈ s.keys.val, k.id = kid → ∀ r ∈ s.reservations.val, r.key_id = k.id → K.reservations r = true
  team_res : ∀ k ∈ s.keys.val, k.id = kid → ∀ t ∈ s.teams.val, t.id = k.team →
    ∀ r ∈ s.reservations.val, r.team = t.id → K.reservations r = true

/-- What a settlement or expiry of reservation `rid` by `a` reads beyond
`Common`: the reservation, the caller's key (is it an admin?), and the
reservation's key and team and their counters. -/
structure SettleNeeds (K : Keep) (s : Snapshot) (a : Principal) (rid : U64) : Prop where
  res : ∀ r ∈ s.reservations.val, r.id = rid → K.reservations r = true
  caller : a.master = false → ∀ x ∈ s.keys.val, x.id = a.key → K.keys x = true
  key : ∀ r ∈ s.reservations.val, r.id = rid → r.key_id ≠ 0#u64 → ∀ x ∈ s.keys.val, x.id = r.key_id → K.keys x = true
  key_usage : ∀ r ∈ s.reservations.val, r.id = rid → r.key_id ≠ 0#u64 →
    ∀ u ∈ s.usage.val, u.scope = 0#u64 → u.id = r.key_id → K.usage u = true
  team : ∀ r ∈ s.reservations.val, r.id = rid → r.team ≠ 0#u64 → ∀ x ∈ s.teams.val, x.id = r.team → K.teams x = true
  team_usage : ∀ r ∈ s.reservations.val, r.id = rid → r.team ≠ 0#u64 →
    ∀ u ∈ s.usage.val, u.scope = 1#u64 → u.id = r.team → K.usage u = true

theorem team_now_id (t : Team) (now : U64) (t2 : Team) (h : team_now t now = ok t2) : t2.id = t.id := by
  have := (post_of_ok (team_now_spec t now) h).2.2
  rw [this]

theorem bne_false {x : U64} (h : x = 0#u64) : (x != 0#u64) = false := by simp [h]
theorem bne_true {x : U64} (h : ¬ x = 0#u64) : (x != 0#u64) = true := by simpa using h

section Commands
variable {K : Keep} {s' s : Snapshot} (hs : Slice K (Snapshot.toSt s') (Snapshot.toSt s))
include hs

theorem dep_count_request (hc : Common K s) (id w : U64) :
    count_request s'.usage SCOPE_DEPLOYMENT id w = count_request s.usage SCOPE_DEPLOYMENT id w :=
  count_request_slice hs _ id (fun u hm h1 _ => hc.dep_usage u hm (by simpa [SCOPE_DEPLOYMENT] using h1)) w

theorem dep_count_tokens (hc : Common K s) (id w n : U64) :
    count_tokens s'.usage SCOPE_DEPLOYMENT id w n = count_tokens s.usage SCOPE_DEPLOYMENT id w n :=
  count_tokens_slice hs _ id (fun u hm h1 _ => hc.dep_usage u hm (by simpa [SCOPE_DEPLOYMENT] using h1)) w n

theorem admit_master_slice (a : Principal) (m pt mt : U64) (ex : alloc.vec.Vec U64) (hc : Common K s) :
    admit_master a s' m pt mt ex = admit_master a s m pt mt ex := by
  unfold admit_master
  rw [route_slice hs hc.deployments hc.dep_usage, fresh_slice hs]
  simp only [dep_count_request hs hc, settings_eq hs]

theorem admit_key_slice (a : Principal) (m pt mt : U64) (ex : alloc.vec.Vec U64) (hc : Common K s)
    (hn : KeyNeeds K s a.key) : admit_key a s' m pt mt ex = admit_key a s m pt mt ex := by
  unfold admit_key
  obtain ⟨w, hw⟩ := ok_of (window_of_spec a.now)
  rw [hw, find_key_slice hs _ hn.key, eq_ok_of_spec (find_key_spec s.keys a.key)]
  simp only [bind_tc_ok, bind_ok]
  cases hk : s.keys.val.find? (fun k => decide (k.id.val = a.key.val)) with
  | none => rfl
  | some k =>
    obtain ⟨hkm, hkp⟩ := find?_mem hk
    have hkid : k.id = a.key := by simpa using hkp
    have hku : ∀ u ∈ s.usage.val, u.scope = SCOPE_KEY → u.id = k.id → K.usage u = true := by
      intro u hu h1 h2; exact hn.key_usage k hkm hkid u hu (by simpa [SCOPE_KEY] using h1) h2
    simp only []
    rw [route_slice hs hc.deployments hc.dep_usage, fresh_slice hs, used_slice hs _ _ hku,
      in_flight_slice hs _ (hn.key_res k hkm hkid), reserved_by_key_slice hs _ (hn.key_res k hkm hkid),
      count_request_slice hs _ _ hku]
    simp only [dep_count_request hs hc, settings_eq hs]
    by_cases h0 : k.team = 0#u64
    · simp only [if_pos h0]
      rw [may_call_slice hs k none m (hn.grants k hkm hkid) (fun _ h => by cases h)]
    · simp only [if_neg h0]
      rw [find_team_slice hs _ (hn.team k hkm hkid), eq_ok_of_spec (find_team_spec s.teams k.team)]
      simp only [bind_tc_ok, bind_ok]
      cases ht : s.teams.val.find? (fun t => decide (t.id.val = k.team.val)) with
      | none => rfl
      | some t =>
        obtain ⟨htm, htp⟩ := find?_mem ht
        have htid : t.id = k.team := by simpa using htp
        have htu : ∀ u ∈ s.usage.val, u.scope = SCOPE_TEAM → u.id = t.id → K.usage u = true := by
          intro u hu h1 h2; exact hn.team_usage k hkm hkid u hu (by simpa [SCOPE_TEAM] using h1) (h2.trans htid)
        simp only []
        obtain ⟨t2, ht2⟩ := ok_of (team_now_spec t a.now)
        rw [may_call_slice hs k (some t) m (hn.grants k hkm hkid) (fun team h g hg hgt => by
              cases h; exact hn.team_grants k hkm hkid g hg (hgt.trans htid)),
          used_slice hs _ _ htu, reserved_by_team_slice hs _ (fun r hr hrt => hn.team_res k hkm hkid t htm htid r hr hrt),
          ht2]
        simp only [bind_tc_ok, bind_ok]
        rw [team_now_id t a.now t2 ht2, count_request_slice hs _ _ htu]

theorem admit_slice (a : Principal) (nm : alloc.vec.Vec U8) (pt mt : U64) (ex : alloc.vec.Vec U64) (hc : Common K s)
    (hm : ∀ x ∈ s.models.val, x.name.val = nm.val → K.models x = true) (hn : a.master = false → KeyNeeds K s a.key) :
    admit a s' nm pt mt ex = admit a s nm pt mt ex := by
  unfold admit
  rw [find_model_slice hs nm hm]
  cases hma : a.master
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [admit_key_slice hs a _ pt mt ex hc (hn hma)]
  · simp only [↓reduceIte]
    simp only [admit_master_slice hs a _ pt mt ex hc]


theorem settle_slice (a : Principal) (rid pt ct : U64) (st : CallStatus) (hc : Common K s)
    (hn : SettleNeeds K s a rid) : settle a s' rid pt ct st = settle a s rid pt ct st := by
  unfold settle
  rw [find_reservation_slice hs _ hn.res, eq_ok_of_spec (find_reservation_spec s.reservations rid)]
  simp only [bind_tc_ok, bind_ok]
  cases hr : s.reservations.val.find? (fun r => decide (r.id.val = rid.val)) with
  | none => rfl
  | some r =>
    obtain ⟨hrm, hrp⟩ := find?_mem hr
    have hrid : r.id = rid := by simpa using hrp
    simp only []
    rw [may_close_slice hs a r hn.caller, deployments_eq hs hc.deployments]
    simp only [dep_count_tokens hs hc, settings_eq hs]
    by_cases hk0 : r.key_id = 0#u64
    · simp only [bne_false hk0, Bool.false_eq_true, ↓reduceIte]
      by_cases ht0 : r.team = 0#u64
      · simp only [bne_false ht0, Bool.false_eq_true, ↓reduceIte]
      · simp only [bne_true ht0, ↓reduceIte]
        rw [find_team_slice hs _ (hn.team r hrm hrid ht0), eq_ok_of_spec (find_team_spec s.teams r.team)]
        simp only [bind_tc_ok, bind_ok]
        cases ht : s.teams.val.find? (fun t => decide (t.id.val = r.team.val)) with
        | none => rfl
        | some t =>
          obtain ⟨-, htp⟩ := find?_mem ht
          have htid : t.id = r.team := by simpa using htp
          simp only []
          simp only [count_tokens_slice hs SCOPE_TEAM t.id (fun u hu h1 h2 =>
            hn.team_usage r hrm hrid ht0 u hu (by simpa [SCOPE_TEAM] using h1) (h2.trans htid))]
    · simp only [bne_true hk0, ↓reduceIte]
      rw [find_key_slice hs _ (hn.key r hrm hrid hk0), eq_ok_of_spec (find_key_spec s.keys r.key_id)]
      simp only [bind_tc_ok, bind_ok]
      have hkey : ∀ k : Key, k.id = r.key_id → ∀ w n,
          count_tokens s'.usage SCOPE_KEY k.id w n = count_tokens s.usage SCOPE_KEY k.id w n := by
        intro k hkid w n
        exact count_tokens_slice hs SCOPE_KEY k.id (fun u hu h1 h2 =>
          hn.key_usage r hrm hrid hk0 u hu (by simpa [SCOPE_KEY] using h1) (h2.trans hkid)) w n
      cases hk : s.keys.val.find? (fun k => decide (k.id.val = r.key_id.val)) with
      | none =>
        by_cases ht0 : r.team = 0#u64
        · simp only [bne_false ht0, Bool.false_eq_true, ↓reduceIte]
        · simp only [bne_true ht0, ↓reduceIte]
          rw [find_team_slice hs _ (hn.team r hrm hrid ht0), eq_ok_of_spec (find_team_spec s.teams r.team)]
          simp only [bind_tc_ok, bind_ok]
          cases ht : s.teams.val.find? (fun t => decide (t.id.val = r.team.val)) with
          | none => rfl
          | some t =>
            obtain ⟨-, htp⟩ := find?_mem ht
            have htid : t.id = r.team := by simpa using htp
            simp only []
            simp only [count_tokens_slice hs SCOPE_TEAM t.id (fun u hu h1 h2 =>
              hn.team_usage r hrm hrid ht0 u hu (by simpa [SCOPE_TEAM] using h1) (h2.trans htid))]
      | some k =>
        obtain ⟨-, hkp⟩ := find?_mem hk
        have hkid : k.id = r.key_id := by simpa using hkp
        simp only []
        simp only [hkey k hkid]
        by_cases ht0 : r.team = 0#u64
        · simp only [bne_false ht0, Bool.false_eq_true, ↓reduceIte]
        · simp only [bne_true ht0, ↓reduceIte]
          rw [find_team_slice hs _ (hn.team r hrm hrid ht0), eq_ok_of_spec (find_team_spec s.teams r.team)]
          simp only [bind_tc_ok, bind_ok]
          cases ht : s.teams.val.find? (fun t => decide (t.id.val = r.team.val)) with
          | none => rfl
          | some t =>
            obtain ⟨-, htp⟩ := find?_mem ht
            have htid : t.id = r.team := by simpa using htp
            simp only []
            simp only [count_tokens_slice hs SCOPE_TEAM t.id (fun u hu h1 h2 =>
              hn.team_usage r hrm hrid ht0 u hu (by simpa [SCOPE_TEAM] using h1) (h2.trans htid))]

theorem expire_slice (a : Principal) (rid : U64) (hn : SettleNeeds K s a rid) :
    expire a s' rid = expire a s rid := by
  unfold expire
  rw [find_reservation_slice hs _ hn.res, eq_ok_of_spec (find_reservation_spec s.reservations rid)]
  simp only [bind_tc_ok, bind_ok]
  cases hr : s.reservations.val.find? (fun r => decide (r.id.val = rid.val)) with
  | none => rfl
  | some r =>
    simp only []
    rw [may_close_slice hs a r hn.caller, settings_eq hs]

theorem key_info_slice (a : Principal) (id : U64)
    (hcaller : a.master = false → ∀ x ∈ s.keys.val, x.id = a.key → K.keys x = true)
    (hkey : ∀ x ∈ s.keys.val, x.id = id → K.keys x = true)
    (hgrants : ∀ g ∈ s.key_models.val, g.key = id → K.keyModels g = true)
    (hres : ∀ r ∈ s.reservations.val, r.key_id = id → K.reservations r = true) :
    key_info a s' id = key_info a s id := by
  unfold key_info
  rw [is_admin_slice hs a hcaller, find_key_slice hs id hkey, models_of_key_slice hs id hgrants,
    reserved_by_key_slice hs id hres]

theorem team_info_slice (a : Principal) (id : U64)
    (hcaller : a.master = false → ∀ x ∈ s.keys.val, x.id = a.key → K.keys x = true)
    (hteam : ∀ x ∈ s.teams.val, x.id = id → K.teams x = true)
    (hgrants : ∀ g ∈ s.team_models.val, g.team = id → K.teamModels g = true)
    (hres : ∀ t ∈ s.teams.val, t.id = id → ∀ r ∈ s.reservations.val, r.team = id → K.reservations r = true) :
    team_info a s' id = team_info a s id := by
  unfold team_info
  rw [is_admin_slice hs a hcaller, find_team_slice hs id hteam, models_of_team_slice hs id hgrants,
    eq_ok_of_spec (find_team_spec s.teams id)]
  simp only [bind_tc_ok, bind_ok]
  cases hm : a.master
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [find_key_slice hs _ (hcaller hm)]
    cases ht : s.teams.val.find? (fun t => decide (t.id.val = id.val)) with
    | none => rfl
    | some t =>
      obtain ⟨htm, htp⟩ := find?_mem ht
      simp only []
      rw [reserved_by_team_slice hs id (hres t htm (by simpa using htp))]
  · simp only [↓reduceIte]
    cases ht : s.teams.val.find? (fun t => decide (t.id.val = id.val)) with
    | none => rfl
    | some t =>
      obtain ⟨htm, htp⟩ := find?_mem ht
      simp only []
      rw [reserved_by_team_slice hs id (hres t htm (by simpa using htp))]

theorem list_models_loop_slice (k : Key) (team : Option Team) (out : alloc.vec.Vec Model) (i : Usize)
    (hkm : ∀ g ∈ s.key_models.val, g.key = k.id → K.keyModels g = true)
    (htm : ∀ t, team = some t → ∀ g ∈ s.team_models.val, g.team = t.id → K.teamModels g = true) :
    list_models_loop s'.settings s'.teams s'.keys s.models s'.deployments s'.key_models s'.team_models s'.usage
        s'.reservations k.id k.team k.user k.max_budget k.spend k.rpm k.tpm k.max_parallel k.expires_at
        k.budget_duration k.budget_reset_at k.blocked k.admin k.all_models team out i =
      list_models_loop s.settings s.teams s.keys s.models s.deployments s.key_models s.team_models s.usage
        s.reservations k.id k.team k.user k.max_budget k.spend k.rpm k.tpm k.max_parallel k.expires_at
        k.budget_duration k.budget_reset_at k.blocked k.admin k.all_models team out i := by
  have hmc : ∀ x, may_call s' k team x = may_call s k team x := fun x => may_call_slice hs k team x hkm htm
  have hmc' : ∀ x, may_call ⟨s'.settings, s'.teams, s'.keys, s.models, s'.deployments, s'.key_models,
        s'.team_models, s'.usage, s'.reservations⟩
      ⟨k.id, k.team, k.user, k.max_budget, k.spend, k.rpm, k.tpm, k.max_parallel, k.expires_at, k.budget_duration,
        k.budget_reset_at, k.blocked, k.admin, k.all_models⟩ team x =
      may_call ⟨s.settings, s.teams, s.keys, s.models, s.deployments, s.key_models, s.team_models, s.usage,
        s.reservations⟩
      ⟨k.id, k.team, k.user, k.max_budget, k.spend, k.rpm, k.tpm, k.max_parallel, k.expires_at, k.budget_duration,
        k.budget_reset_at, k.blocked, k.admin, k.all_models⟩ team x := by
    intro x
    have h1 := hmc x
    unfold may_call at h1 ⊢
    exact h1
  unfold list_models_loop list_models_loop.body
  simp only [hmc']

theorem list_models_slice (a : Principal)
    (hcaller : a.master = false → ∀ x ∈ s.keys.val, x.id = a.key → K.keys x = true)
    (hm : ∀ m ∈ s.models.val, K.models m = true)
    (hkm : a.master = false → ∀ k ∈ s.keys.val, k.id = a.key → ∀ g ∈ s.key_models.val, g.key = k.id → K.keyModels g = true)
    (hteam : a.master = false → ∀ k ∈ s.keys.val, k.id = a.key → ∀ x ∈ s.teams.val, x.id = k.team → K.teams x = true)
    (htm : a.master = false → ∀ k ∈ s.keys.val, k.id = a.key →
      ∀ g ∈ s.team_models.val, g.team = k.team → K.teamModels g = true) :
    list_models a s' = list_models a s := by
  unfold list_models
  rw [is_admin_slice hs a hcaller, models_eq hs hm]
  cases hma : a.master
  · rw [find_key_slice hs _ (hcaller hma), eq_ok_of_spec (find_key_spec s.keys a.key)]
    simp only [bind_tc_ok, bind_ok]
    cases hk : s.keys.val.find? (fun k => decide (k.id.val = a.key.val)) with
    | none => rfl
    | some k =>
      obtain ⟨hkm', hkp⟩ := find?_mem hk
      have hkid : k.id = a.key := by simpa using hkp
      simp only []
      by_cases h0 : k.team = 0#u64
      · simp only [if_pos h0]; simp only [bind_ok]
        rw [list_models_loop_slice hs k none _ _ (hkm hma k hkm' hkid) (fun _ h => by cases h)]
      · simp only [if_neg h0]
        rw [find_team_slice hs _ (hteam hma k hkm' hkid), eq_ok_of_spec (find_team_spec s.teams k.team)]
        simp only [bind_tc_ok, bind_ok]
        rw [list_models_loop_slice hs k _ _ _ (hkm hma k hkm' hkid) (fun t h g hg hgt => by
          obtain ⟨-, htp⟩ := find?_mem h
          exact htm hma k hkm' hkid g hg (hgt.trans (by simpa using htp)))]
  · have : is_admin a s = ok true := by unfold is_admin; simp [hma]
    rw [this]
    simp only [bind_ok, ↓reduceIte]

end Commands


/-! ## Writes on a slice -/

/-- A write whose row `K` keeps, as it keeps every row of the current table
with the same key (so the slice follows the table's row order). -/
def Kept (K : Keep) (st : St) : Write → Prop
  | .PutTeam x => K.teams x = true ∧ ∀ y ∈ st.teams, y.id = x.id → K.teams y = true
  | .PutKey x => K.keys x = true ∧ ∀ y ∈ st.keys, y.id = x.id → K.keys y = true
  | .PutModel x => K.models x = true ∧ ∀ y ∈ st.models, y.id = x.id → K.models y = true
  | .PutDeployment x => K.deployments x = true ∧ ∀ y ∈ st.deployments, y.id = x.id → K.deployments y = true
  | .PutKeyModel x => K.keyModels x = true ∧
      ∀ y ∈ st.keyModels, (y.key, y.model) = (x.key, x.model) → K.keyModels y = true
  | .PutTeamModel x => K.teamModels x = true ∧
      ∀ y ∈ st.teamModels, (y.team, y.model) = (x.team, x.model) → K.teamModels y = true
  | .PutUsage x => K.usage x = true ∧ ∀ y ∈ st.usage, (y.scope, y.id) = (x.scope, x.id) → K.usage y = true
  | .PutReservation x => K.reservations x = true ∧ ∀ y ∈ st.reservations, y.id = x.id → K.reservations y = true
  | _ => True

theorem upsert_filter {α κ : Type} [DecidableEq κ] (key : α → κ) (P : α → Bool) (x : α) (l : List α)
    (hx : P x = true) (hl : ∀ y ∈ l, key y = key x → P y = true) :
    (H5iAppLib.upsert key x l).filter P = H5iAppLib.upsert key x (l.filter P) := by
  induction l with
  | nil => simp [H5iAppLib.upsert, hx]
  | cons y ys ih =>
    have ih' := ih (fun z hz => hl z (List.mem_cons_of_mem _ hz))
    by_cases hk : key y = key x
    · have hy := hl y (by simp) hk
      simp [H5iAppLib.upsert, hk, hx, hy]
    · by_cases hy : P y = true
      · simp [H5iAppLib.upsert, hk, hy, ih']
      · simp only [Bool.not_eq_true] at hy
        simp [H5iAppLib.upsert, hk, hy, ih']

theorem filter_comm {α : Type} (l : List α) (p q : α → Bool) : (l.filter q).filter p = (l.filter p).filter q := by
  simp only [List.filter_filter, Bool.and_comm]

theorem slice_applyWrite {K : Keep} {st' st : St} (hs : Slice K st' st) (w : Write) (hk : Kept K st w) :
    Slice K (applyWrite st' w) (applyWrite st w) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  cases w <;> simp only [applyWrite, Kept] at hk ⊢
  case SetSettings x => exact ⟨rfl, h1, h2, h3, h4, h5, h6, h7, h8⟩
  case PutTeam x => exact ⟨h0, by rw [h1, upsert_filter _ _ _ _ hk.1 hk.2], h2, h3, h4, h5, h6, h7, h8⟩
  case DelTeam id => exact ⟨h0, by rw [h1, filter_comm], h2, h3, h4, h5, h6, h7, h8⟩
  case PutKey x => exact ⟨h0, h1, by rw [h2, upsert_filter _ _ _ _ hk.1 hk.2], h3, h4, h5, h6, h7, h8⟩
  case DelKey id => exact ⟨h0, h1, by rw [h2, filter_comm], h3, h4, h5, h6, h7, h8⟩
  case PutModel x => exact ⟨h0, h1, h2, by rw [h3, upsert_filter _ _ _ _ hk.1 hk.2], h4, h5, h6, h7, h8⟩
  case PutDeployment x => exact ⟨h0, h1, h2, h3, by rw [h4, upsert_filter _ _ _ _ hk.1 hk.2], h5, h6, h7, h8⟩
  case DelDeployment id => exact ⟨h0, h1, h2, h3, by rw [h4, filter_comm], h5, h6, h7, h8⟩
  case PutKeyModel x => exact ⟨h0, h1, h2, h3, h4, by rw [h5, upsert_filter _ _ _ _ hk.1 hk.2], h6, h7, h8⟩
  case DelKeyModel k m => exact ⟨h0, h1, h2, h3, h4, by rw [h5, filter_comm], h6, h7, h8⟩
  case PutTeamModel x => exact ⟨h0, h1, h2, h3, h4, h5, by rw [h6, upsert_filter _ _ _ _ hk.1 hk.2], h7, h8⟩
  case DelTeamModel t m => exact ⟨h0, h1, h2, h3, h4, h5, by rw [h6, filter_comm], h7, h8⟩
  case PutUsage x => exact ⟨h0, h1, h2, h3, h4, h5, h6, by rw [h7, upsert_filter _ _ _ _ hk.1 hk.2], h8⟩
  case PutReservation x => exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, by rw [h8, upsert_filter _ _ _ _ hk.1 hk.2]⟩
  case DelReservation id => exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, by rw [h8, filter_comm]⟩
  case Emit l => exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Every write of a list is `Kept` where it applies. -/
def AllKept (K : Keep) : St → List Write → Prop
  | _, [] => True
  | st, w :: ws => Kept K st w ∧ AllKept K (applyWrite st w) ws

theorem slice_applyAll {K : Keep} : ∀ (ws : List Write) {st' st : St}, Slice K st' st → AllKept K st ws →
    Slice K (applyAll st' ws) (applyAll st ws)
  | [], _, _, hs, _ => hs
  | w :: ws, _, _, hs, ⟨h1, h2⟩ => slice_applyAll ws (slice_applyWrite hs w h1) h2

/-- What a batch item writes, in terms that do not depend on the state:
the rows it puts are rows `K` keeps, with every row of the same key, and it
never writes grants or models. (Reservations are handled apart: a new one is
fresh.) -/
def KeptU (K : Keep) : Write → Prop
  | .PutTeam x => ∀ y : Team, y.id = x.id → K.teams y = true
  | .PutKey x => ∀ y : Key, y.id = x.id → K.keys y = true
  | .PutDeployment x => ∀ y : Deployment, y.id = x.id → K.deployments y = true
  | .PutUsage x => ∀ y : Usage, y.scope = x.scope → y.id = x.id → K.usage y = true
  | .PutModel _ | .PutKeyModel _ | .PutTeamModel _ | .PutReservation _ | .DelReservation _ => False
  | _ => True

theorem kept_of_keptU {K : Keep} (st : St) (w : Write) (h : KeptU K w) : Kept K st w := by
  cases w <;> simp only [KeptU, Kept] at h ⊢ <;> first
    | trivial
    | exact absurd h id
    | exact ⟨h _ rfl, fun y _ hy => h y hy⟩
    | exact ⟨h _ rfl rfl, fun y _ hy => h y (Prod.mk.inj hy).1 (Prod.mk.inj hy).2⟩

theorem keptU_res {K : Keep} {w : Write} (h : KeptU K w) : ∀ st : St, (applyWrite st w).reservations = st.reservations := by
  intro st; cases w <;> simp only [KeptU] at h <;> first | exact absurd h id | rfl

theorem allKept_univ {K : Keep} : ∀ (ws : List Write), (∀ w ∈ ws, KeptU K w) → ∀ st, AllKept K st ws
  | [], _, _ => trivial
  | w :: ws, h, st => ⟨kept_of_keptU st w (h w (by simp)), allKept_univ ws (fun x hx => h x (by simp [hx])) _⟩

theorem allKept_univ_del {K : Keep} : ∀ (ws : List Write),
    (∀ w ∈ ws, KeptU K w ∨ (∃ id, w = .DelReservation id)) → ∀ st, AllKept K st ws
  | [], _, _ => trivial
  | w :: ws, h, st => by
    refine ⟨?_, allKept_univ_del ws (fun x hx => h x (by simp [hx])) _⟩
    rcases h w (by simp) with hw | ⟨id, rfl⟩
    · exact kept_of_keptU st w hw
    · trivial

theorem allKept_append_univ {K : Keep} : ∀ (pre : List Write) (rest : List Write) (st : St),
    (∀ w ∈ pre, KeptU K w) → AllKept K (applyAll st pre) rest → AllKept K st (pre ++ rest)
  | [], rest, st, _, h => h
  | w :: pre, rest, st, hp, h =>
    ⟨kept_of_keptU st w (hp w (by simp)), allKept_append_univ pre rest _ (fun x hx => hp x (by simp [hx])) h⟩

theorem applyAll_res_univ {K : Keep} : ∀ (pre : List Write) (st : St), (∀ w ∈ pre, KeptU K w) →
    (applyAll st pre).reservations = st.reservations
  | [], _, _ => rfl
  | w :: pre, st, hp => by
    rw [show applyAll st (w :: pre) = applyAll (applyWrite st w) pre from rfl,
      applyAll_res_univ pre _ (fun x hx => hp x (by simp [hx])), keptU_res (hp w (by simp)) st]

/-! ## What a plan keeps

`keepA` is what `Snapshot.load` of `planA` keeps of each table (`load_slice`):
the plan's predicates evaluated on the snapshot's encoded rows. `plan_keep`
reads them back as facts about rows (`PlanKeep`). -/

/-- The rows the plan `planA ks ts rs ns m0 allm` keeps of each table of `s`. -/
noncomputable def keepA (s : Snapshot) (ks ts rs : List U64) (ns : List (alloc.vec.Vec U8)) (m0 allm : Bool) : Keep where
  teams x := (teamsA ks ts rs).holds (Snapshot.enc s) (Team.row x)
  keys x := (keysA ks rs).holds (Snapshot.enc s) (Key.row x)
  models x := (if allm then .all else namesA ns : Pred Val).holds (Snapshot.enc s) (Model.row x)
  deployments x := (Pred.all : Pred Val).holds (Snapshot.enc s) (Deployment.row x)
  keyModels x := (armsA noneA 0 none .Id ks).holds (Snapshot.enc s) (KeyModel.row x)
  teamModels x := (teamModelsA ks ts).holds (Snapshot.enc s) (TeamModel.row x)
  usage x := (usageA ks ts rs).holds (Snapshot.enc s) (Usage.row x)
  reservations x := (reservationsA ks ts rs m0).holds (Snapshot.enc s) (Reservation.row x)

theorem load_slice (s : Snapshot) (ks ts rs : List U64) (ns : List (alloc.vec.Vec U8)) (m0 allm : Bool) :
    Slice (keepA s ks ts rs ns m0 allm) (Snapshot.toSt (Snapshot.load (planA ks ts rs ns m0 allm) s))
      (Snapshot.toSt s) := by
  constructor <;> simp [Snapshot.toSt, Snapshot.load, pickVec, pickRows, planA, keepA, Pred.holds]

@[simp] theorem holds_eq (tabs : H5iAppLib.Sql.Tables Val) (c : Nat) (v : Val) (r : List Val) :
    (Pred.eq c v).holds tabs r = decide (r[c]? = some v) := rfl

@[simp] theorem holds_all (tabs : H5iAppLib.Sql.Tables Val) (r : List Val) :
    (Pred.all : Pred Val).holds tabs r = true := rfl

@[simp] theorem holds_or (tabs : H5iAppLib.Sql.Tables Val) (p q : Pred Val) (r : List Val) :
    (Pred.or p q).holds tabs r = (p.holds tabs r || q.holds tabs r) := rfl

@[simp] theorem holds_and (tabs : H5iAppLib.Sql.Tables Val) (p q : Pred Val) (r : List Val) :
    (Pred.and p q).holds tabs r = (p.holds tabs r && q.holds tabs r) := rfl

theorem holds_armsA (tabs : H5iAppLib.Sql.Tables Val) (p : Pred Val) (c : Nat) (sc : Option U64) (via : Via)
    (ids : List U64) (r : List Val) :
    (armsA p c sc via ids).holds tabs r = (p.holds tabs r || ids.any (fun x => (armA c sc via x).holds tabs r)) := by
  induction ids generalizing p with
  | nil => simp [armsA]
  | cons x xs ih =>
    have : armsA p c sc via (x :: xs) = armsA (.or p (armA c sc via x)) c sc via xs := rfl
    rw [this, ih]; simp [Bool.or_assoc]

/-- An arm that holds of a row makes the arms over a list holding it hold. -/
theorem armsA_of (tabs : H5iAppLib.Sql.Tables Val) (p : Pred Val) (c : Nat) (sc : Option U64) (via : Via)
    (ids : List U64) (r : List Val) (x : U64) (hx : x ∈ ids) (h : (armA c sc via x).holds tabs r = true) :
    (armsA p c sc via ids).holds tabs r = true := by
  rw [holds_armsA]; simp only [Bool.or_eq_true, List.any_eq_true]; exact .inr ⟨x, hx, h⟩

theorem armsA_base (tabs : H5iAppLib.Sql.Tables Val) (p : Pred Val) (c : Nat) (sc : Option U64) (via : Via)
    (ids : List U64) (r : List Val) (h : p.holds tabs r = true) : (armsA p c sc via ids).holds tabs r = true := by
  rw [holds_armsA, h]; rfl

/-- The table's rows `p` keeps, as a test on a snapshot's rows, for the
`Row` arms: column `c` of row `r` is column `o` of the row of table `t`
with key `x`. -/
theorem holds_row_keys (s : Snapshot) (c : Nat) (o : Nat) (x : U64) (r : List Val) (v : Val) (hv : r[c]? = some v) :
    (Pred.isIn c 2 (.eq 0 (int x.val)) o {}).holds (Snapshot.enc s) r =
      s.keys.val.any (fun y => decide (y.id = x) && decide ((Key.row y)[o]? = some v)) := by
  rw [holds_in_2, hv]
  simp [Window.apply_default, Key.row, List.any_filter]

theorem holds_row_res (s : Snapshot) (c : Nat) (o : Nat) (x : U64) (r : List Val) (v : Val) (hv : r[c]? = some v) :
    (Pred.isIn c 8 (.eq 0 (int x.val)) o {}).holds (Snapshot.enc s) r =
      s.reservations.val.any (fun y => decide (y.id = x) && decide ((Reservation.row y)[o]? = some v)) := by
  rw [holds_in_8, hv]
  simp [Window.apply_default, Reservation.row, List.any_filter]

theorem holds_row_teams (s : Snapshot) (c : Nat) (x : U64) (r : List Val) (v : Val) (hv : r[c]? = some v) :
    (Pred.isIn c 1 (.eq 0 (int x.val)) 0 {}).holds (Snapshot.enc s) r =
      s.teams.val.any (fun y => decide (y.id = x) && decide (int y.id.val = v)) := by
  rw [holds_in_1, hv]
  simp [Window.apply_default, Team.row, List.any_filter]

theorem holds_team_of_key (s : Snapshot) (c : Nat) (x : U64) (r : List Val) (v : Val) (hv : r[c]? = some v) :
    (Pred.isIn c 1 (.isIn 0 2 (.eq 0 (int x.val)) 1 {}) 0 {}).holds (Snapshot.enc s) r =
      s.teams.val.any (fun t => s.keys.val.any (fun y => decide (y.id = x) && decide (y.team = t.id)) &&
        decide (int t.id.val = v)) := by
  rw [holds_in_1, hv]
  simp only [Window.apply_default, List.any_filter]
  congr 1; funext t
  rw [holds_row_keys s 0 1 x (Team.row t) (int t.id.val) (by simp [Team.row])]
  simp [Team.row, Key.row]

/-- What `planA ks ts rs ns m0 allm` keeps, evaluated on `s`, as facts about rows. -/
structure PlanKeep (s : Snapshot) (ks ts rs : List U64) (ns : List (alloc.vec.Vec U8)) (m0 allm : Bool)
    (K : Keep) : Prop where
  key : ∀ x : Key, x.id ∈ ks → K.keys x = true
  key_of_res : ∀ x : Key, ∀ r ∈ s.reservations.val, r.id ∈ rs → r.key_id = x.id → K.keys x = true
  team_id : ∀ x : Team, x.id ∈ ts → K.teams x = true
  team_of_key : ∀ x : Team, ∀ k ∈ s.keys.val, k.id ∈ ks → k.team = x.id → K.teams x = true
  team_of_res : ∀ x : Team, ∀ r ∈ s.reservations.val, r.id ∈ rs → r.team = x.id → K.teams x = true
  model : ∀ m : Model, (∃ n ∈ ns, m.name.val = n.val) → K.models m = true
  model_all : allm = true → ∀ m : Model, K.models m = true
  deployment : ∀ d : Deployment, K.deployments d = true
  key_grant : ∀ g : KeyModel, g.key ∈ ks → K.keyModels g = true
  team_grant_id : ∀ g : TeamModel, g.team ∈ ts → K.teamModels g = true
  team_grant : ∀ g : TeamModel, ∀ k ∈ s.keys.val, k.id ∈ ks → k.team = g.team → K.teamModels g = true
  usage_dep : ∀ u : Usage, u.scope = 2#u64 → K.usage u = true
  usage_key : ∀ u : Usage, u.scope = 0#u64 → u.id ∈ ks → K.usage u = true
  usage_key_of_res : ∀ u : Usage, u.scope = 0#u64 → ∀ r ∈ s.reservations.val, r.id ∈ rs → r.key_id = u.id →
    K.usage u = true
  usage_team_id : ∀ u : Usage, u.scope = 1#u64 → u.id ∈ ts → K.usage u = true
  usage_team : ∀ u : Usage, u.scope = 1#u64 → ∀ k ∈ s.keys.val, k.id ∈ ks → k.team = u.id → K.usage u = true
  usage_team_of_res : ∀ u : Usage, u.scope = 1#u64 → ∀ r ∈ s.reservations.val, r.id ∈ rs → r.team = u.id →
    K.usage u = true
  res_key : ∀ r : Reservation, r.key_id ∈ ks → K.reservations r = true
  res_master : m0 = true → ∀ r : Reservation, r.key_id = 0#u64 → K.reservations r = true
  res_team_id : ∀ r : Reservation, ∀ t ∈ s.teams.val, t.id = r.team → t.id ∈ ts → K.reservations r = true
  res_team : ∀ r : Reservation, ∀ t ∈ s.teams.val, t.id = r.team → ∀ k ∈ s.keys.val, k.id ∈ ks → k.team = t.id →
    K.reservations r = true
  res_id : ∀ r : Reservation, r.id ∈ rs → K.reservations r = true

theorem arm_id (tabs : H5iAppLib.Sql.Tables Val) (c : Nat) (x : U64) (r : List Val) (h : r[c]? = some (int x.val)) :
    (armA c none .Id x).holds tabs r = true := by
  simp [armA, viaA, h]

theorem arm_scoped (tabs : H5iAppLib.Sql.Tables Val) (c : Nat) (sc : U64) (via : Via) (x : U64) (r : List Val)
    (h0 : r[0]? = some (int sc.val)) (h : (viaA c via x).holds tabs r = true) :
    (armA c (some sc) via x).holds tabs r = true := by
  simp [armA, h0, h]

theorem holds_resKey (s : Snapshot) (c : Nat) (x : U64) (r : List Val) (v : Val) (hv : r[c]? = some v) :
    (viaA c resKey x).holds (Snapshot.enc s) r =
      s.reservations.val.any (fun y => decide (y.id = x) && decide (int y.key_id.val = v)) := by
  show (Pred.isIn c 8 (.eq 0 (int x.val)) 1 {}).holds (Snapshot.enc s) r = _
  rw [holds_row_res s c 1 x r v hv]
  simp [Reservation.row]

theorem holds_resTeam (s : Snapshot) (c : Nat) (x : U64) (r : List Val) (v : Val) (hv : r[c]? = some v) :
    (viaA c resTeam x).holds (Snapshot.enc s) r =
      s.reservations.val.any (fun y => decide (y.id = x) && decide (int y.team.val = v)) := by
  simp only [viaA, resTeam, RES_TEAM]
  show (Pred.isIn c 8 (.eq 0 (int x.val)) 2 {}).holds (Snapshot.enc s) r = _
  rw [holds_row_res s c 2 x r v hv]
  simp [Reservation.row]

theorem holds_keyTeam (s : Snapshot) (c : Nat) (x : U64) (r : List Val) (v : Val) (hv : r[c]? = some v) :
    (viaA c keyTeam x).holds (Snapshot.enc s) r =
      s.keys.val.any (fun y => decide (y.id = x) && decide (int y.team.val = v)) := by
  show (Pred.isIn c 2 (.eq 0 (int x.val)) 1 {}).holds (Snapshot.enc s) r = _
  rw [holds_row_keys s c 1 x r v hv]
  simp [Key.row]

theorem holds_teamRow (s : Snapshot) (c : Nat) (x : U64) (r : List Val) (v : Val) (hv : r[c]? = some v) :
    (viaA c teamRow x).holds (Snapshot.enc s) r =
      s.teams.val.any (fun y => decide (y.id = x) && decide (int y.id.val = v)) := by
  show (Pred.isIn c 1 (.eq 0 (int x.val)) 0 {}).holds (Snapshot.enc s) r = _
  rw [holds_row_teams s c x r v hv]

theorem holds_namesA (tabs : H5iAppLib.Sql.Tables Val) (ns : List (alloc.vec.Vec U8)) (r : List Val) :
    (namesA ns).holds tabs r = (noneA.holds tabs r || ns.any (fun n => decide (r[1]? = some (.Bytes n)))) := by
  have : ∀ p : Pred Val, (ns.foldl (fun q n => .or q (.eq 1 (.Bytes n))) p).holds tabs r =
      (p.holds tabs r || ns.any (fun n => decide (r[1]? = some (.Bytes n)))) := by
    induction ns with
    | nil => intro p; simp
    | cons n ns ih => intro p; simp only [List.foldl_cons, ih, holds_or, holds_eq, List.any_cons]; simp [Bool.or_assoc]
  exact this noneA

theorem any_of {α : Type} {l : List α} {p : α → Bool} (x : α) (hx : x ∈ l) (h : p x = true) : l.any p = true :=
  List.any_eq_true.2 ⟨x, hx, h⟩

theorem plan_keep (s : Snapshot) (ks ts rs : List U64) (ns : List (alloc.vec.Vec U8)) (m0 allm : Bool) :
    PlanKeep s ks ts rs ns m0 allm (keepA s ks ts rs ns m0 allm) := by
  constructor
  · intro x hx; simp only [keepA, keysA]
    apply armsA_base; exact armsA_of _ _ _ _ _ _ _ x.id hx (arm_id _ _ _ _ (by simp [Key.row]))
  · intro x r hr hrid hrk; simp only [keepA, keysA]
    refine armsA_of _ _ _ _ _ _ _ r.id hrid ?_
    simp only [armA]; rw [holds_resKey s 0 r.id (Key.row x) (int x.id.val) (by simp [Key.row])]
    exact any_of r hr (by simp [hrk])
  · intro x hx; simp only [keepA, teamsA]
    apply armsA_base; apply armsA_base; exact armsA_of _ _ _ _ _ _ _ x.id hx (arm_id _ _ _ _ (by simp [Team.row]))
  · intro x k hk hkid hkt; simp only [keepA, teamsA]
    apply armsA_base; refine armsA_of _ _ _ _ _ _ _ k.id hkid ?_
    simp only [armA]; rw [holds_keyTeam s 0 k.id (Team.row x) (int x.id.val) (by simp [Team.row])]
    exact any_of k hk (by simp [hkt])
  · intro x r hr hrid hrt; simp only [keepA, teamsA]
    refine armsA_of _ _ _ _ _ _ _ r.id hrid ?_
    simp only [armA]; rw [holds_resTeam s 0 r.id (Team.row x) (int x.id.val) (by simp [Team.row])]
    exact any_of r hr (by simp [hrt])
  · intro m ⟨n, hn, hmn⟩; simp only [keepA]
    cases allm
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [holds_namesA]
      have : m.name = n := by apply alloc.vec.Vec.ext; exact hmn
      simp only [Bool.or_eq_true]; exact .inr (any_of n hn (by simp [Model.row, this]))
    · rfl
  · intro h m; simp [keepA, h]
  · intro d; rfl
  · intro g hg; simp only [keepA]
    exact armsA_of _ _ _ _ _ _ _ g.key hg (arm_id _ _ _ _ (by simp [KeyModel.row]))
  · intro g hg; simp only [keepA, teamModelsA]
    apply armsA_base; exact armsA_of _ _ _ _ _ _ _ g.team hg (arm_id _ _ _ _ (by simp [TeamModel.row]))
  · intro g k hk hkid hkt; simp only [keepA, teamModelsA]
    refine armsA_of _ _ _ _ _ _ _ k.id hkid ?_
    simp only [armA]; rw [holds_keyTeam s 0 k.id (TeamModel.row g) (int g.team.val) (by simp [TeamModel.row])]
    exact any_of k hk (by simp [hkt])
  · intro u hu; simp only [keepA, usageA]
    apply armsA_base; apply armsA_base; apply armsA_base; apply armsA_base; apply armsA_base
    simp [Usage.row, hu]
  · intro u hu hid; simp only [keepA, usageA]
    apply armsA_base; apply armsA_base; apply armsA_base; apply armsA_base
    refine armsA_of _ _ _ _ _ _ _ u.id hid (arm_scoped _ _ _ _ _ _ (by simp [Usage.row, hu]) ?_)
    simp [viaA, Usage.row]
  · intro u hu r hr hrid hrk; simp only [keepA, usageA]
    apply armsA_base; apply armsA_base; apply armsA_base
    refine armsA_of _ _ _ _ _ _ _ r.id hrid (arm_scoped _ _ _ _ _ _ (by simp [Usage.row, hu]) ?_)
    rw [holds_resKey s 1 r.id (Usage.row u) (int u.id.val) (by simp [Usage.row])]
    exact any_of r hr (by simp [hrk])
  · intro u hu hid; simp only [keepA, usageA]
    apply armsA_base; apply armsA_base
    refine armsA_of _ _ _ _ _ _ _ u.id hid (arm_scoped _ _ _ _ _ _ (by simp [Usage.row, hu]) ?_)
    simp [viaA, Usage.row]
  · intro u hu k hk hkid hkt; simp only [keepA, usageA]
    apply armsA_base
    refine armsA_of _ _ _ _ _ _ _ k.id hkid (arm_scoped _ _ _ _ _ _ (by simp [Usage.row, hu]) ?_)
    rw [holds_keyTeam s 1 k.id (Usage.row u) (int u.id.val) (by simp [Usage.row])]
    exact any_of k hk (by simp [hkt])
  · intro u hu r hr hrid hrt; simp only [keepA, usageA]
    refine armsA_of _ _ _ _ _ _ _ r.id hrid (arm_scoped _ _ _ _ _ _ (by simp [Usage.row, hu]) ?_)
    rw [holds_resTeam s 1 r.id (Usage.row u) (int u.id.val) (by simp [Usage.row])]
    exact any_of r hr (by simp [hrt])
  · intro r hk; simp only [keepA, reservationsA]
    apply armsA_base; apply armsA_base; apply armsA_base
    exact armsA_of _ _ _ _ _ _ _ r.key_id hk (arm_id _ _ _ _ (by simp [Reservation.row]))
  · intro hm r h0; simp only [keepA, reservationsA, hm, ↓reduceIte]
    apply armsA_base; apply armsA_base; apply armsA_base; apply armsA_base
    simp [Reservation.row, h0]
  · intro r t ht htr hts; simp only [keepA, reservationsA]
    apply armsA_base; apply armsA_base
    refine armsA_of _ _ _ _ _ _ _ t.id hts ?_
    simp only [armA, RES_TEAM]; show (viaA 2 teamRow t.id).holds _ _ = true
    rw [holds_teamRow s 2 t.id (Reservation.row r) (int r.team.val) (by simp [Reservation.row])]
    exact any_of t ht (by simp [htr])
  · intro r t ht htr k hk hkid hkt; simp only [keepA, reservationsA]
    apply armsA_base
    refine armsA_of _ _ _ _ _ _ _ k.id hkid ?_
    simp only [armA, viaA, RES_TEAM]
    show (Pred.isIn 2 1 (.isIn 0 2 (.eq 0 (int k.id.val)) 1 {}) 0 {}).holds _ _ = true
    rw [holds_team_of_key s 2 k.id (Reservation.row r) (int r.team.val) (by simp [Reservation.row])]
    exact any_of t ht (by simp only [Bool.and_eq_true, decide_eq_true_eq, int_u64]; exact ⟨any_of k hk (by simp [hkt]), htr⟩)
  · intro r hid; simp only [keepA, reservationsA]
    exact armsA_of _ _ _ _ _ _ _ r.id hid (arm_id _ _ _ _ (by simp [Reservation.row]))


/-! ## Single commands -/

theorem common_of {s0 : Snapshot} {ks ts rs : List U64} {ns : List (alloc.vec.Vec U8)} {m0 allm : Bool} {K : Keep}
    (hK : PlanKeep s0 ks ts rs ns m0 allm K) (s : Snapshot) : Common K s :=
  ⟨fun d _ => hK.deployment d, fun u _ h => hK.usage_dep u h⟩

theorem keyNeeds_of {s : Snapshot} {ks ts rs : List U64} {ns : List (alloc.vec.Vec U8)} {m0 allm : Bool} {K : Keep}
    (hK : PlanKeep s ks ts rs ns m0 allm K) {kid : U64} (hkid : kid ∈ ks) : KeyNeeds K s kid where
  key x _ h := hK.key x (by rw [h]; exact hkid)
  grants k _ h g _ hg := hK.key_grant g (by rw [hg, h]; exact hkid)
  team k hk h x _ hx := hK.team_of_key x k hk (by rw [h]; exact hkid) hx.symm
  team_grants k hk h g _ hg := hK.team_grant g k hk (by rw [h]; exact hkid) hg.symm
  key_usage k _ h u _ hs hu := hK.usage_key u hs (by rw [hu, h]; exact hkid)
  team_usage k hk h u _ hs hu := hK.usage_team u hs k hk (by rw [h]; exact hkid) hu.symm
  key_res k _ h r _ hr := hK.res_key r (by rw [hr, h]; exact hkid)
  team_res k hk h t ht htk r _ hr := hK.res_team r t ht hr.symm k hk (by rw [h]; exact hkid) htk.symm

theorem settleNeeds_of {s : Snapshot} {ks ts rs : List U64} {ns : List (alloc.vec.Vec U8)} {m0 allm : Bool}
    {K : Keep} (hK : PlanKeep s ks ts rs ns m0 allm K) (a : Principal) {rid : U64} (hrid : rid ∈ rs)
    (hcaller : a.master = false → a.key ∈ ks) : SettleNeeds K s a rid where
  res r _ h := hK.res_id r (by rw [h]; exact hrid)
  caller hm x _ h := hK.key x (by rw [h]; exact hcaller hm)
  key r hr h _ x _ hx := hK.key_of_res x r hr (by rw [h]; exact hrid) hx.symm
  key_usage r hr h _ u _ hs hu := hK.usage_key_of_res u hs r hr (by rw [h]; exact hrid) hu.symm
  team r hr h _ x _ hx := hK.team_of_res x r hr (by rw [h]; exact hrid) hx.symm
  team_usage r hr h _ u _ hs hu := hK.usage_team_of_res u hs r hr (by rw [h]; exact hrid) hu.symm

theorem caller_mem (a : Principal) (hm : a.master = false) : a.key ∈ callerA a := by simp [callerA, hm]

/-- The frame theorem for every command but `Batch`, with no hypothesis. -/
theorem frame_cmd (a : Principal) (s : Snapshot) (c : Command) (plan : List (Read Val)) (hp : readsA a c = some plan)
    (hb : ∀ items, c ≠ .Batch items) : transition a (Snapshot.load plan s) c = transition a s c := by
  cases c <;> simp only [readsA, Option.some.injEq, reduceCtorEq] at hp
  case Admit nm pt mt ex =>
    subst hp
    have hs := load_slice s (callerA a) [] [] [nm] false false
    have hK := plan_keep s (callerA a) [] [] [nm] false false
    simp only [transition]
    exact admit_slice hs a nm pt mt ex (common_of hK s) (fun x _ h => hK.model x ⟨nm, by simp, h⟩)
      (fun hm => keyNeeds_of hK (caller_mem a hm))
  case Settle rid pt ct st =>
    subst hp
    have hs := load_slice s (callerA a) [] [rid] [] false false
    have hK := plan_keep s (callerA a) [] [rid] [] false false
    simp only [transition]
    exact settle_slice hs a rid pt ct st (common_of hK s) (settleNeeds_of hK a (by simp) (caller_mem a))
  case Expire rid =>
    subst hp
    have hs := load_slice s (callerA a) [] [rid] [] false false
    have hK := plan_keep s (callerA a) [] [rid] [] false false
    simp only [transition]
    exact expire_slice hs a rid (settleNeeds_of hK a (by simp) (caller_mem a))
  case KeyInfo id =>
    subst hp
    have hs := load_slice s (callerA a ++ [id]) [] [] [] false false
    have hK := plan_keep s (callerA a ++ [id]) [] [] [] false false
    simp only [transition]
    exact key_info_slice hs a id (fun hm x _ h => hK.key x (by rw [h]; simp [caller_mem a hm]))
      (fun x _ h => hK.key x (by rw [h]; simp)) (fun g _ h => hK.key_grant g (by rw [h]; simp))
      (fun r _ h => hK.res_key r (by rw [h]; simp))
  case TeamInfo id =>
    subst hp
    have hs := load_slice s (callerA a) [id] [] [] false false
    have hK := plan_keep s (callerA a) [id] [] [] false false
    simp only [transition]
    exact team_info_slice hs a id (fun hm x _ h => hK.key x (by rw [h]; exact caller_mem a hm))
      (fun x _ h => hK.team_id x (by rw [h]; simp)) (fun g _ h => hK.team_grant_id g (by rw [h]; simp))
      (fun t ht htid r _ hr => hK.res_team_id r t ht (htid.trans hr.symm) (by rw [htid]; simp))
  case ListModels =>
    subst hp
    have hs := load_slice s (callerA a) [] [] [] false true
    have hK := plan_keep s (callerA a) [] [] [] false true
    simp only [transition]
    exact list_models_slice hs a (fun hm x _ h => hK.key x (by rw [h]; exact caller_mem a hm))
      (fun m _ => hK.model_all rfl m)
      (fun hm k _ h g _ hg => hK.key_grant g (by rw [hg, h]; exact caller_mem a hm))
      (fun hm k hk h x _ hx => hK.team_of_key x k hk (by rw [h]; exact caller_mem a hm) hx.symm)
      (fun hm k hk h g _ hg => hK.team_grant g k hk (by rw [h]; exact caller_mem a hm) hg.symm)
  case Batch items => exact absurd rfl (hb items)

/-! ## Batches

The plan of a batch names every item's key, reservation and model
(`wants_cover`). Each item runs on the state the earlier items left, which
differs from the snapshot `s0` the plan was evaluated on only in what items
write (`Ctx`): keys and teams keep their ids and teams, and a new
reservation belongs to an item's key (and its team) or to the master key. -/

/-- An item whose reads the batch's plan names. -/
def Covered (W : Wants) (it : BatchItem) : Prop :=
  (it.master = false → it.key ∈ W.keys) ∧
  match it.op with
  | .Admit m _ _ _ => (∃ n ∈ W.names, m.val = n.val) ∧ (it.master = true → W.m0 = true)
  | .Settle r _ _ _ => r ∈ W.res

/-- `w'` names at least what `w` names. -/
structure Grows (w w' : Wants) : Prop where
  keys : ∀ k ∈ w.keys, k ∈ w'.keys
  res : ∀ r ∈ w.res, r ∈ w'.res
  names : ∀ n ∈ w.names, ∃ n' ∈ w'.names, n'.val = n.val
  m0 : w.m0 = true → w'.m0 = true

theorem grows_refl (w : Wants) : Grows w w := ⟨fun _ h => h, fun _ h => h, fun n h => ⟨n, h, rfl⟩, id⟩

theorem grows_trans {w1 w2 w3 : Wants} (h1 : Grows w1 w2) (h2 : Grows w2 w3) : Grows w1 w3 :=
  ⟨fun k h => h2.keys k (h1.keys k h), fun r h => h2.res r (h1.res r h),
    fun n h => by
      obtain ⟨n', h', e⟩ := h1.names n h
      obtain ⟨n'', h'', e'⟩ := h2.names n' h'
      exact ⟨n'', h'', e'.trans e⟩,
    fun h => h2.m0 (h1.m0 h)⟩

theorem mem_addId_self (l : List U64) (x : U64) : x ∈ addId l x := by
  unfold addId; split <;> simp_all

theorem mem_addId_of (l : List U64) (x y : U64) (h : y ∈ l) : y ∈ addId l x := by
  unfold addId; split <;> simp_all

theorem addName_self (l : List (alloc.vec.Vec U8)) (n : alloc.vec.Vec U8) : ∃ n' ∈ addName l n, n.val = n'.val := by
  unfold addName; split
  · rename_i h; obtain ⟨m, hm, e⟩ := List.any_eq_true.1 h; exact ⟨m, hm, (by simpa using e : m.val = n.val).symm⟩
  · exact ⟨n, by simp, rfl⟩

theorem addName_of (l : List (alloc.vec.Vec U8)) (n m : alloc.vec.Vec U8) (h : m ∈ l) : m ∈ addName l n := by
  unfold addName; split <;> simp_all

theorem grows_step (w : Wants) (it : BatchItem) : Grows w (wantStep w it) := by
  obtain ⟨k, m, op⟩ := it
  have hk : ∀ x ∈ w.keys, x ∈ (if m then w.keys else addId w.keys k) := by
    intro x hx; cases m
    · exact mem_addId_of _ _ _ hx
    · exact hx
  cases op with
  | Admit nm _ _ _ => exact ⟨hk, fun _ h => h, fun n h => ⟨n, addName_of _ _ _ h, rfl⟩, fun h => by simp [wantStep, h]⟩
  | Settle rid _ _ _ => exact ⟨hk, fun _ h => mem_addId_of _ _ _ h, fun n h => ⟨n, h, rfl⟩, id⟩

theorem grows_foldl : ∀ (l : List BatchItem) (w : Wants), Grows w (l.foldl wantStep w)
  | [], w => grows_refl w
  | x :: xs, w => grows_trans (grows_step w x) (grows_foldl xs _)

theorem covered_step (w : Wants) (it : BatchItem) : Covered (wantStep w it) it := by
  obtain ⟨k, m, op⟩ := it
  have hk : m = false → k ∈ (if m then w.keys else addId w.keys k) := by
    intro hm; subst hm; exact mem_addId_self _ _
  cases op with
  | Admit nm _ _ _ =>
    refine ⟨hk, ?_, fun h => by simp only [wantStep, Bool.or_eq_true]; exact .inl h⟩
    exact addName_self _ _
  | Settle rid _ _ _ => exact ⟨hk, mem_addId_self _ _⟩

theorem covered_mono {w w' : Wants} {it : BatchItem} (h : Covered w it) (hg : Grows w w') : Covered w' it := by
  obtain ⟨k, m, op⟩ := it
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hm => hg.keys _ (h1 hm), ?_⟩
  cases op with
  | Admit nm _ _ _ =>
    obtain ⟨⟨n, hn, e⟩, hm0⟩ := h2
    obtain ⟨n', hn', e'⟩ := hg.names n hn
    exact ⟨⟨n', hn', e.trans e'.symm⟩, fun h => hg.m0 (hm0 h)⟩
  | Settle rid _ _ _ => exact hg.res _ h2

theorem cover_foldl : ∀ (l : List BatchItem) (w : Wants), ∀ it ∈ l, Covered (l.foldl wantStep w) it
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: xs, w, it, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact covered_mono (covered_step w it) (grows_foldl xs _)
    · exact cover_foldl xs _ it h

theorem wants_cover (items : List BatchItem) : ∀ it ∈ items, Covered (wantsA items) it :=
  cover_foldl items _

/-- The rows of a batch run's state `st` the plan reasons about, relative to
the snapshot `s0` it was evaluated on. -/
structure Mem (s0 : Snapshot) (ks : List U64) (st : St) : Prop where
  keys : ∀ k ∈ st.keys, ∃ y ∈ s0.keys.val, y.id = k.id ∧ y.team = k.team
  teams : ∀ t ∈ st.teams, ∃ y ∈ s0.teams.val, y.id = t.id
  res : ∀ r ∈ st.reservations, r ∈ s0.reservations.val ∨
    (r.key_id ∈ ks ∧ ∃ y ∈ s0.keys.val, y.id = r.key_id ∧ y.team = r.team) ∨ (r.key_id = 0#u64 ∧ r.team = 0#u64)

structure Ctx (s0 : Snapshot) (ks : List U64) (st : St) : Prop where
  inv : Inv st
  mem : Mem s0 ks st

theorem ctx_init (s : Snapshot) (ks : List U64) (hinv : Inv (Snapshot.toSt s)) : Ctx s ks (Snapshot.toSt s) :=
  ⟨hinv, ⟨fun k hk => ⟨k, hk, rfl, rfl⟩, fun t ht => ⟨t, ht, rfl⟩, fun r hr => .inl hr⟩⟩

/-- A write a batch item can make, in terms of `s0`. -/
def Origin (s0 : Snapshot) (ks : List U64) : Write → Prop
  | .PutKey x => ∃ y ∈ s0.keys.val, y.id = x.id ∧ y.team = x.team
  | .PutTeam x => ∃ y ∈ s0.teams.val, y.id = x.id
  | .PutReservation x =>
    (x.key_id ∈ ks ∧ ∃ y ∈ s0.keys.val, y.id = x.key_id ∧ y.team = x.team) ∨ (x.key_id = 0#u64 ∧ x.team = 0#u64)
  | _ => True

theorem mem_applyWrite {s0 : Snapshot} {ks : List U64} {st : St} (h : Mem s0 ks st) (w : Write)
    (ho : Origin s0 ks w) : Mem s0 ks (applyWrite st w) := by
  obtain ⟨hk, ht, hr⟩ := h
  cases w <;> simp only [applyWrite, Origin] at ho ⊢
  case PutTeam x =>
    refine ⟨hk, fun t htm => ?_, hr⟩
    rcases mem_upsert_of htm with rfl | h
    · exact ho
    · exact ht t h
  case DelTeam id => exact ⟨hk, fun t htm => ht t (List.mem_filter.1 htm).1, hr⟩
  case PutKey x =>
    refine ⟨fun k hkm => ?_, ht, hr⟩
    rcases mem_upsert_of hkm with rfl | h
    · exact ho
    · exact hk k h
  case DelKey id => exact ⟨fun k hkm => hk k (List.mem_filter.1 hkm).1, ht, hr⟩
  case PutReservation x =>
    refine ⟨hk, ht, fun r hrm => ?_⟩
    rcases mem_upsert_of hrm with rfl | h
    · exact .inr ho
    · exact hr r h
  case DelReservation id => exact ⟨hk, ht, fun r hrm => hr r (List.mem_filter.1 hrm).1⟩
  all_goals exact ⟨hk, ht, hr⟩

theorem mem_applyAll {s0 : Snapshot} {ks : List U64} : ∀ (ws : List Write) (st : St), Mem s0 ks st →
    (∀ w ∈ ws, Origin s0 ks w) → Mem s0 ks (applyAll st ws)
  | [], _, h, _ => h
  | w :: ws, st, h, ho => mem_applyAll ws _ (mem_applyWrite h w (ho w (by simp))) (fun x hx => ho x (by simp [hx]))

/-- A snapshot holding a state whose tables fit in vectors. -/
def snapOf (st : St) (h : stSize st < Usize.max) : Snapshot :=
  ⟨st.settings, .from st.teams (by simp only [stSize] at h; omega), .from st.keys (by simp only [stSize] at h; omega),
    .from st.models (by simp only [stSize] at h; omega), .from st.deployments (by simp only [stSize] at h; omega),
    .from st.keyModels (by simp only [stSize] at h; omega), .from st.teamModels (by simp only [stSize] at h; omega),
    .from st.usage (by simp only [stSize] at h; omega), .from st.reservations (by simp only [stSize] at h; omega)⟩

theorem toSt_snapOf (st : St) (h : stSize st < Usize.max) : Snapshot.toSt (snapOf st h) = st := by
  simp [Snapshot.toSt, snapOf, alloc.vec.Vec.from_val]

theorem split3 (a b : List Write) (u x y : Write) : a ++ b ++ [u, x, y] = (a ++ b ++ [u]) ++ [x, y] := by simp

section Items
variable {s0 : Snapshot} {W : Wants} {K : Keep} (hK : PlanKeep s0 W.keys [] W.res W.names W.m0 false K)
include hK

/-- What the plan keeps of the key and its counters of a reservation the
batch settles. -/
theorem res_key_kept {st : St} (hm : Mem s0 W.keys st) {r : Reservation} (hr : r ∈ st.reservations)
    (hrid : r.id ∈ W.res) (h0 : r.key_id ≠ 0#u64) :
    (∀ y : Key, y.id = r.key_id → K.keys y = true) ∧
      (∀ u : Usage, u.scope = 0#u64 → u.id = r.key_id → K.usage u = true) := by
  rcases hm.res r hr with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact ⟨fun y hy => hK.key_of_res y r h1 hrid hy.symm, fun u hs hu => hK.usage_key_of_res u hs r h1 hrid hu.symm⟩
  · exact ⟨fun y hy => hK.key y (by rw [hy]; exact h1), fun u hs hu => hK.usage_key u hs (by rw [hu]; exact h1)⟩
  · exact absurd h1 h0

theorem res_team_kept {st : St} (hm : Mem s0 W.keys st) {r : Reservation} (hr : r ∈ st.reservations)
    (hrid : r.id ∈ W.res) (h0 : r.team ≠ 0#u64) :
    (∀ y : Team, y.id = r.team → K.teams y = true) ∧
      (∀ u : Usage, u.scope = 1#u64 → u.id = r.team → K.usage u = true) := by
  rcases hm.res r hr with h1 | ⟨h1, y, hy, hyi, hyt⟩ | ⟨-, h1⟩
  · exact ⟨fun x hx => hK.team_of_res x r h1 hrid hx.symm, fun u hs hu => hK.usage_team_of_res u hs r h1 hrid hu.symm⟩
  · exact ⟨fun x hx => hK.team_of_key x y hy (by rw [hyi]; exact h1) (hyt.trans hx.symm),
      fun u hs hu => hK.usage_team u hs y hy (by rw [hyi]; exact h1) (hyt.trans hu.symm)⟩
  · exact absurd h1 h0

/-- What the plan keeps of a key the batch names and of its team. -/
theorem key_team_kept {st : St} (hm : Mem s0 W.keys st) {k : Key} (hk : k ∈ st.keys) (hkid : k.id ∈ W.keys) :
    (∀ y : Team, y.id = k.team → K.teams y = true) ∧
      (∀ u : Usage, u.scope = 1#u64 → u.id = k.team → K.usage u = true) ∧
      (∀ g : TeamModel, g.team = k.team → K.teamModels g = true) := by
  obtain ⟨y, hy, hyi, hyt⟩ := hm.keys k hk
  have hyk : y.id ∈ W.keys := by rw [hyi]; exact hkid
  exact ⟨fun x hx => hK.team_of_key x y hy hyk (hyt.trans hx.symm), fun u hs hu => hK.usage_team u hs y hy hyk (hyt.trans hu.symm),
    fun g hg => hK.team_grant g y hy hyk (hyt.trans hg.symm)⟩

/-- Each item runs on a slice as on the full state. -/
theorem item_frame (a : Principal) {s1' s1 : Snapshot}
    (hs : Slice K (Snapshot.toSt s1') (Snapshot.toSt s1)) (hc : Ctx s0 W.keys (Snapshot.toSt s1))
    (it : BatchItem) (hcov : Covered W it) :
    transition (itemPrincipal a it) s1' (itemCmd it) = transition (itemPrincipal a it) s1 (itemCmd it) := by
  obtain ⟨ik, im, op⟩ := it
  obtain ⟨hck, hcop⟩ := hcov
  cases op with
  | Admit nm pt mt ex =>
    simp only [itemCmd, transition]
    obtain ⟨⟨n, hn, hnm⟩, _⟩ := hcop
    refine admit_slice hs _ nm pt mt ex (common_of hK s1) (fun x _ h => hK.model x ⟨n, hn, h.trans hnm⟩)
      (fun hm => ?_)
    have hkid : ik ∈ W.keys := hck hm
    exact {
      key := fun x _ h => hK.key x (by rw [h]; exact hkid)
      grants := fun k _ h g _ hg => hK.key_grant g (by rw [hg, h]; exact hkid)
      team := fun k hk h x _ hx => (key_team_kept hK hc.mem hk (by rw [h]; exact hkid)).1 x hx
      team_grants := fun k hk h g _ hg => (key_team_kept hK hc.mem hk (by rw [h]; exact hkid)).2.2 g hg
      key_usage := fun k _ h u _ hsc hu => hK.usage_key u hsc (by rw [hu, h]; exact hkid)
      team_usage := fun k hk h u _ hsc hu => (key_team_kept hK hc.mem hk (by rw [h]; exact hkid)).2.1 u hsc hu
      key_res := fun k _ h r _ hr => hK.res_key r (by rw [hr, h]; exact hkid)
      team_res := fun k hk h t ht htk r _ hr => by
        obtain ⟨y, hy, hyi, hyt⟩ := hc.mem.keys k hk
        obtain ⟨t0, ht0, ht0i⟩ := hc.mem.teams t ht
        exact hK.res_team r t0 ht0 (ht0i.trans hr.symm) y hy (by rw [hyi, h]; exact hkid)
          (hyt.trans (htk.symm.trans ht0i.symm)) }
  | Settle rid pt ct st =>
    simp only [itemCmd, transition]
    have hrid : rid ∈ W.res := hcop
    refine settle_slice hs _ rid pt ct st (common_of hK s1) ?_
    exact {
      res := fun r _ h => hK.res_id r (by rw [h]; exact hrid)
      caller := fun hm x _ h => hK.key x (by rw [h]; exact hck hm)
      key := fun r hr h h0 x _ hx => (res_key_kept hK hc.mem hr (by rw [h]; exact hrid) h0).1 x hx
      key_usage := fun r hr h h0 u _ hsc hu => (res_key_kept hK hc.mem hr (by rw [h]; exact hrid) h0).2 u hsc hu
      team := fun r hr h h0 x _ hx => (res_team_kept hK hc.mem hr (by rw [h]; exact hrid) h0).1 x hx
      team_usage := fun r hr h h0 u _ hsc hu => (res_team_kept hK hc.mem hr (by rw [h]; exact hrid) h0).2 u hsc hu }

/-- What an item writes is kept by the plan, and comes from `s0` (`Origin`). -/
theorem item_writes (a : Principal) {s1 : Snapshot} (hc : Ctx s0 W.keys (Snapshot.toSt s1))
    (it : BatchItem) (hcov : Covered W it) {w : alloc.vec.Vec Write} {r : Reply}
    (ht : transition (itemPrincipal a it) s1 (itemCmd it) = ok (.Ok (w, r))) :
    AllKept K (Snapshot.toSt s1) w.val ∧ ∀ x ∈ w.val, Origin s0 W.keys x := by
  have he := transition_effect ht
  obtain ⟨ik, im, op⟩ := it
  obtain ⟨hck, hcop⟩ := hcov
  have hfresh : ∀ (R : Reservation), R.id.val = s1.settings.next_id.val + 1 →
      ∀ y ∈ (Snapshot.toSt s1).reservations, y.id = R.id → K.reservations y = true := by
    intro R hR y hy hyid
    have := (hc.inv.reservations_fresh y hy).1
    rw [hyid, hR] at this
    simp [Snapshot.toSt] at this
  cases op with
  | Admit nm pt mt ex =>
    simp only [itemCmd] at he
    obtain ⟨m, -, hmas, hkey⟩ := he
    cases him : im
    · obtain ⟨k, t, d, id, amt, k2, uk, ud, tw, hA, hid, -, hkn, huk, htw, hud, hws⟩ := hkey him
      have hkid : ik ∈ W.keys := hck him
      obtain ⟨hkm, hkv⟩ := Theorems.findKey_mem hA.key
      have hkid' : k.id = ik := (Schema.u64_val_eq _ _).1 hkv
      have hk2 := hkn.limits
      have hkt := key_team_kept hK hc.mem hkm (by rw [hkid']; exact hkid)
      obtain ⟨y, hy, hyi, hyt⟩ := hc.mem.keys k hkm
      -- the team writes
      have htw' : (∀ x ∈ tw, KeptU K x) ∧ ∀ x ∈ tw, Origin s0 W.keys x := by
        cases t with
        | none => simp only [TeamWrites] at htw; subst htw; simp
        | some team =>
          obtain ⟨t2, u1, htn, hu1, rfl⟩ := htw
          have hteam : team ∈ (Snapshot.toSt s1).teams ∧ team.id = k.team := by
            by_cases h0 : k.team.val = 0
            · have := hA.no_team h0; cases this
            · obtain ⟨team', hf, -, he'⟩ := hA.team h0
              cases he'
              obtain ⟨h1, h2⟩ := Theorems.findTeam_mem hf
              exact ⟨h1, (Schema.u64_val_eq _ _).1 h2⟩
          have ht2 := htn.limits
          obtain ⟨hu1s, hu1i, -⟩ := hu1
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            rcases hx with rfl | rfl
            · intro z hz; exact hkt.1 z (by rw [hz, ht2.1, hteam.2])
            · intro z hz1 hz2; exact hkt.2.1 z (by rw [hz1, hu1s]) (by rw [hz2, hu1i, hteam.2])
          · intro x hx
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            rcases hx with rfl | rfl
            · obtain ⟨t0, ht0, ht0i⟩ := hc.mem.teams team hteam.1
              exact ⟨t0, ht0, by rw [ht0i, ht2.1]⟩
            · trivial
      obtain ⟨huks, hukid, -⟩ := huk
      obtain ⟨huds, -, -⟩ := hud
      have hpre : ∀ x ∈ [Write.PutKey k2, .PutUsage uk] ++ tw ++ [.PutUsage ud], KeptU K x := by
        intro x hx
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with ((rfl | rfl) | hx) | rfl
        · intro z hz; exact hK.key z (by rw [hz, hk2.1, hkid']; exact hkid)
        · intro z hz1 hz2; exact hK.usage_key z (by rw [hz1, huks]) (by rw [hz2, hukid, hkid']; exact hkid)
        · exact htw'.1 x hx
        · intro z hz1 _; exact hK.usage_dep z (by rw [hz1, huds])
      rw [hws]
      refine ⟨?_, ?_⟩
      · rw [split3]
        refine allKept_append_univ _ _ _ hpre ⟨⟨hK.res_key _ (show k.id ∈ W.keys by rw [hkid']; exact hkid), ?_⟩, trivial, trivial⟩
        rw [applyAll_res_univ _ _ hpre]
        exact hfresh _ hid
      · intro x hx
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with ((rfl | rfl) | hx) | rfl | rfl | rfl
        · exact ⟨y, hy, by rw [hyi, hk2.1], by rw [hyt, hk2.2.1]⟩
        · trivial
        · exact htw'.2 x hx
        · trivial
        · exact .inl ⟨show k.id ∈ W.keys by rw [hkid']; exact hkid, y, hy, hyi, hyt⟩
        · trivial
    · obtain ⟨d, id, amt, u, -, -, hid, -, hu, hws⟩ := hmas him
      obtain ⟨hus, -, -⟩ := hu
      have hpre : ∀ x ∈ [Write.PutUsage u], KeptU K x := by
        intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        subst hx
        intro z hz1 _; exact hK.usage_dep z (by rw [hz1, hus])
      rw [hws]
      refine ⟨?_, ?_⟩
      · refine allKept_append_univ [Write.PutUsage u] _ _ hpre ⟨⟨hK.res_master (hcop.2 him) _ rfl, ?_⟩, trivial, trivial⟩
        rw [applyAll_res_univ _ _ hpre]
        exact hfresh _ hid
      · intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · trivial
        · exact .inr ⟨rfl, rfl⟩
        · trivial
  | Settle rid pt ct st =>
    simp only [itemCmd] at he
    obtain ⟨rs, c, tokens, kw, tw, ud, dw, hr, -, -, -, -, hkw, htw, hud, hdw, hws⟩ := he
    have hrid : rid ∈ W.res := hcop
    obtain ⟨hrm, hrv⟩ := Theorems.findReservation_mem hr
    have hrid' : rs.id ∈ W.res := by rw [(Schema.u64_val_eq _ _).1 hrv]; exact hrid
    have hkw' : (∀ x ∈ kw, KeptU K x) ∧ ∀ x ∈ kw, Origin s0 W.keys x := by
      rcases hkw with ⟨-, rfl⟩ | ⟨k, k2, sp, u, h0, hf, hkn, -, hu, rfl⟩
      · simp
      · have h0' : rs.key_id ≠ 0#u64 := fun h => h0 (by rw [h]; rfl)
        have hkk := res_key_kept hK hc.mem hrm hrid' h0'
        obtain ⟨hkm, hkv⟩ := Theorems.findKey_mem hf
        have hkid : k.id = rs.key_id := (Schema.u64_val_eq _ _).1 hkv
        have hk2 := hkn.limits
        obtain ⟨hus, hui, -⟩ := hu
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl
          · intro z hz; exact hkk.1 z (by rw [hz]; simp [hk2.1, hkid])
          · intro z hz1 hz2; exact hkk.2 z (by rw [hz1, hus]) (by rw [hz2, hui, hkid])
        · intro x hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl
          · obtain ⟨y, hy, hyi, hyt⟩ := hc.mem.keys k hkm
            exact ⟨y, hy, by simp [hyi, hk2.1], by simp [hyt, hk2.2.1]⟩
          · trivial
    have htw' : (∀ x ∈ tw, KeptU K x) ∧ ∀ x ∈ tw, Origin s0 W.keys x := by
      rcases htw with ⟨-, rfl⟩ | ⟨t, t2, sp, u, h0, hf, htn, -, hu, rfl⟩
      · simp
      · have h0' : rs.team ≠ 0#u64 := fun h => h0 (by rw [h]; rfl)
        have htk := res_team_kept hK hc.mem hrm hrid' h0'
        obtain ⟨htm, htv⟩ := Theorems.findTeam_mem hf
        have htid : t.id = rs.team := (Schema.u64_val_eq _ _).1 htv
        have ht2 := htn.limits
        obtain ⟨hus, hui, -⟩ := hu
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl
          · intro z hz; exact htk.1 z (by rw [hz]; simp [ht2.1, htid])
          · intro z hz1 hz2; exact htk.2 z (by rw [hz1, hus]) (by rw [hz2, hui, htid])
        · intro x hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl
          · obtain ⟨t0, ht0, ht0i⟩ := hc.mem.teams t htm
            exact ⟨t0, ht0, by simp [ht0i, ht2.1]⟩
          · trivial
    have hdw' : ∀ x ∈ dw, KeptU K x := by
      rcases hdw with ⟨-, rfl⟩ | ⟨d, d', -, -, -, rfl⟩
      · simp
      · intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        subst hx
        intro z _; exact hK.deployment z
    obtain ⟨huds, -, -⟩ := hud
    rw [hws]
    refine ⟨allKept_univ_del _ ?_ _, ?_⟩
    · intro x hx
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with ((((rfl | hx) | hx) | rfl) | hx) | rfl
      · exact .inr ⟨_, rfl⟩
      · exact .inl (hkw'.1 x hx)
      · exact .inl (htw'.1 x hx)
      · exact .inl (fun z hz1 _ => hK.usage_dep z (by rw [hz1, huds]))
      · exact .inl (hdw' x hx)
      · exact .inl trivial
    · intro x hx
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with ((((rfl | hx) | hx) | rfl) | hx) | rfl
      · trivial
      · exact hkw'.2 x hx
      · exact htw'.2 x hx
      · trivial
      · have := hdw' x hx
        rcases hdw with ⟨-, rfl⟩ | ⟨d, d', -, -, -, rfl⟩
        · simp at hx
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; subst hx; trivial
      · trivial

/-- A run of the items on the slices the plan loads is a run on the full
states: each item gives the same result on its slice (`item_frame`), and
its writes keep the next state a slice (`item_writes`, `slice_applyAll`). -/
theorem lift_run (a : Principal) :
    ∀ {st' : St} {items : List BatchItem} {ws : List Write} {outs : List ItemOutcome},
      RunItems a st' items ws outs → ∀ st, Slice K st' st → Ctx s0 W.keys st → (∀ it ∈ items, Covered W it) →
        stSize st + 8 * items.length < Usize.max → RunItems a st items ws outs := by
  intro st' items ws outs h
  induction h with
  | nil => intro st _ _ _ _; exact .nil
  | @refused st0' it items ws outs s1' e hs1' ht' hr ih =>
    intro st hsl hc hcov hsz
    have hsz0 : stSize st < Usize.max := by simp only [List.length_cons] at hsz; omega
    obtain ⟨s1, rfl⟩ : ∃ s1, Snapshot.toSt s1 = st := ⟨snapOf st hsz0, toSt_snapOf st hsz0⟩
    have hsl1 : Slice K (Snapshot.toSt s1') (Snapshot.toSt s1) := by rw [hs1']; exact hsl
    have hfr := item_frame hK a hsl1 hc it (hcov it (by simp))
    exact .refused s1 e rfl (by rw [← hfr]; exact ht')
      (ih _ hsl hc (fun x hx => hcov x (by simp [hx])) (by simp only [List.length_cons] at hsz; omega))
  | @done st0' it items ws outs s1' w r hs1' ht' hr ih =>
    intro st hsl hc hcov hsz
    have hsz0 : stSize st < Usize.max := by simp only [List.length_cons] at hsz; omega
    obtain ⟨s1, rfl⟩ : ∃ s1, Snapshot.toSt s1 = st := ⟨snapOf st hsz0, toSt_snapOf st hsz0⟩
    have hsl1 : Slice K (Snapshot.toSt s1') (Snapshot.toSt s1) := by rw [hs1']; exact hsl
    have hcov1 := hcov it (by simp)
    have hfr := item_frame hK a hsl1 hc it hcov1
    have ht : transition (itemPrincipal a it) s1 (itemCmd it) = ok (.Ok (w, r)) := by
      rw [← hfr]; exact ht'
    obtain ⟨hkept, horig⟩ := item_writes hK a hc it hcov1 ht
    have hsl2 : Slice K (applyAll st0' w.val) (applyAll (Snapshot.toSt s1) w.val) := by
      rw [← hs1']; exact slice_applyAll w.val hsl1 hkept
    have hc2 : Ctx s0 W.keys (applyAll (Snapshot.toSt s1) w.val) :=
      ⟨Theorems.inv_preserved_cmd _ _ _ w r hc.inv ht (Theorems.itemCmd_ne_batch it),
        mem_applyAll w.val _ hc.mem horig⟩
    have hlen := item_len ht
    have hsz2 := stSize_applyAll (Snapshot.toSt s1) w.val
    exact .done s1 w r rfl ht
      (ih _ hsl2 hc2 (fun x hx => hcov x (by simp [hx])) (by simp only [List.length_cons] at hsz; omega))


end Items

theorem slice_size {K : Keep} {st' st : St} (h : Slice K st' st) : stSize st' ≤ stSize st := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [stSize, h1, h2, h3, h4, h5, h6, h7, h8]
  have := List.length_filter_le K.teams st.teams
  have := List.length_filter_le K.keys st.keys
  have := List.length_filter_le K.models st.models
  have := List.length_filter_le K.deployments st.deployments
  have := List.length_filter_le K.keyModels st.keyModels
  have := List.length_filter_le K.teamModels st.teamModels
  have := List.length_filter_le K.usage st.usage
  have := List.length_filter_le K.reservations st.reservations
  omega

/-- The frame theorem for `Batch`, on a snapshot that keeps the invariant and
leaves room in its vectors. -/
theorem batch_frame (a : Principal) (s : Snapshot) (items : alloc.vec.Vec BatchItem) (hinv : Inv (Snapshot.toSt s))
    (hfit : Fits s (.Batch items)) :
    transition a (Snapshot.load (planA (wantsA items.val).keys [] (wantsA items.val).res (wantsA items.val).names
      (wantsA items.val).m0 false) s) (.Batch items) = transition a s (.Batch items) := by
  have hs := load_slice s (wantsA items.val).keys [] (wantsA items.val).res (wantsA items.val).names
    (wantsA items.val).m0 false
  have hK := plan_keep s (wantsA items.val).keys [] (wantsA items.val).res (wantsA items.val).names
    (wantsA items.val).m0 false
  cases hm : a.master
  · simp only [transition]; unfold batch; simp [hm]
  · have hfit' : Fits (Snapshot.load (planA (wantsA items.val).keys [] (wantsA items.val).res (wantsA items.val).names
        (wantsA items.val).m0 false) s) (.Batch items) := by
      simp only [Commands.Fits] at hfit ⊢
      rw [size_toSt] at hfit ⊢
      have := slice_size hs
      omega
    obtain ⟨res', hres'⟩ := transition_total a _ _ hfit'
    obtain ⟨ws', rep', rfl⟩ := Theorems.batch_master_ok hm (by simpa only [transition] using hres')
    obtain ⟨-, W', outs', hr', hrun', hws', -⟩ := Theorems.batch_sequential a _ items ws' rep' hres'
    have hsz : stSize (Snapshot.toSt s) + 8 * items.val.length < Usize.max := by
      simp only [Commands.Fits] at hfit; rw [size_toSt] at hfit; exact hfit
    have hrun := lift_run hK a hrun' (Snapshot.toSt s) hs (ctx_init s _ hinv) (wants_cover items.val) hsz
    obtain ⟨ws, outs, hres, hws, houts⟩ := Theorems.batch_complete a s items W' outs'.val hm hfit hrun
    rw [hres', hres, hr']
    have e1 : ws' = ws := by apply alloc.vec.Vec.ext; rw [hws', hws]
    have e2 : outs' = outs := by apply alloc.vec.Vec.ext; exact houts.symm
    rw [e1, e2]

/-- The frame theorem: on what the plan of `c` loads, `transition` gives the
same result, writes and reply or refusal, as on the whole tenant. For a
`Batch`, on a snapshot that keeps the invariant and leaves room in its vectors
(every other command needs neither: `frame_cmd`). -/
theorem frame (a : Principal) (s : Snapshot) (c : Command) (plan : List (Read Val)) (hp : readsA a c = some plan)
    (hinv : Inv (Snapshot.toSt s)) (hfit : Fits s c) :
    transition a (Snapshot.load plan s) c = transition a s c := by
  cases c
  case Batch items =>
    simp only [readsA, Option.some.injEq] at hp
    subst hp
    exact batch_frame a s items hinv hfit
  all_goals exact frame_cmd a s _ plan hp (fun _ h => by cases h)

/-- End to end: when `read_plan a c` names a plan, rows that hold what each
of its reads returns from the tables of `s` decode to a snapshot on which
`transition` gives the same result as on `s`. This is what
`GatewayStore::load_for` does, given that PostgreSQL returns `Read.rows`
for each compiled read (tested). -/
theorem load_for_sound (a : Principal) (s : Snapshot) (c : Command) (v : alloc.vec.Vec h5i_app_sql.Read)
    (hr : read_plan a c = ok (some v)) (hinv : Inv (Snapshot.toSt s)) (hfit : Fits s c) (r : Rows)
    (hrows : ∀ t, t < 9 → Rows.tabs r t = load (v.val.map Read.abs) (Snapshot.enc s) t) :
    ∃ s', decode r = ok (some s') ∧ transition a s' c = transition a s c := by
  have hpl := reads_abs a c _ hr
  exact ⟨_, Schema.decode_load _ s r hrows, frame a s c _ (by rw [← hpl]; rfl) hinv hfit⟩

end gateway_kernel.Frame
