import Spec
/-!
# Specs of the kernel's helper functions

One `@[step]` spec per helper of `kernel/src/lib.rs`, stated on lists and
natural numbers in the vocabulary of `Spec.lean`, so that proofs about
`transition` can run `step*` through admission, settlement and management.

Helpers that take a vector of usage rows (`used`, `eligible`, `route`) are
specified for any vector, through `usedL`/`EligibleL`/`loadL`/`PrefersL`,
which are `Spec.usedIn`/`Eligible`/`load`/`Prefers` with the state's usage
list as an argument (`usedIn_eq`, `Eligible_iff`, ... are definitional).
`route_best` restates `route_spec` with `Spec.Best` for a snapshot.
-/
open Aeneas Aeneas.Std Result gateway_kernel gateway_kernel.Spec H5iAppLib

namespace gateway_kernel.Helpers

attribute [local simp] u64_val_eq

theorem sat_eq (n : Nat) : sat n = min n (2 ^ 64 - 1) := rfl

theorem sat_lt (n : Nat) : sat n < 2 ^ 64 := by rw [sat_eq]; omega

@[step] theorem sat_add_spec (a b : U64) : sat_add a b ⦃ r => r.val = sat (a.val + b.val) ⦄ := by
  unfold sat_add
  step*
  all_goals simp only [core.num.U64.MAX, U64.rMax, sat_eq] at *
  all_goals scalar_tac


theorem mul_check (a b : Nat) (hb : 0 < b) : (2 ^ 64 - 1) / b < a ↔ 2 ^ 64 ≤ a * b := by
  rw [Nat.div_lt_iff_lt_mul hb]; omega

@[step] theorem sat_mul_spec (a b : U64) : sat_mul a b ⦃ r => r.val = sat (a.val * b.val) ⦄ := by
  unfold sat_mul
  by_cases hb0 : b = 0#u64
  · subst hb0; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    step*; simp_all [sat_eq]
  · have hb : 0 < b.val := by
      have : b.val ≠ 0 := fun h => hb0 (by scalar_tac)
      omega
    have hne : (b != 0#u64) = true := by simpa using hb0
    simp only [hne, ↓reduceIte]
    step*
    · have : (2 ^ 64 - 1) / b.val < a.val := by simp only [U64.rMax] at *; scalar_tac
      have := (mul_check _ _ hb).1 this
      simp only [core.num.U64.MAX, U64.rMax, sat_eq] at *; scalar_tac
    · have : a.val ≤ (2 ^ 64 - 1) / b.val := by simp only [U64.rMax] at *; scalar_tac
      have := (Nat.le_div_iff_mul_le hb).1 this
      scalar_tac
    · have : a.val ≤ (2 ^ 64 - 1) / b.val := by simp only [U64.rMax] at *; scalar_tac
      have := (Nat.le_div_iff_mul_le hb).1 this
      simp only [sat_eq] at *; scalar_tac

@[step] theorem cost_spec (ic oc pt ct : U64) :
    cost ic oc pt ct ⦃ r => r.val = price ic.val oc.val pt.val ct.val ⦄ := by
  unfold cost; step*; simp_all [price]

theorem within_iff (x y z m : Nat) (hm : m ≤ MAX) :
    sat (sat (x + y) + z) ≤ m ↔ Within x y z m := by
  simp only [sat_eq, Within, MAX] at *; omega

@[step] theorem within_budget_spec (spend reserved amount maxb : U64) :
    within_budget spend reserved amount maxb ⦃ b =>
      (b = true ↔ Within spend.val reserved.val amount.val maxb.val) ⦄ := by
  unfold within_budget; step*
  rw [← within_iff _ _ _ _ (by simp only [MAX]; scalar_tac), ← i_post, ← i1_post]
  simp

@[step] theorem window_of_spec (now : U64) : window_of now ⦃ r => r.val = window now.val ⦄ := by
  unfold window_of WINDOW; step*; simp_all [window]

@[step] theorem under_limits_spec (r t rpm tpm : U64) :
    under_limits r t rpm tpm ⦃ b => (b = true ↔ r.val < rpm.val ∧ t.val < tpm.val) ⦄ := by
  unfold under_limits; step*

@[step] theorem before_spec (p1 l1 id1 p2 l2 id2 : U64) :
    before p1 l1 id1 p2 l2 id2 ⦃ b => (b = true ↔
      (p1.val < p2.val ∨ (p1.val = p2.val ∧ (l1.val < l2.val ∨ (l1.val = l2.val ∧ id1.val < id2.val))))) ⦄ := by
  unfold before; step*


/-! ## Lookups -/

@[step] theorem bytes_eq_spec (a b : alloc.vec.Vec U8) :
    bytes_eq a b ⦃ r => (r = true ↔ a.val = b.val) ⦄ := by
  unfold bytes_eq
  by_cases hl : a.len = b.len
  · simp only [hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have hlen : a.val.length = b.val.length := by
      have := congrArg (fun x : Usize => x.val) hl; simpa using this
    unfold bytes_eq_loop
    apply WP.spec_mono (loop_search (List.zip a.val b.val) (fun p => !decide (p.1 = p.2)) (fun r : Bool => r)
      (fun _ _ => false) true _ ?_ 0#usize (by simp))
    · intro r hr
      have h := search_all _ _ _ hr
      simp only [Bool.not_not] at h
      rw [h, zip_all_eq _ _ hlen]; simp
    · intro j hj; unfold bytes_eq_loop.body
      simp only [List.length_zip, hlen, Nat.min_self] at hj
      h5i_step
  · have hne : (a.len != b.len) = true := by simpa using hl
    simp only [hne, ↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_iff]
    intro h; apply hl; simp [alloc.vec.Vec.len, h]


@[step] theorem contains_spec (v : alloc.vec.Vec U64) (x : U64) :
    contains v x ⦃ r => (r = true ↔ x.val ∈ v.val.map (fun y => y.val)) ⦄ := by
  unfold contains contains_loop
  apply WP.spec_mono (loop_search v.val (fun y => decide (y = x)) (fun b : Bool => b)
    (fun _ _ => true) false _ ?_ 0#usize (by simp))
  · intro r hr
    rw [hr, searchFrom_const]
    simp
  · intro j hj; unfold contains_loop.body; h5i_step

@[step] theorem find_team_spec (v : alloc.vec.Vec Team) (id : U64) :
    find_team v id ⦃ o => o = v.val.find? (fun t => t.id.val = id.val) ⦄ := by
  unfold find_team find_team_loop
  apply WP.spec_mono (loop_search v.val (fun t => decide (t.id = id)) (fun o : Option Team => o)
    (fun _ t => some t) none _ ?_ 0#usize (by simp))
  · intro r hr; rw [search_find _ _ _ hr]; simp
  · intro j hj; unfold find_team_loop.body; h5i_step

@[step] theorem find_key_spec (v : alloc.vec.Vec Key) (id : U64) :
    find_key v id ⦃ o => o = v.val.find? (fun k => k.id.val = id.val) ⦄ := by
  unfold find_key find_key_loop
  apply WP.spec_mono (loop_search v.val (fun k => decide (k.id = id)) (fun o : Option Key => o)
    (fun _ k => some k) none _ ?_ 0#usize (by simp))
  · intro r hr; rw [search_find _ _ _ hr]; simp
  · intro j hj; unfold find_key_loop.body; h5i_step

@[step] theorem find_deployment_spec (v : alloc.vec.Vec Deployment) (id : U64) :
    find_deployment v id ⦃ o => o = v.val.find? (fun d => d.id.val = id.val) ⦄ := by
  unfold find_deployment find_deployment_loop
  apply WP.spec_mono (loop_search v.val (fun d => decide (d.id = id)) (fun o : Option Deployment => o)
    (fun _ d => some d) none _ ?_ 0#usize (by simp))
  · intro r hr; rw [search_find _ _ _ hr]; simp
  · intro j hj; unfold find_deployment_loop.body; h5i_step

@[step] theorem find_reservation_spec (v : alloc.vec.Vec Reservation) (id : U64) :
    find_reservation v id ⦃ o => o = v.val.find? (fun r => r.id.val = id.val) ⦄ := by
  unfold find_reservation find_reservation_loop
  apply WP.spec_mono (loop_search v.val (fun r => decide (r.id = id)) (fun o : Option Reservation => o)
    (fun _ r => some r) none _ ?_ 0#usize (by simp))
  · intro r hr; rw [search_find _ _ _ hr]; simp
  · intro j hj; unfold find_reservation_loop.body; h5i_step

@[step] theorem find_model_spec (v : alloc.vec.Vec Model) (nm : alloc.vec.Vec U8) :
    find_model v nm ⦃ o => o = (v.val.find? (fun m => m.name.val = nm.val)).map (fun m => m.id) ⦄ := by
  unfold find_model find_model_loop
  apply WP.spec_mono (loop_search v.val (fun m => decide (m.name.val = nm.val)) (fun o : Option U64 => o)
    (fun _ m => some m.id) none _ ?_ 0#usize (by simp))
  · intro r hr; rw [hr, searchFrom_find]; simp
  · intro j hj; unfold find_model_loop.body; h5i_step

@[step] theorem find_usage_spec (v : alloc.vec.Vec Usage) (scope id : U64) :
    find_usage v scope id ⦃ o => o = v.val.find? (fun u => u.scope.val = scope.val ∧ u.id.val = id.val) ⦄ := by
  unfold find_usage find_usage_loop
  apply WP.spec_mono (loop_search v.val (fun u => decide (u.scope = scope ∧ u.id = id)) (fun o : Option Usage => o)
    (fun _ u => some u) none _ ?_ 0#usize (by simp))
  · intro r hr; rw [search_find _ _ _ hr]; simp
  · intro j hj; unfold find_usage_loop.body; h5i_step

@[step] theorem key_may_spec (v : alloc.vec.Vec KeyModel) (key model : U64) :
    key_may v key model ⦃ r => (r = true ↔ ∃ g ∈ v.val, g.key = key ∧ g.model.val = model.val) ⦄ := by
  unfold key_may key_may_loop
  apply WP.spec_mono (loop_search v.val (fun g => decide (g.key = key ∧ g.model = model)) (fun b : Bool => b)
    (fun _ _ => true) false _ ?_ 0#usize (by simp))
  · intro r hr
    rw [hr, searchFrom_const]
    simp
  · intro j hj; unfold key_may_loop.body; h5i_step

@[step] theorem team_may_spec (v : alloc.vec.Vec TeamModel) (team model : U64) :
    team_may v team model ⦃ r => (r = true ↔ ∃ g ∈ v.val, g.team = team ∧ g.model.val = model.val) ⦄ := by
  unfold team_may team_may_loop
  apply WP.spec_mono (loop_search v.val (fun g => decide (g.team = team ∧ g.model = model)) (fun b : Bool => b)
    (fun _ _ => true) false _ ?_ 0#usize (by simp))
  · intro r hr
    rw [hr, searchFrom_const]
    simp
  · intro j hj; unfold team_may_loop.body; h5i_step

@[step] theorem team_in_use_spec (v : alloc.vec.Vec Key) (team : U64) :
    team_in_use v team ⦃ r => (r = true ↔ ∃ k ∈ v.val, k.team = team) ⦄ := by
  unfold team_in_use team_in_use_loop
  apply WP.spec_mono (loop_search v.val (fun k => decide (k.team = team)) (fun b : Bool => b)
    (fun _ _ => true) false _ ?_ 0#usize (by simp))
  · intro r hr
    rw [hr, searchFrom_const]
    simp
  · intro j hj; unfold team_in_use_loop.body; h5i_step

@[step] theorem models_of_key_spec (v : alloc.vec.Vec KeyModel) (key : U64) :
    models_of_key v key ⦃ out => out.val = (v.val.filter (fun g => g.key = key)).map (fun g => g.model) ⦄ := by
  unfold models_of_key models_of_key_loop
  apply WP.spec_mono (loop_fold v.val (fun out : alloc.vec.Vec U64 => out.val)
    (fun acc g => if g.key = key then acc ++ [g.model] else acc)
    (fun out i => out.val.length ≤ i) _ ?_ _ 0#usize (by simp) (by simp))
  · intro r hr; rw [hr]
    simpa using foldl_filter_map (fun g : KeyModel => decide (g.key = key)) (fun g => g.model) v.val []
  · intro out j hj hinv; unfold models_of_key_loop.body; h5i_step

@[step] theorem models_of_team_spec (v : alloc.vec.Vec TeamModel) (team : U64) :
    models_of_team v team ⦃ out => out.val = (v.val.filter (fun g => g.team = team)).map (fun g => g.model) ⦄ := by
  unfold models_of_team models_of_team_loop
  apply WP.spec_mono (loop_fold v.val (fun out : alloc.vec.Vec U64 => out.val)
    (fun acc g => if g.team = team then acc ++ [g.model] else acc)
    (fun out i => out.val.length ≤ i) _ ?_ _ 0#usize (by simp) (by simp))
  · intro r hr; rw [hr]
    simpa using foldl_filter_map (fun g : TeamModel => decide (g.team = team)) (fun g => g.model) v.val []
  · intro out j hj hinv; unfold models_of_team_loop.body; h5i_step


/-- `find_model` as a list function: the id of the first model named `nm`. -/
def findL (ms : List Model) (nm : alloc.vec.Vec U8) : Option U64 :=
  (ms.find? (fun m => m.name.val = nm.val)).map (fun m => m.id)

theorem findModel_toSt (s : Snapshot) (nm : alloc.vec.Vec U8) :
    (findL s.models.val nm).map (fun x => x.val) = findModel (Snapshot.toSt s) nm.val := by
  simp [findL, findModel, Snapshot.toSt, Option.map_map]; rfl

theorem findL_mem {ms : List Model} {nm : alloc.vec.Vec U8} {x : U64} (h : findL ms nm = some x) :
    ∃ m ∈ ms, m.id = x ∧ m.name = nm := by
  simp only [findL, Option.map_eq_some_iff] at h
  obtain ⟨m, hm, rfl⟩ := h
  have := find?_mem hm
  refine ⟨m, this.1, rfl, ?_⟩
  have h2 := this.2; simp at h2
  exact (alloc.vec.Vec.eq_iff _ _).2 h2

/-- `resolve_models` as a list function: every name's model id, or `none`
if some name is not a model. -/
def resolveL (ms : List Model) : List (alloc.vec.Vec U8) → Option (List U64)
  | [] => some []
  | n :: ns => match findL ms n with
    | none => none
    | some id => (resolveL ms ns).map (id :: ·)

theorem resolveL_some {ms : List Model} {ns : List (alloc.vec.Vec U8)} {ids : List U64}
    (h : resolveL ms ns = some ids) :
    ids.length = ns.length ∧ ∀ i (hi : i < ids.length) (hn : i < ns.length), findL ms ns[i] = some ids[i] := by
  induction ns generalizing ids with
  | nil => simp [resolveL] at h; subst h; simp
  | cons n ns ih =>
    simp only [resolveL] at h
    split at h
    · simp at h
    · rename_i id hid
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨ids', h', rfl⟩ := h
      obtain ⟨hl, hf⟩ := ih h'
      refine ⟨by simp [hl], ?_⟩
      intro i hi hn
      cases i with
      | zero => simpa using hid
      | succ i => simpa using hf i (by simp at hi; omega) (by simp at hn; omega)

theorem resolveL_mem {ms : List Model} {ns : List (alloc.vec.Vec U8)} {ids : List U64}
    (h : resolveL ms ns = some ids) : ∀ x ∈ ids, ∃ m ∈ ms, m.id = x := by
  induction ns generalizing ids with
  | nil => simp [resolveL] at h; subst h; simp
  | cons n ns ih =>
    simp only [resolveL] at h
    split at h
    · simp at h
    · rename_i id hid
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨ids', h', rfl⟩ := h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · obtain ⟨m, hm, he, -⟩ := findL_mem hid; exact ⟨m, hm, he⟩
      · exact ih h' x hx

theorem resolveL_none {ms : List Model} {ns : List (alloc.vec.Vec U8)} :
    resolveL ms ns = none ↔ ∃ n ∈ ns, findL ms n = none := by
  induction ns with
  | nil => simp [resolveL]
  | cons n ns ih =>
    simp only [resolveL, List.mem_cons, exists_eq_or_imp]
    split
    · rename_i h; simp [h]
    · rename_i id h; simp [h, ih]

@[step] theorem resolve_models_spec (v : alloc.vec.Vec Model) (names : alloc.vec.Vec (alloc.vec.Vec U8)) :
    resolve_models v names ⦃ r => match r with
      | .Ok ids => resolveL v.val names.val = some ids.val ∧ ids.val.length = names.val.length ∧
          ∀ x ∈ ids.val, ∃ m ∈ v.val, m.id = x
      | .Err e => e = .ModelNotFound ∧ resolveL v.val names.val = none ⦄ := by
  unfold resolve_models resolve_models_loop
  apply loop_idx_spec _ (fun x => x.2) names.val.length
    (fun x => x.1.val.length = x.2.val ∧
      resolveL v.val names.val = (resolveL v.val (names.val.drop x.2.val)).map (x.1.val ++ ·))
    _ ?_ _ ⟨by simp, by simp⟩ (by simp)
  rintro ⟨out, i⟩ ⟨hlen, heq⟩ hi
  simp only at hlen heq hi
  unfold resolve_models_loop.body
  step*
  · have hlt : i.val < names.val.length := by scalar_tac
    have hf : findL v.val names.val[i.val] = none := by
      simp only [findL]; rw [← v1_post, ← o_post]; assumption
    rw [heq, List.drop_eq_getElem_cons hlt]
    simp [resolveL, hf]
  · have hlt : i.val < names.val.length := by scalar_tac
    have hf : findL v.val names.val[i.val] = some id := by
      simp only [findL]; rw [← v1_post, ← o_post]; assumption
    refine ⟨by simp [out1_post, hlen, i2_post], ?_, by scalar_tac, by scalar_tac⟩
    rw [heq, List.drop_eq_getElem_cons hlt, i2_post]
    simp only [resolveL, hf, Option.map_map, out1_post]
    congr 1; funext x; simp
  · have hle : names.val.length ≤ i.val := by scalar_tac
    rw [List.drop_eq_nil_of_le hle] at heq
    have h1 : resolveL v.val names.val = some out.val := by simpa [resolveL] using heq
    exact ⟨h1, (resolveL_some h1).1, resolveL_mem h1⟩

theorem findTeam_toSt (s : Snapshot) (id : U64) :
    s.teams.val.find? (fun t => t.id.val = id.val) = findTeam (Snapshot.toSt s) id.val := rfl

theorem findKey_toSt (s : Snapshot) (id : U64) :
    s.keys.val.find? (fun k => k.id.val = id.val) = findKey (Snapshot.toSt s) id.val := rfl

theorem findDeployment_toSt (s : Snapshot) (id : U64) :
    s.deployments.val.find? (fun d => d.id.val = id.val) = findDeployment (Snapshot.toSt s) id.val := rfl

theorem findReservation_toSt (s : Snapshot) (id : U64) :
    s.reservations.val.find? (fun r => r.id.val = id.val) = findReservation (Snapshot.toSt s) id.val := rfl

/-! ## Saturating sums -/


theorem sat_sat_add (a b : Nat) : sat (sat a + b) = sat (a + b) := by
  simp only [sat_eq]; omega

/-- A saturating fold over the rows passing `P` is the capped sum. -/
theorem foldl_sat {α} (P : α → Bool) (f : α → Nat) (l : List α) (a : Nat) (ha : a ≤ MAX) :
    l.foldl (fun acc x => if P x then sat (acc + f x) else acc) a = sat (a + ((l.filter P).map f).sum) := by
  induction l generalizing a with
  | nil => simp [sat_eq]; omega
  | cons x xs ih =>
    rw [List.foldl_cons]
    by_cases hp : P x
    · simp only [hp, ↓reduceIte, List.filter_cons_of_pos, List.map_cons, List.sum_cons]
      rw [ih _ (by simp only [sat_eq, MAX]; omega), sat_sat_add, Nat.add_assoc]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, List.filter_cons_of_neg, not_false_eq_true]
      exact ih a ha

@[step] theorem in_flight_spec (v : alloc.vec.Vec Reservation) (key : U64) :
    in_flight v key ⦃ n => n.val = sat (v.val.filter (fun r => r.key_id.val = key.val)).length ⦄ := by
  unfold in_flight in_flight_loop
  apply WP.spec_mono (loop_fold v.val (fun n : U64 => n.val)
    (fun acc r => if decide (r.key_id.val = key.val) then sat (acc + (fun _ => 1) r) else acc)
    (fun _ _ => True) _ ?_ _ 0#usize (by simp) trivial)
  · intro r hr; rw [hr, foldl_sat _ _ _ _ (by simp)]; simp
  · intro n j hj _; unfold in_flight_loop.body; h5i_step

@[step] theorem reserved_by_key_spec (v : alloc.vec.Vec Reservation) (key : U64) :
    reserved_by_key v key ⦃ n => n.val =
      sat ((v.val.filter (fun r => r.key_id.val = key.val)).map (fun r => r.amount.val)).sum ⦄ := by
  unfold reserved_by_key reserved_by_key_loop
  apply WP.spec_mono (loop_fold v.val (fun n : U64 => n.val)
    (fun acc r => if decide (r.key_id.val = key.val) then sat (acc + r.amount.val) else acc)
    (fun _ _ => True) _ ?_ _ 0#usize (by simp) trivial)
  · intro r hr; rw [hr, foldl_sat _ _ _ _ (by simp)]; simp
  · intro n j hj _; unfold reserved_by_key_loop.body; h5i_step

@[step] theorem reserved_by_team_spec (v : alloc.vec.Vec Reservation) (team : U64) :
    reserved_by_team v team ⦃ n => n.val =
      sat ((v.val.filter (fun r => r.team.val = team.val)).map (fun r => r.amount.val)).sum ⦄ := by
  unfold reserved_by_team reserved_by_team_loop
  apply WP.spec_mono (loop_fold v.val (fun n : U64 => n.val)
    (fun acc r => if decide (r.team.val = team.val) then sat (acc + r.amount.val) else acc)
    (fun _ _ => True) _ ?_ _ 0#usize (by simp) trivial)
  · intro r hr; rw [hr, foldl_sat _ _ _ _ (by simp)]; simp
  · intro n j hj _; unfold reserved_by_team_loop.body; h5i_step

theorem inFlight_toSt (s : Snapshot) (key : U64) :
    sat (s.reservations.val.filter (fun r => r.key_id.val = key.val)).length = inFlight (Snapshot.toSt s) key.val := rfl

theorem reservedKey_toSt (s : Snapshot) (key : U64) :
    sat ((s.reservations.val.filter (fun r => r.key_id.val = key.val)).map (fun r => r.amount.val)).sum =
      reservedKey (Snapshot.toSt s) key.val := rfl

theorem reservedTeam_toSt (s : Snapshot) (team : U64) :
    sat ((s.reservations.val.filter (fun r => r.team.val = team.val)).map (fun r => r.amount.val)).sum =
      reservedTeam (Snapshot.toSt s) team.val := rfl


/-! ## Rate-limit windows

`Spec.usedIn`, `Spec.Eligible`, `Spec.load` and `Spec.Prefers` read only the
usage rows of the state. The `L` versions take those rows directly, so the
helper specs hold for any vector; `usedIn_eq` etc. are the (definitional)
bridges. -/

/-- `Spec.usedIn` on a list of usage rows. -/
def usedL (us : List Usage) (scope id w : Nat) : Nat × Nat :=
  match us.find? (fun u => u.scope.val = scope ∧ u.id.val = id) with
  | some u => if u.window.val = w then (u.requests.val, u.tokens.val) else (0, 0)
  | none => (0, 0)

theorem usedIn_eq (st : St) (scope id w : Nat) : usedIn st scope id w = usedL st.usage scope id w := rfl

theorem usedL_toSt (s : Snapshot) (scope id w : Nat) :
    usedL s.usage.val scope id w = usedIn (Snapshot.toSt s) scope id w := rfl

@[step] theorem used_spec (v : alloc.vec.Vec Usage) (scope id w : U64) :
    used v scope id w ⦃ p => p.1.val = (usedL v.val scope.val id.val w.val).1 ∧
      p.2.val = (usedL v.val scope.val id.val w.val).2 ⦄ := by
  unfold used usedL
  step*

@[step] theorem count_request_spec (v : alloc.vec.Vec Usage) (scope id w : U64) :
    count_request v scope id w ⦃ u => u.scope = scope ∧ u.id = id ∧ u.window = w ∧
      u.requests.val = sat ((usedL v.val scope.val id.val w.val).1 + 1) ∧
      u.tokens.val = (usedL v.val scope.val id.val w.val).2 ⦄ := by
  unfold count_request
  step*

@[step] theorem count_tokens_spec (v : alloc.vec.Vec Usage) (scope id w n : U64) :
    count_tokens v scope id w n ⦃ u => u.scope = scope ∧ u.id = id ∧ u.window = w ∧
      u.requests.val = (usedL v.val scope.val id.val w.val).1 ∧
      u.tokens.val = sat ((usedL v.val scope.val id.val w.val).2 + n.val) ⦄ := by
  unfold count_tokens
  step*

/-! ## Budget periods -/

@[step] theorem key_now_spec (k : Key) (now : U64) :
    key_now k now ⦃ k' =>
      k'.spend.val = spendAt k.spend.val k.budget_duration.val k.budget_reset_at.val now.val ∧
      k'.budget_reset_at.val = (if k.budget_duration.val ≠ 0 ∧ k.budget_reset_at.val ≤ now.val
        then sat (now.val + k.budget_duration.val) else k.budget_reset_at.val) ∧
      k' = { k with spend := k'.spend, budget_reset_at := k'.budget_reset_at } ⦄ := by
  unfold key_now
  step* <;> simp_all [spendAt]

@[step] theorem team_now_spec (t : Team) (now : U64) :
    team_now t now ⦃ t' =>
      t'.spend.val = spendAt t.spend.val t.budget_duration.val t.budget_reset_at.val now.val ∧
      t'.budget_reset_at.val = (if t.budget_duration.val ≠ 0 ∧ t.budget_reset_at.val ≤ now.val
        then sat (now.val + t.budget_duration.val) else t.budget_reset_at.val) ∧
      t' = { t with spend := t'.spend, budget_reset_at := t'.budget_reset_at } ⦄ := by
  unfold team_now
  step* <;> simp_all [spendAt]

/-- The failure count after one more retryable failure at `now`. -/
def failsAfter (d : Deployment) (now : Nat) : Nat :=
  if d.fail_window.val = window now then sat (d.fails.val + 1) else 1

@[step] theorem record_failure_spec (d : Deployment) (allowed cooldown now : U64) :
    record_failure d allowed cooldown now ⦃ d' =>
      d'.fail_window.val = window now.val ∧
      (if allowed.val < failsAfter d now.val
        then d'.fails.val = 0 ∧ d'.cooldown_until.val = sat (now.val + cooldown.val)
        else d'.fails.val = failsAfter d now.val ∧ d'.cooldown_until = d.cooldown_until) ∧
      d' = { d with fails := d'.fails, fail_window := d'.fail_window, cooldown_until := d'.cooldown_until } ⦄ := by
  unfold record_failure
  h5i_steps <;> (simp_all [failsAfter]; try omega)


/-! ## Routing -/

/-- `Spec.Eligible` on a list of usage rows. -/
def EligibleL (us : List Usage) (now m : Nat) (exclude : List Nat) (d : Deployment) : Prop :=
  d.model.val = m ∧ d.enabled = true ∧ d.cooldown_until.val ≤ now ∧ d.id.val ∉ exclude ∧
    (usedL us 2 d.id.val (window now)).1 < d.rpm.val ∧ (usedL us 2 d.id.val (window now)).2 < d.tpm.val

theorem Eligible_iff (st : St) (now m : Nat) (exclude : List Nat) (d : Deployment) :
    Eligible st now m exclude d ↔ EligibleL st.usage now m exclude d := Iff.rfl

@[step] theorem eligible_spec (d : Deployment) (usage : alloc.vec.Vec Usage) (model now : U64)
    (exclude : alloc.vec.Vec U64) :
    eligible d usage model now exclude ⦃ b =>
      (b = true ↔ EligibleL usage.val now.val model.val (exclude.val.map (fun x => x.val)) d) ⦄ := by
  unfold eligible SCOPE_DEPLOYMENT
  step* <;> simp_all [EligibleL]


/-- `Spec.load` on a list of usage rows. -/
def loadL (us : List Usage) (now : Nat) (d : Deployment) : Nat := (usedL us 2 d.id.val (window now)).1

/-- `Spec.Prefers` on a list of usage rows. -/
def PrefersL (us : List Usage) (now : Nat) (d e : Deployment) : Prop :=
  d.priority.val < e.priority.val ∨
    (d.priority.val = e.priority.val ∧
      (loadL us now d < loadL us now e ∨ (loadL us now d = loadL us now e ∧ d.id.val < e.id.val)))

theorem Prefers_iff (st : St) (now : Nat) (d e : Deployment) :
    Prefers st now d e ↔ PrefersL st.usage now d e := Iff.rfl

theorem load_eq (st : St) (now : Nat) (d : Deployment) : load st now d = loadL st.usage now d := rfl

theorem PrefersL_irrefl (us : List Usage) (now : Nat) (d : Deployment) : ¬ PrefersL us now d d := by
  simp [PrefersL]

theorem PrefersL_trans {us : List Usage} {now : Nat} {d e f : Deployment}
    (h1 : PrefersL us now d e) (h2 : PrefersL us now e f) : PrefersL us now d f := by
  unfold PrefersL at *; omega

/-- What `route` keeps after scanning `deps[0..i)`: no eligible deployment
yet, or the best one so far with its load. -/
def RouteInv (deps : List Deployment) (us : List Usage) (now m : Nat) (ex : List Nat)
    (best : Option Deployment) (bestLoad : Nat) (i : Nat) : Prop :=
  match best with
  | none => ∀ j (hj : j < deps.length), j < i → ¬ EligibleL us now m ex deps[j]
  | some b => b ∈ deps ∧ EligibleL us now m ex b ∧ bestLoad = loadL us now b ∧
      ∀ j (hj : j < deps.length), j < i → EligibleL us now m ex deps[j] → ¬ PrefersL us now deps[j] b

/-- What `route` returns. -/
def RoutePost (deps : List Deployment) (us : List Usage) (now m : Nat) (ex : List Nat) :
    Option Deployment → Prop
  | some d => d ∈ deps ∧ EligibleL us now m ex d ∧
      ∀ e ∈ deps, EligibleL us now m ex e → ¬ PrefersL us now e d
  | none => ∀ e ∈ deps, ¬ EligibleL us now m ex e

theorem route_loop_spec (deps : alloc.vec.Vec Deployment) (usage : alloc.vec.Vec Usage)
    (model now : U64) (exclude : alloc.vec.Vec U64) (w : U64) (hw : w.val = window now.val)
    (best : Option Deployment) (bestLoad : U64) (i : Usize)
    (hinv : RouteInv deps.val usage.val now.val model.val (exclude.val.map (fun x => x.val)) best bestLoad.val i.val)
    (hi : i.val ≤ deps.val.length) :
    route_loop deps usage model now exclude w best bestLoad i ⦃ o =>
      RoutePost deps.val usage.val now.val model.val (exclude.val.map (fun x => x.val)) o ⦄ := by
  unfold route_loop
  apply loop_idx_spec _ (fun x => x.2.2) deps.val.length
    (fun x => RouteInv deps.val usage.val now.val model.val (exclude.val.map (fun x => x.val)) x.1 x.2.1.val x.2.2.val)
    _ ?_ _ hinv hi
  rintro ⟨cur, bl, j⟩ hI hj
  simp only at hI hj
  unfold route_loop.body SCOPE_DEPLOYMENT
  h5i_steps
  case h_1 =>
    obtain ⟨load, tk⟩ := x
    simp only at x_post x_post1 ⊢
    have hl : load.val = loadL usage.val now.val d := by rw [x_post, hw]; rfl
    h5i_steps
    -- The first eligible deployment becomes the best.
    have hjl : j.val < deps.val.length := by scalar_tac
    have he : EligibleL usage.val now.val model.val (exclude.val.map (fun x => x.val)) d := b_post.1 ‹_›
    refine ⟨⟨by rw [d_post]; exact List.getElem_mem hjl, he, hl, ?_⟩, by scalar_tac, by scalar_tac⟩
    intro k hk hkj hek
    rcases Nat.lt_or_ge k j.val with hkj' | hkj'
    · exact absurd hek (hI k hk hkj')
    · have : k = j.val := by scalar_tac
      subst this; rw [← d_post]; exact PrefersL_irrefl _ _ _
  case h_2 =>
    rename_i b2
    obtain ⟨load, tk⟩ := x
    simp only at x_post x_post1 ⊢
    have hl : load.val = loadL usage.val now.val d := by rw [x_post, hw]; rfl
    obtain ⟨hb2m, hb2e, hb2l, hb2⟩ := hI
    have hjl : j.val < deps.val.length := by scalar_tac
    have he : EligibleL usage.val now.val model.val (exclude.val.map (fun x => x.val)) d := b_post.1 ‹_›
    h5i_steps
    · -- A preferred eligible deployment replaces the best.
      have hp : PrefersL usage.val now.val d b2 := by
        have := x_post.1 ‹_›; unfold PrefersL; rw [← hl, ← hb2l]; exact this
      refine ⟨⟨by rw [d_post]; exact List.getElem_mem hjl, he, hl, ?_⟩, by scalar_tac, by scalar_tac⟩
      intro k hk hkj hek
      rcases Nat.lt_or_ge k j.val with hkj' | hkj'
      · exact fun h => hb2 k hk hkj' hek (PrefersL_trans h hp)
      · have : k = j.val := by scalar_tac
        subst this; rw [← d_post]; exact PrefersL_irrefl _ _ _
    · -- The best stays.
      have hp : ¬ PrefersL usage.val now.val d b2 := by
        intro h; apply ‹¬x = true›; apply x_post.2; unfold PrefersL at h; rw [← hl, ← hb2l] at h; exact h
      refine ⟨⟨hb2m, hb2e, hb2l, ?_⟩, by scalar_tac, by scalar_tac⟩
      intro k hk hkj hek
      rcases Nat.lt_or_ge k j.val with hkj' | hkj'
      · exact hb2 k hk hkj' hek
      · have : k = j.val := by scalar_tac
        subst this; rw [← d_post]; exact hp
  -- D: an ineligible deployment changes nothing.
  · have hne : ¬ EligibleL usage.val now.val model.val (exclude.val.map (fun x => x.val)) d :=
      fun h => ‹¬b = true› (b_post.2 h)
    refine ⟨?_, by scalar_tac, by scalar_tac⟩
    cases cur with
    | none =>
      intro k hk hkj
      rcases Nat.lt_or_ge k j.val with hkj' | hkj'
      · exact hI k hk hkj'
      · have : k = j.val := by scalar_tac
        subst this; rw [← d_post]; exact hne
    | some b2 =>
      obtain ⟨hb2m, hb2e, hb2l, hb2⟩ := hI
      refine ⟨hb2m, hb2e, hb2l, ?_⟩
      intro k hk hkj hek
      rcases Nat.lt_or_ge k j.val with hkj' | hkj'
      · exact hb2 k hk hkj' hek
      · have : k = j.val := by scalar_tac
        subst this; rw [← d_post] at hek; exact absurd hek hne
  -- E: the end of the scan.
  · have hle : deps.val.length ≤ j.val := by scalar_tac
    cases cur with
    | none =>
      intro e he
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
      exact hI k hk (by omega)
    | some b2 =>
      obtain ⟨hb2m, hb2e, hb2l, hb2⟩ := hI
      refine ⟨hb2m, hb2e, ?_⟩
      intro e he
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
      exact hb2 k hk (by omega)

/-- `route` returns an eligible deployment of `deps` that no eligible
deployment of `deps` is preferred to, or `none` when none is eligible. -/
@[step] theorem route_spec (deps : alloc.vec.Vec Deployment) (usage : alloc.vec.Vec Usage)
    (model now : U64) (exclude : alloc.vec.Vec U64) :
    route deps usage model now exclude ⦃ o => match o with
      | some d => d ∈ deps.val ∧ EligibleL usage.val now.val model.val (exclude.val.map (fun x => x.val)) d ∧
          ∀ e ∈ deps.val, EligibleL usage.val now.val model.val (exclude.val.map (fun x => x.val)) e →
            ¬ PrefersL usage.val now.val e d
      | none => ∀ e ∈ deps.val, ¬ EligibleL usage.val now.val model.val (exclude.val.map (fun x => x.val)) e ⦄ := by
  unfold route
  step with window_of_spec as ⟨w, hw⟩
  apply WP.spec_mono (route_loop_spec deps usage model now exclude w hw none 0#u64 0#usize
    (fun j hj h => absurd h (by simp)) (by simp))
  intro o ho
  cases o <;> exact ho

/-- `route` on a snapshot's deployments and usage picks exactly a `Spec.Best`
deployment, and returns `none` only when no deployment is eligible. -/
theorem route_best (s : Snapshot) (model now : U64) (exclude : alloc.vec.Vec U64) :
    route s.deployments s.usage model now exclude ⦃ o => match o with
      | some d => Best (Snapshot.toSt s) now.val model.val (exclude.val.map (fun x => x.val)) d
      | none => ∀ e ∈ (Snapshot.toSt s).deployments,
          ¬ Eligible (Snapshot.toSt s) now.val model.val (exclude.val.map (fun x => x.val)) e ⦄ := by
  apply WP.spec_mono (route_spec s.deployments s.usage model now exclude)
  intro o ho
  cases o <;> exact ho

/-! ## Who may do what -/

@[step] theorem is_admin_spec (a : Principal) (s : Snapshot) :
    is_admin a s ⦃ b => (b = true ↔ IsAdmin (Snapshot.toSt s) a) ⦄ := by
  unfold is_admin
  cases hm : a.master
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step with find_key_spec as ⟨o, ho⟩
    have hk : findKey (Snapshot.toSt s) a.key.val = o := ho.symm
    simp only [IsAdmin, hm, Bool.false_eq_true, false_or, hk]
    rcases o with _ | k
    · simp
    · cases ha : k.admin <;> cases hb : k.blocked <;> simp [ha, hb]
  · simp [IsAdmin, hm]

@[step] theorem may_call_spec (s : Snapshot) (k : Key) (t : Option Team) (model : U64) :
    may_call s k t model ⦃ b => (b = true ↔ MayCall (Snapshot.toSt s) k t model.val) ⦄ := by
  unfold may_call
  step* <;> simp_all [MayCall, Snapshot.toSt]

@[step] theorem fresh_spec (s : Snapshot) :
    fresh s ⦃ r => match r with
      | .Ok id => s.settings.next_id.val < MAX ∧ id.val = s.settings.next_id.val + 1
      | .Err e => e = .Overflow ∧ s.settings.next_id.val = MAX ⦄ := by
  unfold fresh
  step* <;> (simp_all [core.num.U64.MAX, U64.rMax]; try scalar_tac)



@[step] theorem with_next_id_spec (st : Settings) (id : U64) :
    with_next_id st id ⦃ r => r = { st with next_id := id } ⦄ := by
  unfold with_next_id; step*

@[step] theorem one_spec (w : Write) : one w ⦃ v => v.val = [w] ⦄ := by
  unfold one; step*

end gateway_kernel.Helpers
