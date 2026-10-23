import Commands
/-!
# Theorems about the gateway

Admission is sound and complete for `Spec.AdmitByKey`; successful commands keep
`Spec.Inv`; management needs an admin and a plain key is confined to
`Spec.KeyMayWrite`; honest runs never exceed a budget; spend logs come exactly
from settlements and expiries.
-/
open Aeneas Aeneas.Std Result gateway_kernel gateway_kernel.Spec gateway_kernel.Helpers gateway_kernel.Commands H5iAppLib

namespace gateway_kernel.Theorems

set_option hygiene false in
/-- Close `(↑wsN).length < Usize.max` for the short write lists of a command. -/
macro "len_tac" : tactic => `(tactic| first
  | (simp only [ws5_post, ws4_post, ws3_post, ws2_post, ws1_post, ws_post, vec_new_val, List.length_append, List.length_cons, List.length_nil, List.nil_append]; omega)
  | (simp only [ws4_post, ws3_post, ws2_post, ws1_post, ws_post, vec_new_val, List.length_append, List.length_cons, List.length_nil, List.nil_append]; omega)
  | (simp only [ws3_post, ws2_post, ws1_post, ws_post, vec_new_val, List.length_append, List.length_cons, List.length_nil, List.nil_append]; omega)
  | (simp only [ws2_post, ws1_post, ws_post, vec_new_val, List.length_append, List.length_cons, List.length_nil, List.nil_append]; omega)
  | (simp only [ws1_post, ws_post, vec_new_val, List.length_append, List.length_cons, List.length_nil, List.nil_append]; omega))

/-! ## Admission -/

/-- What a successful `Admit` did: by a key, the whole policy `AdmitByKey`
held for the reservation it replied with; by the master key, the deployment is
`Best`. -/
theorem admit_sound (a : Principal) (s : Snapshot) (nm : alloc.vec.Vec U8) (pt mt : U64) (ex : alloc.vec.Vec U64)
    ws r (h : transition a s (.Admit nm pt mt ex) = ok (.Ok (ws, r))) :
    ∃ m : U64, findModel (Snapshot.toSt s) nm.val = some m.val ∧
      (a.master = false → ∃ (k : Key) (t : Option Team) (d : Deployment) (rid amt : U64),
        AdmitByKey (Snapshot.toSt s) a m.val pt.val mt.val (ex.val.map (·.val)) k t d amt.val ∧
        rid.val = s.settings.next_id.val + 1 ∧ r = .Admitted rid d.id amt) ∧
      (a.master = true → ∃ (d : Deployment) (rid amt : U64), Best (Snapshot.toSt s) a.now.val m.val (ex.val.map (·.val)) d ∧
        amt.val = price d.input_cost.val d.output_cost.val pt.val mt.val ∧
        rid.val = s.settings.next_id.val + 1 ∧ r = .Admitted rid d.id amt) := by
  obtain ⟨m, hm, hmaster, hkey⟩ := transition_effect h
  refine ⟨m, hm, fun hf => ?_, fun ht => ?_⟩
  · obtain ⟨k, t, d, id, amt, -, -, -, -, hA, hid, hr, -⟩ := hkey hf
    exact ⟨k, t, d, id, amt, hA, hid, hr⟩
  · obtain ⟨d, id, amt, -, hb, hamt, hid, hr, -⟩ := hmaster ht
    exact ⟨d, id, amt, hb, hamt, hid, hr⟩


/-- Deployment ids are unique, so at most one deployment is `Best`. -/
theorem best_unique {st : St} {now m : Nat} {ex : List Nat} {d e : Deployment}
    (hn : (st.deployments.map (·.id)).Nodup) (hd : Best st now m ex d) (he : Best st now m ex e) : d = e := by
  obtain ⟨hdm, hde, hdb⟩ := hd
  obtain ⟨hem, hee, heb⟩ := he
  have h1 := hdb e hem hee
  have h2 := heb d hdm hde
  have hid : d.id = e.id := by
    by_contra hne
    have hne' : d.id.val ≠ e.id.val := fun h => hne ((u64_val_eq _ _).1 h)
    simp only [Prefers] at h1 h2
    omega
  exact List.inj_on_of_nodup_map hn hdm hem hid

attribute [-step] key_now_spec team_now_spec
attribute [local step] key_now_spec' team_now_spec'

theorem admit_key_ok (a : Principal) (s : Snapshot) (m pt mt : U64) (ex : alloc.vec.Vec U64)
    (k0 : Key) (t0 : Option Team) (d0 : Deployment) (amt : Nat)
    (hA : AdmitByKey (Snapshot.toSt s) a m.val pt.val mt.val (ex.val.map (·.val)) k0 t0 d0 amt)
    (hn : ((Snapshot.toSt s).deployments.map (·.id)).Nodup) (hid : s.settings.next_id.val < MAX) :
    admit_key a s m pt mt ex ⦃ res => ∃ (ws : alloc.vec.Vec Write) (rid amt' : U64), res = .Ok (ws, .Admitted rid d0.id amt') ∧
      amt'.val = amt ∧ rid.val = s.settings.next_id.val + 1 ⦄ := by
  have hk : s.keys.val.find? (fun k => decide (k.id.val = a.key.val)) = some k0 := hA.key
  unfold admit_key
  have := usize_max_ge
  step*
  all_goals try len_tac
  all_goals
    have hkk : k = k0 := by
      have h := ‹o = some k›; rw [o_post, hk] at h; exact (Option.some.inj h).symm
    subst hkk
    try simp only [SCOPE_KEY, SCOPE_TEAM, SCOPE_DEPLOYMENT] at *
  -- Shared: the key is unblocked and unexpired.
  · exact absurd hA.unblocked (by simp [‹k.blocked = true›])
  · exfalso; have := ‹a.now ≥ k.expires_at›; have := hA.unexpired; scalar_tac
  -- No team.
  · exfalso; have h1 := ‹i ≥ k.max_parallel›; have h2 := hA.parallel
    rw [ge_iff_le, UScalar.le_equiv, i_post] at h1; rw [← inFlight_toSt] at h2; omega
  · exfalso; have := o1_post; rw [‹o1 = none›] at this; exact this d0 hA.best.1 hA.best.2.1
  · have hd : d = d0 := best_unique hn (by have := o1_post; rw [‹o1 = some d›] at this; exact this) hA.best
    subst hd
    have hid' := r_post; rw [‹r = _›] at hid'
    exact ⟨ws4, id, amount, rfl, by rw [amount_post, hA.priced], hid'.2⟩
  · exfalso
    have hd : d = d0 := best_unique hn (by have := o1_post; rw [‹o1 = some d›] at this; exact this) hA.best
    subst hd
    apply ‹¬b2 = true›
    rw [b2_post, i1_post, k2_post.2.1, k2_post.limits.2.2.2.1, reservedKey_toSt, amount_post, ← hA.priced]
    exact hA.key_budget
  · exfalso; apply ‹¬b1 = true›; rw [b1_post, kr_post, kr_post1, ‹w.val = window a.now.val›]
    exact ⟨hA.key_rpm, hA.key_tpm⟩
  · exfalso; apply ‹¬b = true›; rw [b_post]
    have := hA.no_team (by simp [‹k.team = 0#u64›]); rw [← this]; exact hA.may_call
  -- With a team.
  all_goals
    obtain ⟨team, hft, htb, ht0⟩ := hA.team (by simpa using ‹¬k.team = 0#u64›)
    rw [← findTeam_toSt] at hft
  · exfalso; have h := ‹o1 = none›; rw [o1_post, hft] at h; cases h
  all_goals
    have htt : t = team := by
      have h := ‹o1 = some t›; rw [o1_post, hft] at h; exact (Option.some.inj h).symm
    subst htt
  · exact absurd htb (by simp [‹t.blocked = true›])
  · exfalso; have h1 := ‹i ≥ k.max_parallel›; have h2 := hA.parallel
    rw [ge_iff_le, UScalar.le_equiv, i_post] at h1; rw [← inFlight_toSt] at h2; omega
  · exfalso; have := o2_post; rw [‹o2 = none›] at this; exact this d0 hA.best.1 hA.best.2.1
  · have hd : d = d0 := best_unique hn (by have := o2_post; rw [‹o2 = some d›] at this; exact this) hA.best
    subst hd
    have hid' := r_post; rw [‹r = _›] at hid'
    exact ⟨ws6, id, amount, rfl, by rw [amount_post, hA.priced], hid'.2⟩
  · exfalso
    have hd : d = d0 := best_unique hn (by have := o2_post; rw [‹o2 = some d›] at this; exact this) hA.best
    subst hd
    apply ‹¬b4 = true›
    rw [b4_post, i2_post, t2_post.2.1, t2_post.limits.2.1, reservedTeam_toSt, amount_post, ← hA.priced]
    exact hA.team_budget t ht0
  · exfalso
    have hd : d = d0 := best_unique hn (by have := o2_post; rw [‹o2 = some d›] at this; exact this) hA.best
    subst hd
    apply ‹¬b3 = true›
    rw [b3_post, i1_post, k2_post.2.1, k2_post.limits.2.2.2.1, reservedKey_toSt, amount_post, ← hA.priced]
    exact hA.key_budget
  · exfalso; apply ‹¬b2 = true›; rw [b2_post, tr_post, tr_post1, ‹w.val = window a.now.val›]
    exact hA.team_limits t ht0
  · exfalso; apply ‹¬b1 = true›; rw [b1_post, kr_post, kr_post1, ‹w.val = window a.now.val›]
    exact ⟨hA.key_rpm, hA.key_tpm⟩
  · exfalso; apply ‹¬b = true›; rw [b_post, ← ht0]; exact hA.may_call

/-- Completeness of admission: a key call that satisfies the whole policy
`AdmitByKey` (with deployment `d` and amount `amt`) is admitted, on `d`, for
`amt`, under the next id, unless ids are exhausted. Deployment ids are unique
(`Inv`), so the `Best` deployment is unique. -/
theorem admit_complete (a : Principal) (s : Snapshot) (nm : alloc.vec.Vec U8) (pt mt : U64) (ex : alloc.vec.Vec U64)
    (m : Nat) (k : Key) (t : Option Team) (d : Deployment) (amt : Nat)
    (hinv : Inv (Snapshot.toSt s)) (hm : findModel (Snapshot.toSt s) nm.val = some m)
    (hA : AdmitByKey (Snapshot.toSt s) a m pt.val mt.val (ex.val.map (·.val)) k t d amt)
    (hid : s.settings.next_id.val < MAX) :
    ∃ (ws : alloc.vec.Vec Write) (rid amt' : U64),
      transition a s (.Admit nm pt mt ex) = ok (.Ok (ws, .Admitted rid d.id amt')) ∧
      amt'.val = amt ∧ rid.val = s.settings.next_id.val + 1 := by
  have hfm := eq_ok_of_spec (find_model_spec s.models nm)
  have hm' := hm
  rw [← findModel_toSt] at hm'
  obtain ⟨m', hm1, hm2⟩ : ∃ m' : U64, findL s.models.val nm = some m' ∧ m'.val = m := by
    cases h : findL s.models.val nm with
    | none => rw [h] at hm'; cases hm'
    | some m' => rw [h] at hm'; exact ⟨m', rfl, Option.some.inj hm'⟩
  subst hm2
  have hk := admit_key_ok a s m' pt mt ex k t d amt hA hinv.deployments_nodup hid
  obtain ⟨res, hres, ws, rid, amt', rfl, h1, h2⟩ := (WP.spec_equiv_exists _ _).1 hk
  refine ⟨ws, rid, amt', ?_, h1, h2⟩
  have hfind : find_model s.models nm = ok (some m') := by rw [hfm]; exact congrArg ok hm1
  simp only [transition, admit, hfind, hA.not_master, bind_tc_ok]
  simpa using hres

/-! ## The invariant

Each lemma below says how one kind of change keeps `Inv`; the proof of
`inv_preserved` composes them along a command's writes. -/

section InvLemmas
variable {st : St}

theorem all_upsert {α κ : Type} [DecidableEq κ] {k : α → κ} {P : α → Prop} {l : List α} {x : α}
    (hl : ∀ y ∈ l, P y) (hx : P x) : ∀ y ∈ upsert k x l, P y := by
  intro y hy
  rcases mem_upsert_of hy with rfl | hy
  · exact hx
  · exact hl y hy

theorem inv_settings (hi : Inv st) (x : Settings) (hx : st.settings.next_id.val ≤ x.next_id.val) :
    Inv { st with settings := x } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, h10⟩
  · intro k hk; have := h6 k hk; simp only at *; omega
  · intro t ht; have := h7 t ht; simp only at *; omega
  · intro m hm; have := h8 m hm; simp only at *; omega
  · intro r hr; have := h9 r hr; simp only at *; omega

theorem inv_put_key (hi : Inv st) (k : Key) (h0 : 0 < k.id.val) (hk : k.id.val ≤ st.settings.next_id.val)
    (ht : k.team.val ≠ 0 → ∃ t ∈ st.teams, t.id = k.team) :
    Inv { st with keys := upsert (·.id) k st.keys } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact ⟨nodup_upsert _ _ h1, h2, h3, h4, h5, all_upsert h6 ⟨h0, hk⟩, h7, h8, h9, all_upsert h10 ht⟩

theorem inv_put_team (hi : Inv st) (t : Team) (h0 : 0 < t.id.val) (ht : t.id.val ≤ st.settings.next_id.val) :
    Inv { st with teams := upsert (·.id) t st.teams } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  refine ⟨h1, nodup_upsert _ _ h2, h3, h4, h5, h6, all_upsert h7 ⟨h0, ht⟩, h8, h9, ?_⟩
  intro k hk hk0
  obtain ⟨t', ht', he⟩ := h10 k hk hk0
  obtain ⟨z, hz, hze⟩ := key_kept (·.id) t ht'
  exact ⟨z, hz, hze.trans he⟩

theorem inv_put_model (hi : Inv st) (m : Model) (hm : m.id.val ≤ st.settings.next_id.val)
    (hf : ∀ y ∈ st.models, y.id ≠ m.id) :
    Inv { st with models := upsert (·.id) m st.models } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact ⟨h1, h2, nodup_upsert _ _ h3, h4, h5, h6, h7, all_upsert h8 hm, h9, h10⟩

theorem inv_put_deployment (hi : Inv st) (d : Deployment) :
    Inv { st with deployments := upsert (·.id) d st.deployments } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact ⟨h1, h2, h3, nodup_upsert _ _ h4, h5, h6, h7, h8, h9, h10⟩

theorem inv_put_reservation (hi : Inv st) (r : Reservation)
    (hr : r.id.val ≤ st.settings.next_id.val ∧ r.key_id.val ≤ st.settings.next_id.val ∧ r.team.val ≤ st.settings.next_id.val) :
    Inv { st with reservations := upsert (·.id) r st.reservations } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact ⟨h1, h2, h3, h4, nodup_upsert _ _ h5, h6, h7, h8, all_upsert h9 hr, h10⟩

theorem inv_del_key (hi : Inv st) (id : U64) : Inv { st with keys := st.keys.filter (fun k => k.id ≠ id) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact ⟨nodup_map_filter _ _ _ h1, h2, h3, h4, h5, fun k hk => h6 k (List.mem_of_mem_filter hk), h7, h8, h9,
    fun k hk => h10 k (List.mem_of_mem_filter hk)⟩

theorem inv_del_team (hi : Inv st) (id : U64) (hk : ∀ k ∈ st.keys, k.team ≠ id) :
    Inv { st with teams := st.teams.filter (fun t => t.id ≠ id) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  refine ⟨h1, nodup_map_filter _ _ _ h2, h3, h4, h5, h6, fun t ht => h7 t (List.mem_of_mem_filter ht), h8, h9, ?_⟩
  intro k hk' hk0
  obtain ⟨t, ht, he⟩ := h10 k hk' hk0
  refine ⟨t, List.mem_filter.2 ⟨ht, ?_⟩, he⟩
  simp only [ne_eq, decide_eq_true_eq]; rw [he]; exact hk k hk'

theorem inv_del_deployment (hi : Inv st) (id : U64) :
    Inv { st with deployments := st.deployments.filter (fun d => d.id ≠ id) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact ⟨h1, h2, h3, nodup_map_filter _ _ _ h4, h5, h6, h7, h8, h9, h10⟩

theorem inv_del_reservation (hi : Inv st) (id : U64) :
    Inv { st with reservations := st.reservations.filter (fun r => r.id ≠ id) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact ⟨h1, h2, h3, h4, nodup_map_filter _ _ _ h5, h6, h7, h8, fun r hr => h9 r (List.mem_of_mem_filter hr), h10⟩

theorem inv_usage (hi : Inv st) (u : List Usage) : Inv { st with usage := u } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem inv_grants (hi : Inv st) (a : List KeyModel) (b : List TeamModel) :
    Inv { st with keyModels := a, teamModels := b } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem findKey_mem {st : St} {n : Nat} {k : Key} (h : findKey st n = some k) : k ∈ st.keys ∧ k.id.val = n := by
  have := find?_mem h; simpa using this
theorem findTeam_mem {st : St} {n : Nat} {t : Team} (h : findTeam st n = some t) : t ∈ st.teams ∧ t.id.val = n := by
  have := find?_mem h; simpa using this
theorem findDeployment_mem {st : St} {n : Nat} {d : Deployment} (h : findDeployment st n = some d) :
    d ∈ st.deployments ∧ d.id.val = n := by
  have := find?_mem h; simpa using this
theorem findReservation_mem {st : St} {n : Nat} {r : Reservation} (h : findReservation st n = some r) :
    r ∈ st.reservations ∧ r.id.val = n := by
  have := find?_mem h; simpa using this

/-- Writes that only change model grants. -/
def IsGrant : Write → Prop
  | .PutKeyModel _ | .DelKeyModel _ _ | .PutTeamModel _ | .DelTeamModel _ _ => True
  | _ => False

theorem applyAll_grants (st : St) (l : List Write) (h : ∀ w ∈ l, IsGrant w) :
    ∃ a b, applyAll st l = { st with keyModels := a, teamModels := b } := by
  induction l generalizing st with
  | nil => exact ⟨st.keyModels, st.teamModels, rfl⟩
  | cons w l ih =>
    obtain ⟨a, b, he⟩ := ih (applyWrite st w) (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have hw := h w List.mem_cons_self
    simp only [applyAll, List.foldl_cons] at he ⊢
    rw [he]
    cases w <;> simp only [IsGrant] at hw <;> exact ⟨a, b, rfl⟩

theorem applyAll_append (st : St) (l1 l2 : List Write) : applyAll st (l1 ++ l2) = applyAll (applyAll st l1) l2 := by
  simp [applyAll, List.foldl_append]

end InvLemmas

theorem key_le {st : St} (hi : Inv st) {k : Key} (hk : k ∈ st.keys) :
    0 < k.id.val ∧ k.id.val ≤ st.settings.next_id.val ∧ k.team.val ≤ st.settings.next_id.val := by
  refine ⟨(hi.keys_fresh k hk).1, (hi.keys_fresh k hk).2, ?_⟩
  by_cases h0 : k.team.val = 0
  · omega
  · obtain ⟨t, ht, he⟩ := hi.key_team k hk h0
    rw [← he]; exact (hi.teams_fresh t ht).2

theorem grants_map {α : Type} (l : List α) (f : α → Write) (hf : ∀ x, IsGrant (f x)) : ∀ w ∈ l.map f, IsGrant w := by
  intro w hw; obtain ⟨x, -, rfl⟩ := List.mem_map.1 hw; exact hf x

theorem grants_append {l1 l2 : List Write} (h1 : ∀ w ∈ l1, IsGrant w) (h2 : ∀ w ∈ l2, IsGrant w) :
    ∀ w ∈ l1 ++ l2, IsGrant w := by
  intro w hw; rcases List.mem_append.1 hw with hw | hw
  · exact h1 w hw
  · exact h2 w hw

theorem applyAll_nil (st : St) : applyAll st [] = st := rfl

/-! ## Compaction

A batch commits `compactL` of its items' writes. In a table whose rows have
unique keys, a row ends up as the last write to it left it, so dropping the
writes a later write to the same row supersedes reaches the same rows (up to
their order in the table). -/

/-- The spend logs a write list sends to the outbox. -/
def emits (ws : List Write) : List SpendLog := ws.filterMap (fun w => match w with | .Emit l => some l | _ => none)

/-- The last write in `ws` to row `t`. -/
def lastW (t : U64 × U64 × U64) (ws : List Write) : Option Write := ws.reverse.find? (fun w => tgt w = some t)

theorem lastW_snoc (t : U64 × U64 × U64) (ws : List Write) (w : Write) :
    lastW t (ws ++ [w]) = if tgt w = some t then some w else lastW t ws := by
  by_cases h : tgt w = some t <;> simp [lastW, h]

theorem lastW_cons (t : U64 × U64 × U64) (w : Write) (ws : List Write) :
    lastW t (w :: ws) = (lastW t ws).or (if tgt w = some t then some w else none) := by
  unfold lastW
  rw [List.reverse_cons, List.find?_append]
  by_cases h : tgt w = some t <;> simp [h]

theorem lastW_compact (t : U64 × U64 × U64) (ws : List Write) : lastW t (compactL ws) = lastW t ws := by
  induction ws with
  | nil => rfl
  | cons w rest ih =>
    unfold compactL
    split
    · rename_i hov
      rw [ih, lastW_cons]
      unfold overwrittenL at hov
      split at hov
      · simp at hov
      · rename_i u hu
        obtain ⟨w', hw', ht'⟩ := List.any_eq_true.1 hov
        simp only [decide_eq_true_eq] at ht'
        by_cases htu : u = t
        · subst htu
          have : (lastW u rest).isSome := by
            unfold lastW
            rw [List.find?_isSome]
            exact ⟨w', List.mem_reverse.2 hw', by simp [ht']⟩
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 this
          simp [hx]
        · simp [hu, htu]
    · rw [lastW_cons, ih, lastW_cons]

theorem emits_compact (ws : List Write) : emits (compactL ws) = emits ws := by
  induction ws with
  | nil => rfl
  | cons w rest ih =>
    unfold compactL
    split
    · rename_i hov
      rw [ih]
      cases w <;> simp_all [emits, overwrittenL, tgt]
    · simp only [emits, List.filterMap_cons] at ih ⊢; rw [ih]

theorem compactL_sublist (ws : List Write) : (compactL ws).Sublist ws := by
  induction ws with
  | nil => exact .slnil
  | cons w rest ih =>
    unfold compactL
    split
    · exact ih.cons w
    · exact ih.cons_cons w

section Table
variable {α κ : Type} [DecidableEq κ] (tbl : St → List α) (kf : α → κ) (enc : κ → U64 × U64 × U64)
  (isPut : Write → Option α) (isDel : Write → Option κ)

/-- How the writes act on one table: a put upserts its row, a delete drops
its key, every other write leaves the table alone and targets no row of it. -/
structure TableOps : Prop where
  enc_inj : ∀ a b, enc a = enc b → a = b
  put : ∀ st w x, isPut w = some x → tbl (applyWrite st w) = upsert kf x (tbl st) ∧ tgt w = some (enc (kf x))
  del : ∀ st w k, isDel w = some k → isPut w = none ∧
    tbl (applyWrite st w) = (tbl st).filter (fun y => kf y ≠ k) ∧ tgt w = some (enc k)
  other : ∀ st w, isPut w = none → isDel w = none → tbl (applyWrite st w) = tbl st ∧ ∀ k, tgt w ≠ some (enc k)

variable {tbl kf enc isPut isDel}

theorem table_mem (ho : TableOps tbl kf enc isPut isDel) (st : St) (hn : ((tbl st).map kf).Nodup) (ws : List Write) :
    ((tbl (applyAll st ws)).map kf).Nodup ∧ ∀ x, (x ∈ tbl (applyAll st ws) ↔
      match lastW (enc (kf x)) ws with
      | none => x ∈ tbl st
      | some w => isPut w = some x) := by
  induction ws using List.reverseRecOn with
  | nil => exact ⟨hn, fun x => by simp [lastW, applyAll]⟩
  | append_singleton ws w ih =>
    obtain ⟨ihn, ihm⟩ := ih
    have happ : applyAll st (ws ++ [w]) = applyWrite (applyAll st ws) w := by
      simp [applyAll, List.foldl_append]
    rw [happ]
    cases hp : isPut w with
    | some y =>
      obtain ⟨he, ht⟩ := ho.put (applyAll st ws) w y hp
      rw [he]
      refine ⟨nodup_upsert _ _ ihn, fun x => ?_⟩
      rw [mem_upsert_iff ihn, lastW_snoc]
      by_cases hk : kf x = kf y
      · rw [if_pos (by rw [ht, hk])]
        simp only [hp, Option.some.injEq]
        constructor
        · rintro (rfl | ⟨-, h⟩)
          · rfl
          · exact absurd hk h
        · rintro rfl; exact .inl rfl
      · rw [if_neg (fun h => hk (ho.enc_inj _ _ (Option.some.inj (ht.symm.trans h))).symm), ← ihm x]
        constructor
        · rintro (rfl | ⟨h, -⟩)
          · exact absurd rfl hk
          · exact h
        · intro h; exact .inr ⟨h, hk⟩
    | none =>
      cases hd : isDel w with
      | some k =>
        obtain ⟨-, he, ht⟩ := ho.del (applyAll st ws) w k hd
        rw [he]
        refine ⟨nodup_map_filter _ _ _ ihn, fun x => ?_⟩
        rw [List.mem_filter, lastW_snoc]
        by_cases hk : kf x = k
        · rw [if_pos (by rw [ht, hk])]
          simp [hp, hk]
        · rw [if_neg (fun h => hk (ho.enc_inj _ _ (Option.some.inj (ht.symm.trans h))).symm), ← ihm x]
          simp [hk]
      | none =>
        obtain ⟨he, ht⟩ := ho.other (applyAll st ws) w hp hd
        rw [he]
        refine ⟨ihn, fun x => ?_⟩
        rw [lastW_snoc, if_neg (ht _), ihm x]

/-- In a table with unique keys, compacting the writes reaches the same rows. -/
theorem table_perm (ho : TableOps tbl kf enc isPut isDel) (st : St) (hn : ((tbl st).map kf).Nodup) (ws : List Write) :
    (tbl (applyAll st (compactL ws))).Perm (tbl (applyAll st ws)) := by
  obtain ⟨h1, m1⟩ := table_mem ho st hn (compactL ws)
  obtain ⟨h2, m2⟩ := table_mem ho st hn ws
  refine (List.perm_ext_iff_of_nodup h1.of_map h2.of_map).2 fun x => ?_
  rw [m1, m2, lastW_compact]

theorem table_nodup (ho : TableOps tbl kf enc isPut isDel) (st : St) (hn : ((tbl st).map kf).Nodup) (ws : List Write) :
    ((tbl (applyAll st ws)).map kf).Nodup := (table_mem ho st hn ws).1

end Table

theorem teamOps : TableOps St.teams (fun y : Team => y.id) (fun k : U64 => (1#u64, k, 0#u64))
    (fun w => match w with | .PutTeam x => some x | _ => none) (fun w => match w with | .DelTeam id => some id | _ => none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h; simp only [Prod.mk.injEq] at h; first | exact h.2.1 | exact Prod.ext h.2.1 h.2.2
  · intro st w x h; cases w <;> simp_all [applyWrite, tgt]
  · intro st w k h; cases w <;> simp_all [applyWrite, tgt] <;>
      (subst h; congr 1; funext g; apply Bool.eq_iff_iff.2; simp)
  · intro st w h1 h2; cases w <;> simp_all [applyWrite, tgt]

theorem keyOps : TableOps St.keys (fun y : Key => y.id) (fun k : U64 => (2#u64, k, 0#u64))
    (fun w => match w with | .PutKey x => some x | _ => none) (fun w => match w with | .DelKey id => some id | _ => none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h; simp only [Prod.mk.injEq] at h; first | exact h.2.1 | exact Prod.ext h.2.1 h.2.2
  · intro st w x h; cases w <;> simp_all [applyWrite, tgt]
  · intro st w k h; cases w <;> simp_all [applyWrite, tgt] <;>
      (subst h; congr 1; funext g; apply Bool.eq_iff_iff.2; simp)
  · intro st w h1 h2; cases w <;> simp_all [applyWrite, tgt]

theorem modelOps : TableOps St.models (fun y : Model => y.id) (fun k : U64 => (3#u64, k, 0#u64))
    (fun w => match w with | .PutModel x => some x | _ => none) (fun _ => (none : Option (U64))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h; simp only [Prod.mk.injEq] at h; first | exact h.2.1 | exact Prod.ext h.2.1 h.2.2
  · intro st w x h; cases w <;> simp_all [applyWrite, tgt]
  · intro st w k h; cases w <;> simp_all [applyWrite, tgt] <;>
      (subst h; congr 1; funext g; apply Bool.eq_iff_iff.2; simp)
  · intro st w h1 h2; cases w <;> simp_all [applyWrite, tgt]

theorem deploymentOps : TableOps St.deployments (fun y : Deployment => y.id) (fun k : U64 => (4#u64, k, 0#u64))
    (fun w => match w with | .PutDeployment x => some x | _ => none) (fun w => match w with | .DelDeployment id => some id | _ => none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h; simp only [Prod.mk.injEq] at h; first | exact h.2.1 | exact Prod.ext h.2.1 h.2.2
  · intro st w x h; cases w <;> simp_all [applyWrite, tgt]
  · intro st w k h; cases w <;> simp_all [applyWrite, tgt] <;>
      (subst h; congr 1; funext g; apply Bool.eq_iff_iff.2; simp)
  · intro st w h1 h2; cases w <;> simp_all [applyWrite, tgt]

theorem keyModelOps : TableOps St.keyModels (fun g : KeyModel => (g.key, g.model)) (fun k : U64 × U64 => (5#u64, k.1, k.2))
    (fun w => match w with | .PutKeyModel x => some x | _ => none) (fun w => match w with | .DelKeyModel k m => some (k, m) | _ => none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h; simp only [Prod.mk.injEq] at h; first | exact h.2.1 | exact Prod.ext h.2.1 h.2.2
  · intro st w x h; cases w <;> simp_all [applyWrite, tgt]
  · intro st w k h; cases w <;> simp_all [applyWrite, tgt] <;>
      (subst h; congr 1; funext g; apply Bool.eq_iff_iff.2; simp)
  · intro st w h1 h2; cases w <;> simp_all [applyWrite, tgt]

theorem teamModelOps : TableOps St.teamModels (fun g : TeamModel => (g.team, g.model)) (fun k : U64 × U64 => (6#u64, k.1, k.2))
    (fun w => match w with | .PutTeamModel x => some x | _ => none) (fun w => match w with | .DelTeamModel t m => some (t, m) | _ => none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h; simp only [Prod.mk.injEq] at h; first | exact h.2.1 | exact Prod.ext h.2.1 h.2.2
  · intro st w x h; cases w <;> simp_all [applyWrite, tgt]
  · intro st w k h; cases w <;> simp_all [applyWrite, tgt] <;>
      (subst h; congr 1; funext g; apply Bool.eq_iff_iff.2; simp)
  · intro st w h1 h2; cases w <;> simp_all [applyWrite, tgt]

theorem usageOps : TableOps St.usage (fun u : Usage => (u.scope, u.id)) (fun k : U64 × U64 => (7#u64, k.1, k.2))
    (fun w => match w with | .PutUsage x => some x | _ => none) (fun _ => (none : Option (U64 × U64))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h; simp only [Prod.mk.injEq] at h; first | exact h.2.1 | exact Prod.ext h.2.1 h.2.2
  · intro st w x h; cases w <;> simp_all [applyWrite, tgt]
  · intro st w k h; cases w <;> simp_all [applyWrite, tgt] <;>
      (subst h; congr 1; funext g; apply Bool.eq_iff_iff.2; simp)
  · intro st w h1 h2; cases w <;> simp_all [applyWrite, tgt]

theorem reservationOps : TableOps St.reservations (fun y : Reservation => y.id) (fun k : U64 => (8#u64, k, 0#u64))
    (fun w => match w with | .PutReservation x => some x | _ => none) (fun w => match w with | .DelReservation id => some id | _ => none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h; simp only [Prod.mk.injEq] at h; first | exact h.2.1 | exact Prod.ext h.2.1 h.2.2
  · intro st w x h; cases w <;> simp_all [applyWrite, tgt]
  · intro st w k h; cases w <;> simp_all [applyWrite, tgt] <;>
      (subst h; congr 1; funext g; apply Bool.eq_iff_iff.2; simp)
  · intro st w h1 h2; cases w <;> simp_all [applyWrite, tgt]

theorem settings_applyAll (st : St) (ws : List Write) :
    (applyAll st ws).settings = match lastW (0#u64, 0#u64, 0#u64) ws with
      | some (.SetSettings x) => x
      | _ => st.settings := by
  induction ws using List.reverseRecOn with
  | nil => simp [lastW, applyAll]
  | append_singleton ws w ih =>
    have happ : applyAll st (ws ++ [w]) = applyWrite (applyAll st ws) w := by
      simp [applyAll, List.foldl_append]
    rw [happ, lastW_snoc]
    by_cases ht : tgt w = some (0#u64, 0#u64, 0#u64)
    · rw [if_pos ht]
      cases w <;> simp_all [tgt, applyWrite]
    · rw [if_neg ht, ← ih]
      cases w <;> simp_all [tgt, applyWrite]

/-- With unique keys in every table, a batch's compacted writes reach the same
rows as its writes (up to their order in each table), and send the same
spend logs in the same order. -/
theorem compact_equiv (st : St) (ws : List Write) (hk : Keyed st) :
    Equiv (applyAll st (compactL ws)) (applyAll st ws) ∧ emits (compactL ws) = emits ws :=
  ⟨⟨by rw [settings_applyAll, settings_applyAll, lastW_compact],
    table_perm teamOps st hk.teams ws, table_perm keyOps st hk.keys ws,
    table_perm modelOps st hk.models ws, table_perm deploymentOps st hk.deployments ws,
    table_perm keyModelOps st hk.keyModels ws, table_perm teamModelOps st hk.teamModels ws,
    table_perm usageOps st hk.usage ws, table_perm reservationOps st hk.reservations ws⟩, emits_compact ws⟩

/-- Every write keeps keys unique in every table. -/
theorem keyed_applyAll {st : St} (hk : Keyed st) (ws : List Write) : Keyed (applyAll st ws) :=
  ⟨table_nodup teamOps st hk.teams ws, table_nodup keyOps st hk.keys ws,
    table_nodup modelOps st hk.models ws, table_nodup deploymentOps st hk.deployments ws,
    table_nodup keyModelOps st hk.keyModels ws, table_nodup teamModelOps st hk.teamModels ws,
    table_nodup usageOps st hk.usage ws, table_nodup reservationOps st hk.reservations ws⟩

/-- Every reachable state has unique keys in every table. -/
theorem reachable_keyed {st : St} (h : Reachable st) : Keyed st := by
  induction h with
  | init => constructor <;> simp [init]
  | step _ _ ih => exact keyed_applyAll ih _

/-- `Inv` only looks at the settings and five tables, as sets of rows. -/
theorem inv_of_perm {st st' : St} (hi : Inv st) (hs : st'.settings = st.settings) (hk : st'.keys.Perm st.keys)
    (ht : st'.teams.Perm st.teams) (hm : st'.models.Perm st.models) (hd : st'.deployments.Perm st.deployments)
    (hr : st'.reservations.Perm st.reservations) : Inv st' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  refine ⟨(hk.map _).nodup_iff.2 h1, (ht.map _).nodup_iff.2 h2, (hm.map _).nodup_iff.2 h3,
    (hd.map _).nodup_iff.2 h4, (hr.map _).nodup_iff.2 h5, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk'; rw [hs]; exact h6 k (hk.mem_iff.1 hk')
  · intro t ht'; rw [hs]; exact h7 t (ht.mem_iff.1 ht')
  · intro m hm'; rw [hs]; exact h8 m (hm.mem_iff.1 hm')
  · intro r hr'; rw [hs]; exact h9 r (hr.mem_iff.1 hr')
  · intro k hk' h0
    obtain ⟨t, ht', he⟩ := h10 k (hk.mem_iff.1 hk') h0
    exact ⟨t, ht.mem_iff.2 ht', he⟩

/-- Compacting keeps `Inv`: it only needs unique keys in the tables `Inv` constrains. -/
theorem compact_inv {st : St} {ws : List Write} (hi : Inv st) (h : Inv (applyAll st ws)) :
    Inv (applyAll st (compactL ws)) :=
  inv_of_perm h (by rw [settings_applyAll, settings_applyAll, lastW_compact])
    (table_perm keyOps st hi.keys_nodup ws) (table_perm teamOps st hi.teams_nodup ws)
    (table_perm modelOps st hi.models_nodup ws) (table_perm deploymentOps st hi.deployments_nodup ws)
    (table_perm reservationOps st hi.reservations_nodup ws)

theorem itemCmd_ne_batch (it : BatchItem) (items : alloc.vec.Vec BatchItem) : itemCmd it ≠ .Batch items := by
  obtain ⟨_, _, op⟩ := it; cases op <;> simp [itemCmd]

/-- Successful commands other than `Batch` keep the invariant. -/
theorem inv_preserved_cmd (a : Principal) (s : Snapshot) (c : Command) ws r
    (hinv : Inv (Snapshot.toSt s)) (h : transition a s c = ok (.Ok (ws, r))) (hb : ∀ items, c ≠ .Batch items) :
    Inv (applyAll (Snapshot.toSt s) ws.val) := by
  have he := transition_effect h
  generalize ws.val = l at he ⊢
  have hnx := hinv.keys_fresh
  cases c with
  | Admit nm pt mt ex =>
    obtain ⟨m, hm, hmas, hkey⟩ := he
    cases hma : a.master
    · obtain ⟨k, t, d, id, amt, k2, uk, ud, tw, hA, hid, hr, hkn, huk, htw, hud, rfl⟩ := hkey hma
      have hk := key_le hinv (findKey_mem hA.key).1
      have hkl := hkn.limits
      cases t with
      | none =>
        simp only [TeamWrites] at htw; subst htw
        simp only [applyAll, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, applyWrite]
        refine inv_put_reservation (inv_usage (inv_put_key (inv_settings hinv _ ?_) k2 ?_ ?_ ?_) _) _ ?_
        · simp [Snapshot.toSt, hid]
        · rw [hkl.1]; exact hk.1
        · simp only [Snapshot.toSt] at hk ⊢; rw [hkl.1]; omega
        · rw [hkl.2.1]; exact hinv.key_team k (findKey_mem hA.key).1
        · simp only [Snapshot.toSt] at hk ⊢; omega
      | some team =>
        obtain ⟨t2, ut, htn, hut, rfl⟩ := htw
        obtain ⟨team', hft, -, hte⟩ := hA.team (fun h0 => by have := hA.no_team h0; cases this)
        cases hte
        have ht := findTeam_mem hft
        have htf := hinv.teams_fresh _ ht.1
        simp only [applyAll, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, applyWrite]
        refine inv_put_reservation (inv_usage (inv_put_team (inv_put_key (inv_settings hinv _ ?_) k2 ?_ ?_ ?_) t2 ?_ ?_) _) _ ?_
        · simp [Snapshot.toSt, hid]
        · rw [hkl.1]; exact hk.1
        · simp only [Snapshot.toSt] at hk ⊢; rw [hkl.1]; omega
        · rw [hkl.2.1]; exact hinv.key_team k (findKey_mem hA.key).1
        · rw [htn.limits.1]; exact htf.1
        · simp only [Snapshot.toSt] at htf ⊢; rw [htn.limits.1]; omega
        · simp only [Snapshot.toSt] at hk ⊢; omega
    · obtain ⟨d, id, amt, u, hb, hamt, hid, hr, hu, rfl⟩ := hmas hma
      simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
      refine inv_put_reservation (inv_usage (inv_settings hinv _ ?_) _) _ ?_
      · simp [Snapshot.toSt, hid]
      · simp [Snapshot.toSt, hid]
  | Settle id pt ct status =>
    obtain ⟨rv, c, tokens, kw, tw, ud, dw, hfr, hmc, hc, htok, hr, hkw, htw, hud, hdw, rfl⟩ := he
    rcases hkw with ⟨-, rfl⟩ | ⟨k, k2, sp, uk, -, hfk, hkn, hsp, huk, rfl⟩ <;>
    rcases htw with ⟨-, rfl⟩ | ⟨t, t2, sp', ut, -, hft, htn, hsp', hut, rfl⟩ <;>
    rcases hdw with ⟨-, rfl⟩ | ⟨dd, dd', -, hfd, hfl, rfl⟩ <;>
    simp only [applyAll, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, List.append_nil,
      applyWrite]
    all_goals first
      | refine inv_put_deployment (inv_usage (inv_put_team (inv_put_key (inv_del_reservation hinv id) _ ?_ ?_ ?_) _ ?_ ?_) _) _
      | refine inv_usage (inv_put_team (inv_put_key (inv_del_reservation hinv id) _ ?_ ?_ ?_) _ ?_ ?_) _
      | refine inv_put_deployment (inv_usage (inv_put_key (inv_del_reservation hinv id) _ ?_ ?_ ?_) _) _
      | refine inv_usage (inv_put_key (inv_del_reservation hinv id) _ ?_ ?_ ?_) _
      | refine inv_put_deployment (inv_usage (inv_put_team (inv_del_reservation hinv id) _ ?_ ?_) _) _
      | refine inv_usage (inv_put_team (inv_del_reservation hinv id) _ ?_ ?_) _
      | refine inv_put_deployment (inv_usage (inv_del_reservation hinv id) _) _
      | refine inv_usage (inv_del_reservation hinv id) _
    all_goals dsimp only
    all_goals first
      | (rw [hkn.limits.1]; exact (key_le hinv (findKey_mem hfk).1).1)
      | (rw [hkn.limits.1]; exact (key_le hinv (findKey_mem hfk).1).2.1)
      | (rw [hkn.limits.2.1]; exact hinv.key_team _ (findKey_mem hfk).1)
      | (rw [htn.limits.1]; exact (hinv.teams_fresh _ (findTeam_mem hft).1).1)
      | (rw [htn.limits.1]; exact (hinv.teams_fresh _ (findTeam_mem hft).1).2)
  | Expire id =>
    obtain ⟨rv, -, -, -, -, -, rfl⟩ := he
    exact inv_del_reservation hinv id
  | KeyInfo _ => subst he; exact hinv
  | TeamInfo _ => subst he; exact hinv
  | ListModels => subst he; exact hinv
  | Dump => obtain ⟨-, rfl, -⟩ := he; exact hinv
  | Configure af cs ttl =>
    obtain ⟨-, -, rfl⟩ := he
    exact inv_settings hinv _ (le_refl _)
  | CreateTeam spec names =>
    obtain ⟨-, ids, id, ra, -, hid, -, -, rfl⟩ := he
    rw [← List.singleton_append, applyAll_append, applyAll_append]
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (applyAll (Snapshot.toSt s) [.PutTeam _])
      (ids.map (fun m => Write.PutTeamModel { team := id, model := m })) (grants_map ids _ (fun _ => trivial))
    rw [hg]
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    refine inv_put_team (inv_grants (inv_settings hinv _ ?_) ka tb) _ ?_ ?_
    · simp [Snapshot.toSt, hid]
    · simp [Snapshot.toSt, hid]
    · simp [Snapshot.toSt, hid]
  | UpdateTeam id p =>
    obtain ⟨-, t, t', hft, -, rfl, hid, -⟩ := he
    have ht := hinv.teams_fresh t (findTeam_mem hft).1
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    exact inv_put_team hinv t' (by rw [hid]; exact ht.1) (by rw [hid]; exact ht.2)
  | DeleteTeam id =>
    obtain ⟨-, t, -, hk, -, rfl⟩ := he
    rw [applyAll_append]
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (Snapshot.toSt s)
      ((s.team_models.val.filter (fun g => g.team = id)).map (fun g => Write.DelTeamModel id g.model))
      (grants_map _ _ (fun _ => trivial))
    rw [hg]
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    exact inv_del_team (inv_grants hinv ka tb) id hk
  | SetTeamModels id names =>
    obtain ⟨-, t, ids, -, -, -, rfl⟩ := he
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (Snapshot.toSt s)
      ((s.team_models.val.filter (fun g => g.team = id)).map (fun g => Write.DelTeamModel id g.model) ++
        ids.map (fun m => Write.PutTeamModel { team := id, model := m }))
      (grants_append (grants_map _ _ (fun _ => trivial)) (grants_map _ _ (fun _ => trivial)))
    rw [hg]
    exact inv_grants hinv ka tb
  | CreateKey spec names =>
    obtain ⟨-, ids, id, ra, hteam, -, hid, -, -, rfl⟩ := he
    rw [← List.singleton_append, applyAll_append, applyAll_append]
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (applyAll (Snapshot.toSt s) [.PutKey _])
      (ids.map (fun m => Write.PutKeyModel { key := id, model := m })) (grants_map ids _ (fun _ => trivial))
    rw [hg]
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    refine inv_put_key (inv_grants (inv_settings hinv _ ?_) ka tb) _ ?_ ?_ ?_
    · simp [Snapshot.toSt, hid]
    · simp [Snapshot.toSt, hid]
    · simp [Snapshot.toSt, hid]
    · intro h0
      obtain ⟨t, hft⟩ := hteam h0
      have ht := findTeam_mem hft
      exact ⟨t, ht.1, (u64_val_eq _ _).1 ht.2⟩
  | UpdateKey id p =>
    obtain ⟨-, k, k', hfk, -, rfl, hid, hteam, -⟩ := he
    have hk := key_le hinv (findKey_mem hfk).1
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    refine inv_put_key hinv k' (by rw [hid]; exact hk.1) (by rw [hid]; exact hk.2.1) ?_
    rw [hteam]; exact hinv.key_team k (findKey_mem hfk).1
  | DeleteKey id =>
    obtain ⟨-, k, -, -, rfl⟩ := he
    rw [applyAll_append]
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (Snapshot.toSt s)
      ((s.key_models.val.filter (fun g => g.key = id)).map (fun g => Write.DelKeyModel id g.model))
      (grants_map _ _ (fun _ => trivial))
    rw [hg]
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    exact inv_del_key (inv_grants hinv ka tb) id
  | SetKeyModels id names =>
    obtain ⟨-, k, ids, -, -, -, rfl⟩ := he
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (Snapshot.toSt s)
      ((s.key_models.val.filter (fun g => g.key = id)).map (fun g => Write.DelKeyModel id g.model) ++
        ids.map (fun m => Write.PutKeyModel { key := id, model := m }))
      (grants_append (grants_map _ _ (fun _ => trivial)) (grants_map _ _ (fun _ => trivial)))
    rw [hg]
    exact inv_grants hinv ka tb
  | ResetKeySpend id =>
    obtain ⟨-, k, hfk, -, rfl⟩ := he
    have hk := key_le hinv (findKey_mem hfk).1
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    exact inv_put_key hinv _ hk.1 hk.2.1 (hinv.key_team k (findKey_mem hfk).1)
  | UpsertDeployment nm spec =>
    obtain ⟨-, m, pre, -, hpre, rfl⟩ := he
    rcases hpre with ⟨-, rfl⟩ | ⟨-, hm, rfl⟩
    · simp only [applyAll, List.foldl_cons, List.foldl_nil, List.nil_append, applyWrite]
      exact inv_put_deployment hinv _
    · simp only [applyAll, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, applyWrite]
      refine inv_put_deployment (inv_put_model (inv_settings hinv _ ?_) _ ?_ ?_) _
      · simp [Snapshot.toSt, hm]
      · simp [Snapshot.toSt, hm]
      · intro y hy he
        have := hinv.models_fresh y hy
        rw [he] at this; simp only [Snapshot.toSt] at this; omega
  | DeleteDeployment id =>
    obtain ⟨-, d, -, -, rfl⟩ := he
    exact inv_del_deployment hinv id
  | Batch items => exact absurd rfl (hb items)

/-- A sequential run of batch items keeps the invariant. -/
theorem runItems_inv {a : Principal} {st : St} {items : List BatchItem} {W : List Write} {outs : List ItemOutcome}
    (h : RunItems a st items W outs) (hi : Inv st) : Inv (applyAll st W) := by
  induction h with
  | nil => exact hi
  | refused s e hs ht hr ih => exact ih hi
  | done s w r hs ht hr ih =>
    subst hs
    rw [applyAll_append]
    exact ih (inv_preserved_cmd _ s _ w r hi ht (itemCmd_ne_batch _))

/-- Successful commands keep the invariant. A batch reaches the end of the
sequential run of its items up to row order (`compact_inv`). -/
theorem inv_preserved (a : Principal) (s : Snapshot) (c : Command) ws r
    (hinv : Inv (Snapshot.toSt s)) (h : transition a s c = ok (.Ok (ws, r))) :
    Inv (applyAll (Snapshot.toSt s) ws.val) := by
  cases c with
  | Batch items =>
    obtain ⟨-, W, outs, -, hrun, hws⟩ := transition_effect h
    rw [hws]; exact compact_inv hinv (runItems_inv hrun hinv)
  | _ => exact inv_preserved_cmd a s _ ws r hinv h (by intro _ h; cases h)

theorem init_inv : Inv init := by
  constructor <;> simp [init]

/-- The invariant holds in every reachable state. -/
theorem reachable_inv {st : St} (h : Reachable st) : Inv st := by
  induction h with
  | init => exact init_inv
  | step _ ht ih => exact inv_preserved _ _ _ _ _ ih ht

/-! ## Authorization and confinement -/

/-- Every management command (all but `Admit`, `Settle`, `Expire`, `KeyInfo`,
`TeamInfo` and `ListModels`, so including `Batch`) succeeds only for an admin
(`Batch` only for the master key). -/
theorem manage_needs_admin (a : Principal) (s : Snapshot) (c : Command) ws r (hc : IsManage c)
    (h : transition a s c = ok (.Ok (ws, r))) : IsAdmin (Snapshot.toSt s) a := by
  cases c with
  | Batch items => exact .inl (transition_effect h).1
  | _ => first
    | exact absurd hc id
    | exact (manage_of h trivial (fun e => .inl (by simp))).1

theorem findReservation_fresh {st : St} (hi : Inv st) {n : Nat} (hn : st.settings.next_id.val < n) :
    findReservation st n = none := by
  apply List.find?_eq_none.2
  intro r hr he
  have := (hi.reservations_fresh r hr).1
  simp at he; omega

/-- A key that is not an admin only writes what `KeyMayWrite` allows: its own
key's and team's spend (never their limits), its own reservations, usage
counters, the id counter, a deployment's health, and spend logs. -/
theorem key_confined (a : Principal) (s : Snapshot) (c : Command) ws r
    (hna : ¬ IsAdmin (Snapshot.toSt s) a) (hinv : Inv (Snapshot.toSt s))
    (h : transition a s c = ok (.Ok (ws, r))) : ∀ w ∈ ws.val, KeyMayWrite (Snapshot.toSt s) a w := by
  have he := transition_effect h
  have hma : a.master = false := by
    cases hm : a.master
    · rfl
    · exact absurd (Or.inl hm) hna
  generalize ws.val = l at he ⊢
  cases c with
  | Admit nm pt mt ex =>
    obtain ⟨m, -, -, hkey⟩ := he
    obtain ⟨k, t, d, id, amt, k2, uk, ud, tw, hA, hid, hr, hkn, huk, htw, hud, rfl⟩ := hkey hma
    have hk := findKey_mem hA.key
    have hkl := hkn.limits
    have hka : k.id = a.key := (u64_val_eq _ _).1 hk.2
    have hpk : KeyMayWrite (Snapshot.toSt s) a (.PutKey k2) :=
      ⟨hkl.1.trans hka, k, by rw [hkl.1, hk.2]; exact hA.key, hkl⟩
    have hpr : ∀ R : Reservation, R.id = id → R.key_id = k.id → KeyMayWrite (Snapshot.toSt s) a (.PutReservation R) :=
      fun R h1 h2 => ⟨h2.trans hka, findReservation_fresh hinv (by rw [h1, hid]; simp [Snapshot.toSt])⟩
    intro w hw
    cases t with
    | none =>
      simp only [TeamWrites] at htw; subst htw
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · exact hpk
      · trivial
      · trivial
      · exact hpr _ rfl rfl
      · exact ⟨rfl, rfl, rfl⟩
    | some team =>
      obtain ⟨t2, ut, htn, hut, rfl⟩ := htw
      obtain ⟨team', hft, -, hte⟩ := hA.team (fun h0 => by have := hA.no_team h0; cases this)
      cases hte
      have ht := findTeam_mem hft
      have htl := htn.limits
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hpk
      · trivial
      · refine ⟨⟨_, by rw [htl.1, ht.2]; exact hft, htl⟩, Or.inl ⟨k, hA.key, ?_⟩⟩
        rw [htl.1]; exact ((u64_val_eq _ _).1 ht.2).symm
      · trivial
      · trivial
      · exact hpr _ rfl rfl
      · exact ⟨rfl, rfl, rfl⟩
  | Settle id pt ct status =>
    obtain ⟨rv, c, tokens, kw, tw, ud, dw, hfr, hmc, hc, htok, hr, hkw, htw, hud, hdw, rfl⟩ := he
    have hrk : rv.key_id = a.key := by
      rcases hmc with ⟨-, h⟩ | h
      · exact h
      · exact absurd h hna
    have hrm := findReservation_mem hfr
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with ((((rfl | hw) | hw) | rfl) | hw) | rfl
    · exact ⟨rv, hfr, hrk⟩
    · rcases hkw with ⟨-, rfl⟩ | ⟨k, k2, sp, uk, -, hfk, hkn, hsp, huk, rfl⟩
      · cases hw
      · have hk := findKey_mem hfk
        have hkl := hkn.limits
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · refine ⟨?_, k, ?_, ?_⟩
          · show k2.id = a.key
            rw [hkl.1, ← hrk]; exact (u64_val_eq _ _).1 hk.2
          · show findKey _ k2.id.val = some k
            rw [hkl.1, hk.2]; exact hfk
          · exact ⟨hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2.1, hkl.2.2.2.2.1, hkl.2.2.2.2.2.1, hkl.2.2.2.2.2.2.1,
              hkl.2.2.2.2.2.2.2.1, hkl.2.2.2.2.2.2.2.2.1, hkl.2.2.2.2.2.2.2.2.2.1, hkl.2.2.2.2.2.2.2.2.2.2.1,
              hkl.2.2.2.2.2.2.2.2.2.2.2⟩
        · trivial
    · rcases htw with ⟨-, rfl⟩ | ⟨t, t2, sp', ut, -, hft, htn, hsp', hut, rfl⟩
      · cases hw
      · have ht := findTeam_mem hft
        have htl := htn.limits
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · refine ⟨⟨t, ?_, ?_⟩, Or.inr ⟨rv, hrm.1, hrk, ?_⟩⟩
          · show findTeam _ t2.id.val = some t
            rw [htl.1, ht.2]; exact hft
          · exact ⟨htl.1, htl.2.1, htl.2.2.1, htl.2.2.2.1, htl.2.2.2.2.1, htl.2.2.2.2.2.1, htl.2.2.2.2.2.2⟩
          · show rv.team = t2.id
            rw [htl.1]; exact ((u64_val_eq _ _).1 ht.2).symm
        · trivial
    · trivial
    · rcases hdw with ⟨-, rfl⟩ | ⟨dd, dd', -, hfd, hfl, rfl⟩
      · cases hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw
        have hd := findDeployment_mem hfd
        have hid' : dd'.id = dd.id := by rw [hfl.1]
        refine ⟨dd, by rw [hid', hd.2]; exact hfd, ?_⟩
        rw [hfl.1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · trivial
  | Expire id =>
    obtain ⟨rv, hfr, hmc, -, -, rfl⟩ := he
    have hrk : rv.key_id = a.key := by
      rcases hmc with ⟨-, h⟩ | h
      · exact h
      · exact absurd h hna
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨rv, hfr, hrk⟩
    · trivial
  | KeyInfo _ => subst he; intro w hw; cases hw
  | TeamInfo _ => subst he; intro w hw; cases hw
  | ListModels => subst he; intro w hw; cases hw
  | Batch items => exact absurd (Or.inl he.1) hna
  | _ => exact absurd he.1 hna

/-! ## Budgets

`KeyWithin` caps the reserved sum at `MAX`; with a budget below `MAX` the cap
never applies, so we work with the plain sums `sumK`/`sumT`. -/

/-- What a key's (or a team's) reservations hold, uncapped. -/
def sumK (rs : List Reservation) (kid : Nat) : Nat := ((rs.filter (fun r => r.key_id.val = kid)).map (·.amount.val)).sum
def sumT (rs : List Reservation) (tid : Nat) : Nat := ((rs.filter (fun r => r.team.val = tid)).map (·.amount.val)).sum

def KOK (rs : List Reservation) (k : Key) : Prop := k.max_budget.val = MAX ∨ k.spend.val + sumK rs k.id.val ≤ k.max_budget.val
def TOK (rs : List Reservation) (t : Team) : Prop := t.max_budget.val = MAX ∨ t.spend.val + sumT rs t.id.val ≤ t.max_budget.val

/-- Every key and team within its budget, uncapped. -/
def BudgetOK (st : St) : Prop := (∀ k ∈ st.keys, KOK st.reservations k) ∧ (∀ t ∈ st.teams, TOK st.reservations t)

theorem within_sat (sp x a m : Nat) (hm : m ≤ MAX) : Within sp (sat x) a m ↔ m = MAX ∨ sp + x + a ≤ m := by
  simp only [Within, sat_eq, MAX] at *; omega

theorem keyWithin_iff (st : St) (k : Key) : KeyWithin st k ↔ KOK st.reservations k := by
  have : k.max_budget.val ≤ MAX := by have := k.max_budget.hBounds; simp only [MAX]; scalar_tac
  unfold KeyWithin KOK reservedKey reservationsOfKey
  rw [within_sat _ _ _ _ this]; simp [sumK]

theorem teamWithin_iff (st : St) (t : Team) : TeamWithin st t ↔ TOK st.reservations t := by
  have : t.max_budget.val ≤ MAX := by have := t.max_budget.hBounds; simp only [MAX]; scalar_tac
  unfold TeamWithin TOK reservedTeam reservationsOfTeam
  rw [within_sat _ _ _ _ this]; simp [sumT]

section Sums
variable {α : Type} (p q : α → Bool) (f : α → Nat)

theorem sum_filter_filter_le (l : List α) : (((l.filter q).filter p).map f).sum ≤ ((l.filter p).map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => by_cases hq : q x <;> by_cases hp : p x <;> simp only [List.filter_cons, hq, hp, ↓reduceIte, Bool.false_eq_true, List.map_cons, List.sum_cons] <;> omega

theorem sum_filter_remove (l : List α) (x : α) (hx : x ∈ l) (hp : p x = true) (hq : q x = false) :
    (((l.filter q).filter p).map f).sum + f x ≤ ((l.filter p).map f).sum := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · have := sum_filter_filter_le p q f ys
      simp only [List.filter_cons, hq, hp, ↓reduceIte, Bool.false_eq_true, List.map_cons, List.sum_cons]; omega
    · have := ih hx
      by_cases hqy : q y <;> by_cases hpy : p y <;> simp only [List.filter_cons, hqy, hpy, ↓reduceIte, Bool.false_eq_true, List.map_cons, List.sum_cons] <;> omega

end Sums

theorem sumK_append (rs : List Reservation) (R : Reservation) (kid : Nat) :
    sumK (rs ++ [R]) kid = sumK rs kid + (if R.key_id.val = kid then R.amount.val else 0) := by
  simp only [sumK, List.filter_append, List.map_append, List.sum_append]
  by_cases h : R.key_id.val = kid <;> simp [h]

theorem sumT_append (rs : List Reservation) (R : Reservation) (tid : Nat) :
    sumT (rs ++ [R]) tid = sumT rs tid + (if R.team.val = tid then R.amount.val else 0) := by
  simp only [sumT, List.filter_append, List.map_append, List.sum_append]
  by_cases h : R.team.val = tid <;> simp [h]

theorem sumK_filter_le (rs : List Reservation) (q : Reservation → Bool) (kid : Nat) :
    sumK (rs.filter q) kid ≤ sumK rs kid := sum_filter_filter_le _ _ _ rs

theorem sumT_filter_le (rs : List Reservation) (q : Reservation → Bool) (tid : Nat) :
    sumT (rs.filter q) tid ≤ sumT rs tid := sum_filter_filter_le _ _ _ rs

theorem sumK_zero (rs : List Reservation) (kid : Nat) (h : ∀ r ∈ rs, r.key_id.val ≠ kid) : sumK rs kid = 0 := by
  simp only [sumK]
  rw [List.filter_eq_nil_iff.2 (fun r hr => by simpa using h r hr)]; rfl

theorem sumT_zero (rs : List Reservation) (tid : Nat) (h : ∀ r ∈ rs, r.team.val ≠ tid) : sumT rs tid = 0 := by
  simp only [sumT]
  rw [List.filter_eq_nil_iff.2 (fun r hr => by simpa using h r hr)]; rfl

theorem KOK.mono {rs rs' : List Reservation} {k : Key} (h : KOK rs k) (hs : sumK rs' k.id.val ≤ sumK rs k.id.val) :
    KOK rs' k := by
  unfold KOK at *; omega

theorem TOK.mono {rs rs' : List Reservation} {t : Team} (h : TOK rs t) (hs : sumT rs' t.id.val ≤ sumT rs t.id.val) :
    TOK rs' t := by
  unfold TOK at *; omega

theorem budget_of {st st' : St} (hb : BudgetOK st) (hk : ∀ k ∈ st'.keys, k ∈ st.keys)
    (ht : ∀ t ∈ st'.teams, t ∈ st.teams)
    (hsk : ∀ k ∈ st'.keys, sumK st'.reservations k.id.val ≤ sumK st.reservations k.id.val)
    (hst : ∀ t ∈ st'.teams, sumT st'.reservations t.id.val ≤ sumT st.reservations t.id.val) : BudgetOK st' :=
  ⟨fun k h => (hb.1 k (hk k h)).mono (hsk k h), fun t h => (hb.2 t (ht t h)).mono (hst t h)⟩

theorem spendAt_le (sp d r n : Nat) : spendAt sp d r n ≤ sp := by
  unfold spendAt; split <;> omega

theorem sat_le (n : Nat) : sat n ≤ n := by simp only [sat_eq]; omega

theorem upsert_res_fresh {st : St} (hi : Inv st) (R : Reservation) (h : st.settings.next_id.val < R.id.val) :
    upsert (·.id) R st.reservations = st.reservations ++ [R] := by
  apply upsert_fresh
  intro y hy he
  have := (hi.reservations_fresh y hy).1
  rw [he] at this; omega

/-- A settlement's key write keeps every key within budget: the key loses the
reservation and gains at most its amount. -/
theorem settle_keys_ok {keys : List Key} {res : List Reservation} (hb : ∀ k ∈ keys, KOK res k)
    (hn : (keys.map (·.id)).Nodup) {k : Key} (hk : k ∈ keys) {rv : Reservation} (hrv : rv ∈ res)
    (hkid : rv.key_id.val = k.id.val) (K : Key) (hK : K.id = k.id) (hKm : K.max_budget = k.max_budget)
    (hKs : K.spend.val ≤ k.spend.val + rv.amount.val) :
    ∀ k' ∈ upsert (·.id) K keys, KOK (res.filter (fun r => r.id ≠ rv.id)) k' := by
  intro k' hk'
  rcases (mem_upsert_iff hn).1 hk' with rfl | ⟨hk'm, -⟩
  · have h1 := hb k hk
    have h2 := sum_filter_remove (fun r : Reservation => decide (r.key_id.val = k.id.val))
      (fun r => decide (r.id ≠ rv.id)) (fun r => r.amount.val) res rv hrv (by simpa using hkid) (by simp)
    unfold KOK at *; rw [hK, hKm]; unfold sumK at *; omega
  · exact (hb k' hk'm).mono (sumK_filter_le _ _ _)

theorem settle_teams_ok {teams : List Team} {res : List Reservation} (hb : ∀ t ∈ teams, TOK res t)
    (hn : (teams.map (·.id)).Nodup) {t : Team} (ht : t ∈ teams) {rv : Reservation} (hrv : rv ∈ res)
    (htid : rv.team.val = t.id.val) (T : Team) (hT : T.id = t.id) (hTm : T.max_budget = t.max_budget)
    (hTs : T.spend.val ≤ t.spend.val + rv.amount.val) :
    ∀ t' ∈ upsert (·.id) T teams, TOK (res.filter (fun r => r.id ≠ rv.id)) t' := by
  intro t' ht'
  rcases (mem_upsert_iff hn).1 ht' with rfl | ⟨ht'm, -⟩
  · have h1 := hb t ht
    have h2 := sum_filter_remove (fun r : Reservation => decide (r.team.val = t.id.val))
      (fun r => decide (r.id ≠ rv.id)) (fun r => r.amount.val) res rv hrv (by simpa using htid) (by simp)
    unfold TOK at *; rw [hT, hTm]; unfold sumT at *; omega
  · exact (hb t' ht'm).mono (sumT_filter_le _ _ _)

/-- An honest successful step other than `Batch` keeps every key and team within budget. -/
theorem budget_step_cmd (a : Principal) (s : Snapshot) (c : Command) ws r
    (hinv : Inv (Snapshot.toSt s)) (hb : BudgetOK (Snapshot.toSt s)) (hh : Honest (Snapshot.toSt s) a c)
    (h : transition a s c = ok (.Ok (ws, r))) (hbat : ∀ items, c ≠ .Batch items) :
    BudgetOK (applyAll (Snapshot.toSt s) ws.val) := by
  have he := transition_effect h
  generalize ws.val = l at he ⊢
  cases c with
  | Admit nm pt mt ex =>
    obtain ⟨m, hm, hmas, hkey⟩ := he
    cases hma : a.master
    · obtain ⟨k, t, d, id, amt, k2, uk, ud, tw, hA, hid, hr, hkn, huk, htw, hud, rfl⟩ := hkey hma
      have hkm := findKey_mem hA.key
      have hk := key_le hinv hkm.1
      have hkl := hkn.limits
      have hres := upsert_res_fresh hinv { id := id, key_id := k.id, team := k.team, deployment := d.id, model := m, input_cost := d.input_cost, output_cost := d.output_cost, amount := amt, created_at := a.now }
        (by simp only [Snapshot.toSt] at *; omega)
      have hkeys : ∀ k' ∈ upsert (·.id) k2 (Snapshot.toSt s).keys, KOK ((Snapshot.toSt s).reservations ++
          [{ id := id, key_id := k.id, team := k.team, deployment := d.id, model := m, input_cost := d.input_cost, output_cost := d.output_cost, amount := amt, created_at := a.now }]) k' := by
        intro k' hk'
        rcases (mem_upsert_iff hinv.keys_nodup).1 hk' with rfl | ⟨hk'm, hne⟩
        · have hw := hA.key_budget
          have hmb : k.max_budget.val ≤ MAX := by have := k.max_budget.hBounds; simp only [MAX]; scalar_tac
          unfold reservedKey reservationsOfKey at hw
          rw [within_sat _ _ _ _ hmb] at hw
          unfold KOK; rw [sumK_append, hkl.1, hkl.2.2.2.1, hkn.2.1]
          simp only [↓reduceIte]; unfold sumK; omega
        · refine (hb.1 k' hk'm).mono ?_
          rw [sumK_append]
          have : ¬ k.id.val = k'.id.val := fun e => hne (by rw [hkl.1]; exact ((u64_val_eq _ _).1 e).symm)
          simp [this]
      cases t with
      | none =>
        simp only [TeamWrites] at htw; subst htw
        simp only [applyAll, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, applyWrite]
        rw [hres]
        refine ⟨hkeys, fun t' ht' => (hb.2 t' ht').mono ?_⟩
        rw [sumT_append]
        have h0 : k.team.val = 0 := by
          by_contra h0; obtain ⟨_, _, _, he⟩ := hA.team h0; cases he
        have := (hinv.teams_fresh t' ht').1
        have : ¬ k.team.val = t'.id.val := by omega
        simp [this]
      | some team =>
        obtain ⟨t2, ut, htn, hut, rfl⟩ := htw
        obtain ⟨team', hft, -, hte⟩ := hA.team (fun h0 => by have := hA.no_team h0; cases this)
        cases hte
        have htm := findTeam_mem hft
        have htl := htn.limits
        simp only [applyAll, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, applyWrite]
        rw [hres]
        refine ⟨hkeys, ?_⟩
        intro t' ht'
        rcases (mem_upsert_iff hinv.teams_nodup).1 ht' with rfl | ⟨ht'm, hne⟩
        · have hw := hA.team_budget _ rfl
          have hmb : team.max_budget.val ≤ MAX := by have := team.max_budget.hBounds; simp only [MAX]; scalar_tac
          unfold reservedTeam reservationsOfTeam at hw
          rw [within_sat _ _ _ _ hmb] at hw
          unfold TOK; rw [sumT_append, htl.1, htl.2.1, htn.2.1]
          simp only [htm.2, ↓reduceIte] at hw ⊢; unfold sumT; omega
        · refine (hb.2 t' ht'm).mono ?_
          rw [sumT_append]
          have : ¬ k.team.val = t'.id.val := fun e => hne (by rw [htl.1]; exact ((u64_val_eq _ _).1 (htm.2.trans e)).symm)
          simp [this]
    · obtain ⟨d, id, amt, u, hbst, hamt, hid, hr, hu, rfl⟩ := hmas hma
      simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
      rw [upsert_res_fresh hinv _ (by simp only [Snapshot.toSt] at *; omega)]
      refine budget_of hb (fun k hk => hk) (fun t ht => ht) (fun k hk => ?_) (fun t ht => ?_)
      · have := (hinv.keys_fresh k hk).1
        simp only; rw [sumK_append, if_neg (by simp; omega)]; omega
      · have := (hinv.teams_fresh t ht).1
        simp only; rw [sumT_append, if_neg (by simp; omega)]; omega
  | Settle rid pt ct status =>
    obtain ⟨rv, c, tokens, kw, tw, ud, dw, hfr, hmc, hc, htok, hr, hkw, htw, hud, hdw, rfl⟩ := he
    have hrm := findReservation_mem hfr
    have hcost : c.val ≤ rv.amount.val := by rw [hc]; exact hh rv hfr
    have hrid : rv.id = rid := (u64_val_eq _ _).1 hrm.2
    subst hrid
    have hkeys0 : ∀ k ∈ (Snapshot.toSt s).keys, KOK ((Snapshot.toSt s).reservations.filter (fun r => r.id ≠ rv.id)) k :=
      fun k hk => (hb.1 k hk).mono (sumK_filter_le _ _ _)
    have hteams0 : ∀ t ∈ (Snapshot.toSt s).teams, TOK ((Snapshot.toSt s).reservations.filter (fun r => r.id ≠ rv.id)) t :=
      fun t ht => (hb.2 t ht).mono (sumT_filter_le _ _ _)
    rcases hkw with ⟨-, rfl⟩ | ⟨k, k2, sp, uk, -, hfk, hkn, hsp, huk, rfl⟩ <;>
    rcases htw with ⟨-, rfl⟩ | ⟨t, t2, sp', ut, -, hft, htn, hsp', hut, rfl⟩ <;>
    rcases hdw with ⟨-, rfl⟩ | ⟨dd, dd', -, hfd, hfl, rfl⟩ <;>
    simp only [applyAll, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, List.append_nil,
      applyWrite] <;>
    refine ⟨?_, ?_⟩
    all_goals first
      | exact hkeys0
      | exact hteams0
      | (refine settle_keys_ok hb.1 hinv.keys_nodup (findKey_mem hfk).1 hrm.1 (findKey_mem hfk).2.symm _
            hkn.limits.1 hkn.limits.2.2.2.1 ?_
         dsimp only; rw [hsp]
         have := sat_le (k2.spend.val + c.val)
         have := spendAt_le k.spend.val k.budget_duration.val k.budget_reset_at.val a.now.val
         rw [← hkn.2.1] at this; omega)
      | (refine settle_teams_ok hb.2 hinv.teams_nodup (findTeam_mem hft).1 hrm.1 (findTeam_mem hft).2.symm _
            htn.limits.1 htn.limits.2.1 ?_
         dsimp only; rw [hsp']
         have := sat_le (t2.spend.val + c.val)
         have := spendAt_le t.spend.val t.budget_duration.val t.budget_reset_at.val a.now.val
         rw [← htn.2.1] at this; omega)
  | Expire rid =>
    obtain ⟨rv, -, -, -, -, rfl⟩ := he
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    exact budget_of hb (fun k hk => hk) (fun t ht => ht) (fun k _ => sumK_filter_le _ _ _) (fun t _ => sumT_filter_le _ _ _)
  | KeyInfo _ => subst he; exact hb
  | TeamInfo _ => subst he; exact hb
  | ListModels => subst he; exact hb
  | Dump => obtain ⟨-, rfl, -⟩ := he; exact hb
  | Configure af cs ttl =>
    obtain ⟨-, -, rfl⟩ := he
    exact hb
  | CreateTeam spec names =>
    obtain ⟨-, ids, id, ra, -, hid, -, -, rfl⟩ := he
    rw [← List.singleton_append, applyAll_append, applyAll_append]
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (applyAll (Snapshot.toSt s) [.PutTeam _])
      (ids.map (fun m => Write.PutTeamModel { team := id, model := m })) (grants_map ids _ (fun _ => trivial))
    rw [hg]
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    refine ⟨hb.1, fun t ht => ?_⟩
    rcases mem_upsert_of ht with rfl | ht
    · right
      rw [sumT_zero _ _ (fun r hr => by have := (hinv.reservations_fresh r hr).2.2; simp only [Snapshot.toSt] at *; omega)]
      simp
    · exact hb.2 t ht
  | UpdateTeam id p =>
    obtain ⟨-, t, t', hft, -, rfl, hid, hsp, hmb, -⟩ := he
    have htm := findTeam_mem hft
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    refine ⟨hb.1, fun t'' ht'' => ?_⟩
    rcases (mem_upsert_iff hinv.teams_nodup).1 ht'' with rfl | ⟨ht'', -⟩
    · cases hp : p.max_budget with
      | none =>
        have := hb.2 t htm.1
        unfold TOK at *; rw [hid, hsp, hmb, hp]; exact this
      | some v =>
        have hw := hh v t hp hft
        have hv : v.val ≤ MAX := by have := v.hBounds; simp only [MAX]; scalar_tac
        unfold reservedTeam reservationsOfTeam at hw
        rw [within_sat _ _ _ _ hv] at hw
        unfold TOK; rw [hid, hsp, hmb, hp]; simp only [Option.getD_some]; unfold sumT; rw [htm.2]; omega
    · exact hb.2 t'' ht''
  | DeleteTeam id =>
    obtain ⟨-, t, -, hk, -, rfl⟩ := he
    rw [applyAll_append]
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (Snapshot.toSt s)
      ((s.team_models.val.filter (fun g => g.team = id)).map (fun g => Write.DelTeamModel id g.model))
      (grants_map _ _ (fun _ => trivial))
    rw [hg]
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    exact budget_of hb (fun k hk => hk) (fun t ht => List.mem_of_mem_filter ht) (fun _ _ => le_refl _) (fun _ _ => le_refl _)
  | SetTeamModels id names =>
    obtain ⟨-, t, ids, -, -, -, rfl⟩ := he
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (Snapshot.toSt s)
      ((s.team_models.val.filter (fun g => g.team = id)).map (fun g => Write.DelTeamModel id g.model) ++
        ids.map (fun m => Write.PutTeamModel { team := id, model := m }))
      (grants_append (grants_map _ _ (fun _ => trivial)) (grants_map _ _ (fun _ => trivial)))
    rw [hg]
    exact hb
  | CreateKey spec names =>
    obtain ⟨-, ids, id, ra, -, -, hid, -, -, rfl⟩ := he
    rw [← List.singleton_append, applyAll_append, applyAll_append]
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (applyAll (Snapshot.toSt s) [.PutKey _])
      (ids.map (fun m => Write.PutKeyModel { key := id, model := m })) (grants_map ids _ (fun _ => trivial))
    rw [hg]
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    refine ⟨fun k hk => ?_, hb.2⟩
    rcases mem_upsert_of hk with rfl | hk
    · right
      rw [sumK_zero _ _ (fun r hr => by have := (hinv.reservations_fresh r hr).2.1; simp only [Snapshot.toSt] at *; omega)]
      simp
    · exact hb.1 k hk
  | UpdateKey id p =>
    obtain ⟨-, k, k', hfk, -, rfl, hid, -, -, hsp, -, hmb, -⟩ := he
    have hkm := findKey_mem hfk
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    refine ⟨fun k'' hk'' => ?_, hb.2⟩
    rcases (mem_upsert_iff hinv.keys_nodup).1 hk'' with rfl | ⟨hk'', -⟩
    · cases hp : p.max_budget with
      | none =>
        have := hb.1 k hkm.1
        unfold KOK at *; rw [hid, hsp, hmb, hp]; exact this
      | some v =>
        have hw := hh v k hp hfk
        have hv : v.val ≤ MAX := by have := v.hBounds; simp only [MAX]; scalar_tac
        unfold reservedKey reservationsOfKey at hw
        rw [within_sat _ _ _ _ hv] at hw
        unfold KOK; rw [hid, hsp, hmb, hp]; simp only [Option.getD_some]; unfold sumK; rw [hkm.2]; omega
    · exact hb.1 k'' hk''
  | DeleteKey id =>
    obtain ⟨-, k, -, -, rfl⟩ := he
    rw [applyAll_append]
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (Snapshot.toSt s)
      ((s.key_models.val.filter (fun g => g.key = id)).map (fun g => Write.DelKeyModel id g.model))
      (grants_map _ _ (fun _ => trivial))
    rw [hg]
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    exact budget_of hb (fun k hk => List.mem_of_mem_filter hk) (fun t ht => ht) (fun _ _ => le_refl _) (fun _ _ => le_refl _)
  | SetKeyModels id names =>
    obtain ⟨-, k, ids, -, -, -, rfl⟩ := he
    obtain ⟨ka, tb, hg⟩ := applyAll_grants (Snapshot.toSt s)
      ((s.key_models.val.filter (fun g => g.key = id)).map (fun g => Write.DelKeyModel id g.model) ++
        ids.map (fun m => Write.PutKeyModel { key := id, model := m }))
      (grants_append (grants_map _ _ (fun _ => trivial)) (grants_map _ _ (fun _ => trivial)))
    rw [hg]
    exact hb
  | ResetKeySpend id =>
    obtain ⟨-, k, hfk, -, rfl⟩ := he
    have hkm := findKey_mem hfk
    simp only [applyAll, List.foldl_cons, List.foldl_nil, applyWrite]
    refine ⟨fun k'' hk'' => ?_, hb.2⟩
    rcases (mem_upsert_iff hinv.keys_nodup).1 hk'' with rfl | ⟨hk'', -⟩
    · have := hb.1 k hkm.1
      have h0 : (0#u64 : U64).val = 0 := rfl
      unfold KOK at *; dsimp only; omega
    · exact hb.1 k'' hk''
  | UpsertDeployment nm spec =>
    obtain ⟨-, m, pre, -, hpre, rfl⟩ := he
    rcases hpre with ⟨-, rfl⟩ | ⟨-, hm, rfl⟩
    · simp only [applyAll, List.foldl_cons, List.foldl_nil, List.nil_append, applyWrite]
      exact hb
    · simp only [applyAll, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, applyWrite]
      exact hb
  | DeleteDeployment id =>
    obtain ⟨-, d, -, -, rfl⟩ := he
    exact hb
  | Batch items => exact absurd rfl (hbat items)

/-- `BudgetOK` looks at keys, teams and reservations as sets of rows. -/
theorem budget_of_perm {st st' : St} (hb : BudgetOK st) (hk : st'.keys.Perm st.keys) (ht : st'.teams.Perm st.teams)
    (hr : st'.reservations.Perm st.reservations) : BudgetOK st' := by
  refine ⟨fun k hk' => ?_, fun t ht' => ?_⟩
  · have h := hb.1 k (hk.mem_iff.1 hk')
    have : sumK st'.reservations k.id.val = sumK st.reservations k.id.val :=
      ((hr.filter _).map _).sum_eq
    unfold KOK at *; rw [this]; exact h
  · have h := hb.2 t (ht.mem_iff.1 ht')
    have : sumT st'.reservations t.id.val = sumT st.reservations t.id.val :=
      ((hr.filter _).map _).sum_eq
    unfold TOK at *; rw [this]; exact h

theorem compact_budget {st : St} {ws : List Write} (hi : Inv st) (h : BudgetOK (applyAll st ws)) :
    BudgetOK (applyAll st (compactL ws)) :=
  budget_of_perm h (table_perm keyOps st hi.keys_nodup ws) (table_perm teamOps st hi.teams_nodup ws)
    (table_perm reservationOps st hi.reservations_nodup ws)

theorem item_honest {st : St} {p : Principal} {it : BatchItem}
    (h : match it.op with
      | .Settle rid prompt completion _ => SettleHonest st rid prompt completion
      | .Admit .. => True) : Honest st p (itemCmd it) := by
  obtain ⟨_, _, op⟩ := it
  cases op <;> simp_all [itemCmd, Honest]

/-- A sequential run of batch items whose settlements are honest where they
run keeps every key and team within budget. -/
theorem runItems_budget {a : Principal} {st : St} {items : List BatchItem} {W : List Write} {outs : List ItemOutcome}
    (h : RunItems a st items W outs) (hi : Inv st) (hb : BudgetOK st) (hh : BatchHonest a st items) :
    BudgetOK (applyAll st W) := by
  induction h with
  | nil => exact hb
  | refused s e hs ht hr ih =>
    simp only [BatchHonest] at hh
    exact ih hi hb (hh.2.1 s e hs ht)
  | done s w r hs ht hr ih =>
    subst hs
    simp only [BatchHonest] at hh
    rw [applyAll_append]
    exact ih (inv_preserved_cmd _ s _ w r hi ht (itemCmd_ne_batch _))
      (budget_step_cmd _ s _ w r hi hb (item_honest hh.1) ht (itemCmd_ne_batch _)) (hh.2.2 s w r rfl ht)

/-- An honest successful step keeps every key and team within budget. -/
theorem budget_step (a : Principal) (s : Snapshot) (c : Command) ws r
    (hinv : Inv (Snapshot.toSt s)) (hb : BudgetOK (Snapshot.toSt s)) (hh : Honest (Snapshot.toSt s) a c)
    (h : transition a s c = ok (.Ok (ws, r))) : BudgetOK (applyAll (Snapshot.toSt s) ws.val) := by
  cases c with
  | Batch items =>
    obtain ⟨-, W, outs, -, hrun, hws⟩ := transition_effect h
    rw [hws]; exact compact_budget hinv (runItems_budget hrun hinv hb hh)
  | _ => exact budget_step_cmd a s _ ws r hinv hb hh h (by intro _ h; cases h)

theorem reachable_of_honest {st : St} (h : ReachableHonest st) : Reachable st := by
  induction h with
  | init => exact .init
  | step _ _ ht ih => exact .step ih ht

theorem budget_ok {st : St} (h : ReachableHonest st) : BudgetOK st := by
  induction h with
  | init => exact ⟨fun k hk => by simp [init] at hk, fun t ht => by simp [init] at ht⟩
  | step hr hh ht ih => exact budget_step _ _ _ _ _ (reachable_inv (reachable_of_honest hr)) ih hh ht

/-- Budgets are never exceeded: in every state reached by honest steps, every
key and every team holds its spend plus its reservations within its budget. -/
theorem budget_never_exceeded {st : St} (h : ReachableHonest st) :
    (∀ k ∈ st.keys, KeyWithin st k) ∧ (∀ t ∈ st.teams, TeamWithin st t) :=
  ⟨fun k hk => (keyWithin_iff st k).2 ((budget_ok h).1 k hk),
   fun t ht => (teamWithin_iff st t).2 ((budget_ok h).2 t ht)⟩

/-! ## Spend logs -/

/-- A successful `Settle` emits exactly one spend log: for its reservation,
with the cost it replies. -/
theorem settle_logged (a : Principal) (s : Snapshot) (rid pt ct : U64) (status : CallStatus) ws r
    (h : transition a s (.Settle rid pt ct status) = ok (.Ok (ws, r))) :
    ∃ (log : SpendLog) (c : U64), emits ws.val = [log] ∧ r = .Settled c ∧ log.cost = c ∧ log.reservation = rid ∧
      log.status = status := by
  obtain ⟨rv, c, tokens, kw, tw, ud, dw, hfr, hmc, hc, htok, hr, hkw, htw, hud, hdw, hws⟩ := transition_effect h
  refine ⟨{ reservation := rid, key := rv.key_id, team := rv.team, deployment := rv.deployment, model := rv.model, prompt_tokens := pt, completion_tokens := ct, cost := c, «at» := a.now, status := status }, c, ?_, hr, rfl, rfl, rfl⟩
  rw [hws]
  rcases hkw with ⟨-, rfl⟩ | ⟨k, k2, sp, uk, -, -, -, -, -, rfl⟩ <;>
  rcases htw with ⟨-, rfl⟩ | ⟨t, t2, sp', ut, -, -, -, -, -, rfl⟩ <;>
  rcases hdw with ⟨-, rfl⟩ | ⟨dd, dd', -, -, -, rfl⟩ <;>
  simp [emits]

/-- `emit_origin` for every command but `Batch`. -/
theorem emit_origin_cmd (a : Principal) (s : Snapshot) (c : Command) ws r
    (h : transition a s c = ok (.Ok (ws, r))) (log : SpendLog) (hl : .Emit log ∈ ws.val)
    (hbat : ∀ items, c ≠ .Batch items) :
    (∃ rid pt ct status cost, c = .Settle rid pt ct status ∧ r = .Settled cost ∧ log.reservation = rid ∧
      log.cost = cost) ∨
    (∃ rid, c = .Expire rid ∧ r = .Settled 0#u64 ∧ log.reservation = rid ∧ log.cost = 0#u64 ∧
      log.status = .Expired) := by
  have he := transition_effect h
  generalize ws.val = l at he hl
  cases c with
  | Settle rid pt ct status =>
    obtain ⟨rv, cost, tokens, kw, tw, ud, dw, hfr, hmc, hc, htok, hr, hkw, htw, hud, hdw, rfl⟩ := he
    left
    refine ⟨rid, pt, ct, status, cost, rfl, hr, ?_⟩
    rcases hkw with ⟨-, rfl⟩ | ⟨k, k2, sp, uk, -, -, -, -, -, rfl⟩ <;>
    rcases htw with ⟨-, rfl⟩ | ⟨t, t2, sp', ut, -, -, -, -, -, rfl⟩ <;>
    rcases hdw with ⟨-, rfl⟩ | ⟨dd, dd', -, -, -, rfl⟩ <;>
    simp at hl <;> subst hl <;> exact ⟨rfl, rfl⟩
  | Expire rid =>
    obtain ⟨rv, -, -, -, hr, rfl⟩ := he
    right
    simp at hl; subst hl
    exact ⟨rid, rfl, hr, rfl, rfl, rfl⟩
  | Admit nm pt mt ex =>
    obtain ⟨m, -, hmas, hkey⟩ := he
    exfalso
    cases hma : a.master
    · obtain ⟨k, t, d, id, amt, k2, uk, ud, tw, -, -, -, -, -, htw, -, rfl⟩ := hkey hma
      cases t with
      | none => simp only [TeamWrites] at htw; subst htw; simp at hl
      | some team => obtain ⟨t2, ut, -, -, rfl⟩ := htw; simp at hl
    · obtain ⟨d, id, amt, u, -, -, -, -, -, rfl⟩ := hmas hma
      simp at hl
  | KeyInfo _ => subst he; cases hl
  | TeamInfo _ => subst he; cases hl
  | ListModels => subst he; cases hl
  | Dump => obtain ⟨-, rfl, -⟩ := he; cases hl
  | Configure x1 x2 x3 => obtain ⟨-, -, rfl⟩ := he; simp at hl
  | CreateTeam x1 x2 => obtain ⟨-, ids, id, ra, -, -, -, -, rfl⟩ := he; simp at hl
  | UpdateTeam x1 x2 => obtain ⟨-, t, t', -, -, rfl, -⟩ := he; simp at hl
  | DeleteTeam x1 => obtain ⟨-, t, -, -, -, rfl⟩ := he; simp at hl
  | SetTeamModels x1 x2 => obtain ⟨-, t, ids, -, -, -, rfl⟩ := he; simp at hl
  | CreateKey x1 x2 => obtain ⟨-, ids, id, ra, -, -, -, -, -, rfl⟩ := he; simp at hl
  | UpdateKey x1 x2 => obtain ⟨-, k, k', -, -, rfl, -⟩ := he; simp at hl
  | DeleteKey x1 => obtain ⟨-, k, -, -, rfl⟩ := he; simp at hl
  | SetKeyModels x1 x2 => obtain ⟨-, k, ids, -, -, -, rfl⟩ := he; simp at hl
  | ResetKeySpend x1 => obtain ⟨-, k, -, -, rfl⟩ := he; simp at hl
  | UpsertDeployment x1 x2 =>
    obtain ⟨-, m, pre, -, hpre, rfl⟩ := he
    rcases hpre with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp at hl
  | DeleteDeployment x1 => obtain ⟨-, d, -, -, rfl⟩ := he; simp at hl
  | Batch items => exact absurd rfl (hbat items)

/-- A spend log written by a batch item comes from a `Settle` item, for its
reservation, with the cost it replied. -/
theorem emit_item {p : Principal} {s : Snapshot} {it : BatchItem} {w : alloc.vec.Vec Write} {r : Reply}
    (h : transition p s (itemCmd it) = ok (.Ok (w, r))) (log : SpendLog) (hl : .Emit log ∈ w.val) :
    ∃ rid pt ct status cost, it.op = .Settle rid pt ct status ∧ r = .Settled cost ∧ log.reservation = rid ∧
      log.cost = cost := by
  rcases emit_origin_cmd p s _ w r h log hl (itemCmd_ne_batch it) with
    ⟨rid, pt, ct, status, cost, hc, hr, h1, h2⟩ | ⟨rid, hc, -⟩
  · obtain ⟨_, _, op⟩ := it
    cases op with
    | Admit => simp [itemCmd] at hc
    | Settle => simp only [itemCmd, Command.Settle.injEq] at hc; obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
                exact ⟨_, _, _, _, cost, rfl, hr, h1, h2⟩
  · obtain ⟨_, _, op⟩ := it
    cases op <;> simp [itemCmd] at hc

/-- Every spend log of a sequential run of batch items comes from a `Settle`
item that succeeded: item `i`, whose outcome `i` is `Settled` with the log's cost. -/
theorem runItems_emits {a : Principal} {st : St} {items : List BatchItem} {W : List Write} {outs : List ItemOutcome}
    (h : RunItems a st items W outs) (log : SpendLog) (hl : .Emit log ∈ W) :
    ∃ (i : Nat) (it : BatchItem) (rid pt ct : U64) (status : CallStatus) (cost : U64), items[i]? = some it ∧ it.op = .Settle rid pt ct status ∧
      outs[i]? = some (.Settled cost) ∧ log.reservation = rid ∧ log.cost = cost := by
  induction h with
  | nil => cases hl
  | refused s e hs ht hr ih =>
    obtain ⟨i, it, rid, pt, ct, status, cost, h1, h2, h3, h4, h5⟩ := ih hl
    exact ⟨i + 1, it, rid, pt, ct, status, cost, by simpa using h1, h2, by simpa using h3, h4, h5⟩
  | done s w r hs ht hr ih =>
    rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨rid, pt, ct, status, cost, h1, h2, h3, h4⟩ := emit_item ht log hl
      subst h2
      exact ⟨0, _, rid, pt, ct, status, cost, rfl, h1, rfl, h3, h4⟩
    · obtain ⟨i, it, rid, pt, ct, status, cost, h1, h2, h3, h4, h5⟩ := ih hl
      exact ⟨i + 1, it, rid, pt, ct, status, cost, by simpa using h1, h2, by simpa using h3, h4, h5⟩

/-- Every spend log comes from a `Settle` (for its reservation, with the cost
it replies), an `Expire` (for its reservation, with cost 0 and status
`Expired`), or a `Settle` item `i` of a batch that succeeded (for that item's
reservation, with the cost of its outcome `i`). -/
theorem emit_origin (a : Principal) (s : Snapshot) (c : Command) ws r
    (h : transition a s c = ok (.Ok (ws, r))) (log : SpendLog) (hl : .Emit log ∈ ws.val) :
    (∃ rid pt ct status cost, c = .Settle rid pt ct status ∧ r = .Settled cost ∧ log.reservation = rid ∧
      log.cost = cost) ∨
    (∃ rid, c = .Expire rid ∧ r = .Settled 0#u64 ∧ log.reservation = rid ∧ log.cost = 0#u64 ∧
      log.status = .Expired) ∨
    (∃ (items : alloc.vec.Vec BatchItem) (outs : alloc.vec.Vec ItemOutcome), c = .Batch items ∧ r = .Batch outs ∧
      ∃ (i : Nat) (it : BatchItem) (rid pt ct : U64) (status : CallStatus) (cost : U64), items.val[i]? = some it ∧
        it.op = .Settle rid pt ct status ∧ outs.val[i]? = some (.Settled cost) ∧
        log.reservation = rid ∧ log.cost = cost) := by
  cases c with
  | Batch items =>
    obtain ⟨-, W, outs, hr, hrun, hws⟩ := transition_effect h
    rw [hws] at hl
    exact .inr (.inr ⟨items, outs, rfl, hr, runItems_emits hrun log ((compactL_sublist W).subset hl)⟩)
  | _ =>
    rcases emit_origin_cmd a s _ ws r h log hl (by intro _ h; cases h) with h1 | h2
    · exact .inl h1
    · exact .inr (.inl h2)

/-! ## Batches -/

/-- A successful `Batch` is exactly the sequential run of its items: the
caller is the master key, the reply lists one outcome per item, and there is
a run `RunItems` from the snapshot's state in which each item, as its own
principal on the state the earlier successful items left, was refused
(writing nothing) or succeeded with the outcome it got, the run's writes `W`
being the items' writes in order. The batch commits `compactL W`: the
writes no later write to the same row supersedes, which sends the same spend
logs in the same order and, with unique keys per table (every reachable
state, `reachable_keyed`), reaches the same rows as `W` up to their order in
each table. -/
theorem batch_sequential (a : Principal) (s : Snapshot) (items : alloc.vec.Vec BatchItem) ws r
    (h : transition a s (.Batch items) = ok (.Ok (ws, r))) :
    a.master = true ∧ ∃ (W : List Write) (outs : alloc.vec.Vec ItemOutcome), r = .Batch outs ∧
      RunItems a (Snapshot.toSt s) items.val W outs.val ∧ ws.val = compactL W ∧ emits ws.val = emits W ∧
      (Keyed (Snapshot.toSt s) → Equiv (applyAll (Snapshot.toSt s) ws.val) (applyAll (Snapshot.toSt s) W)) := by
  obtain ⟨hm, W, outs, hr, hrun, hws⟩ := transition_effect h
  refine ⟨hm, W, outs, hr, hrun, hws, by rw [hws, emits_compact], fun hk => ?_⟩
  rw [hws]; exact (compact_equiv _ W hk).1

/-! ## Universal authorization

The h5i authorization schema: for every actor, state and command, every
write of a successful command is one an admin may make, or, in a reachable
state (`Inv`), one a non-admin key may make (`KeyMayWrite`). -/

/-- What a principal may write: anything as an admin; as a key, only what
`KeyMayWrite` allows (given the structural invariant of reachable states). -/
def allowed (st : St) (a : Principal) (w : Write) : Prop :=
  IsAdmin st a ∨ (Inv st → KeyMayWrite st a w)

theorem authorized :
    H5iAppLib.WritesAuthorized transition Snapshot.toSt (fun ws : alloc.vec.Vec Write => ws.val) allowed := by
  intro a s c ws r h w hw
  by_cases ha : IsAdmin (Snapshot.toSt s) a
  · exact .inl ha
  · exact .inr fun hinv => key_confined a s c ws r ha hinv h w hw

theorem outcomeOf_admitted {r : Reply} {rid d amt : U64} (h : outcomeOf r = .Admitted rid d amt) :
    r = .Admitted rid d amt := by
  cases r <;> simp_all [outcomeOf]

/-- Each item of a run that was admitted ran, as its own principal, on the
state the items before it left (a run of the items before it), and its
`transition` replied with that admission. -/
theorem runItems_admitted {a : Principal} {st : St} {items : List BatchItem} {W : List Write}
    {outs : List ItemOutcome} (h : RunItems a st items W outs) (i : Nat) (rid d amt : U64)
    (ho : outs[i]? = some (.Admitted rid d amt)) :
    ∃ (it : BatchItem) (Wpre : List Write) (si : Snapshot) (w : alloc.vec.Vec Write), items[i]? = some it ∧
      RunItems a st (items.take i) Wpre (outs.take i) ∧ Snapshot.toSt si = applyAll st Wpre ∧
      transition (itemPrincipal a it) si (itemCmd it) = ok (.Ok (w, .Admitted rid d amt)) := by
  induction h generalizing i with
  | nil => simp at ho
  | refused s e hs ht hr ih =>
    cases i with
    | zero => simp at ho
    | succ i =>
      obtain ⟨it, Wpre, si, w, h1, h2, h3, h4⟩ := ih i (by simpa using ho)
      exact ⟨it, Wpre, si, w, by simpa using h1, by simpa using RunItems.refused s e hs ht h2, h3, h4⟩
  | done s w r hs ht hr ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
      have := outcomeOf_admitted ho; subst this
      exact ⟨_, [], s, w, rfl, by simpa using RunItems.nil, by simpa [applyAll] using hs, ht⟩
    | succ i =>
      obtain ⟨it, Wpre, si, w', h1, h2, h3, h4⟩ := ih i (by simpa using ho)
      refine ⟨it, w.val ++ Wpre, si, w', by simpa using h1, by simpa using RunItems.done s w r hs ht h2, ?_, h4⟩
      rw [h3, applyAll_append]

/-- `admit_sound` for batches: every `Admitted` outcome `i` of a successful
batch comes from an `Admit` item that ran on the state the items before it
left (`Wpre`, the writes of a run of those items), and by a key, the whole
policy `AdmitByKey` held there for the item's principal, with the reported
deployment and amount; by the master key, the deployment is `Best`. -/
theorem batch_admit_sound (a : Principal) (s : Snapshot) (items : alloc.vec.Vec BatchItem) ws
    (outs : alloc.vec.Vec ItemOutcome) (h : transition a s (.Batch items) = ok (.Ok (ws, .Batch outs)))
    (i : Nat) (rid d amt : U64) (ho : outs.val[i]? = some (.Admitted rid d amt)) :
    ∃ (it : BatchItem) (Wpre : List Write) (si : Snapshot), items.val[i]? = some it ∧
      RunItems a (Snapshot.toSt s) (items.val.take i) Wpre (outs.val.take i) ∧
      Snapshot.toSt si = applyAll (Snapshot.toSt s) Wpre ∧
      ∃ (nm : alloc.vec.Vec U8) (pt mt : U64) (ex : alloc.vec.Vec U64) (m : U64), it.op = .Admit nm pt mt ex ∧
        findModel (Snapshot.toSt si) nm.val = some m.val ∧
        (it.master = false → ∃ (k : Key) (t : Option Team) (dep : Deployment),
          AdmitByKey (Snapshot.toSt si) (itemPrincipal a it) m.val pt.val mt.val (ex.val.map (·.val)) k t dep amt.val ∧
          rid.val = si.settings.next_id.val + 1 ∧ d = dep.id) ∧
        (it.master = true → ∃ dep : Deployment, Best (Snapshot.toSt si) a.now.val m.val (ex.val.map (·.val)) dep ∧
          amt.val = price dep.input_cost.val dep.output_cost.val pt.val mt.val ∧
          rid.val = si.settings.next_id.val + 1 ∧ d = dep.id) := by
  obtain ⟨-, W, outs', hr, hrun, -⟩ := batch_sequential a s items ws _ h
  simp only [Reply.Batch.injEq] at hr; subst hr
  obtain ⟨it, Wpre, si, w, h1, h2, h3, h4⟩ := runItems_admitted hrun i rid d amt ho
  refine ⟨it, Wpre, si, h1, h2, h3, ?_⟩
  obtain ⟨k0, m0, op⟩ := it
  cases op with
  | Settle rid' pt ct st =>
    have := transition_effect h4
    obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hrep, -⟩ := this
    cases hrep
  | Admit nm pt mt ex =>
    obtain ⟨m, hm, hkey, hmas⟩ := admit_sound _ si nm pt mt ex w _ h4
    refine ⟨nm, pt, mt, ex, m, rfl, hm, fun hf => ?_, fun ht => ?_⟩
    · obtain ⟨k, t, dep, rid', amt', hA, hid, hr⟩ := hkey hf
      simp only [Reply.Admitted.injEq] at hr; obtain ⟨rfl, rfl, rfl⟩ := hr
      exact ⟨k, t, dep, hA, hid, rfl⟩
    · obtain ⟨dep, rid', amt', hb, hamt, hid, hr⟩ := hmas ht
      simp only [Reply.Admitted.injEq] at hr; obtain ⟨rfl, rfl, rfl⟩ := hr
      exact ⟨dep, hb, hamt, hid, rfl⟩

theorem toSt_inj {s s' : Snapshot} (h : Snapshot.toSt s = Snapshot.toSt s') : s = s' := by
  obtain ⟨st, t, k, m, d, km, tm, u, r⟩ := s
  obtain ⟨st', t', k', m', d', km', tm', u', r'⟩ := s'
  simp only [Snapshot.toSt, St.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  subst h1
  congr 1 <;> apply alloc.vec.Vec.ext <;> assumption

/-- A sequential run is determined by its start and its items. -/
theorem runItems_det {a : Principal} {st : St} {items : List BatchItem} {W W' : List Write}
    {outs outs' : List ItemOutcome} (h : RunItems a st items W outs) (h' : RunItems a st items W' outs') :
    W = W' ∧ outs = outs' := by
  induction h generalizing W' outs' with
  | nil => cases h'; exact ⟨rfl, rfl⟩
  | refused s e hs ht hr ih =>
    cases h' with
    | refused s' e' hs' ht' hr' =>
      have := toSt_inj (hs.trans hs'.symm); subst this
      rw [ht] at ht'; simp only [ok.injEq, core.result.Result.Err.injEq] at ht'; subst ht'
      obtain ⟨rfl, rfl⟩ := ih hr'; exact ⟨rfl, rfl⟩
    | done s' w' r' hs' ht' hr' =>
      have := toSt_inj (hs.trans hs'.symm); subst this
      rw [ht] at ht'; simp at ht'
  | done s w r hs ht hr ih =>
    cases h' with
    | refused s' e' hs' ht' hr' =>
      have := toSt_inj (hs.trans hs'.symm); subst this
      rw [ht] at ht'; simp at ht'
    | done s' w' r' hs' ht' hr' =>
      have := toSt_inj (hs.trans hs'.symm); subst this
      rw [ht] at ht'; simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at ht'
      obtain ⟨rfl, rfl⟩ := ht'
      obtain ⟨rfl, rfl⟩ := ih hr'; exact ⟨rfl, rfl⟩

theorem batch_master_ok {a : Principal} {s : Snapshot} {items : alloc.vec.Vec BatchItem} {res}
    (hm : a.master = true) (h : batch a s items = ok res) : ∃ ws rep, res = .Ok (ws, rep) := by
  unfold batch at h
  rw [if_pos hm, gateway_kernel.Schema.Snapshot.clone_eq] at h
  simp only [bind_ok] at h
  obtain ⟨⟨W, outs⟩, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨v, -, h⟩ := bind_eq_ok.1 h
  simp only [ok.injEq] at h
  exact ⟨v, _, h.symm⟩

/-- Conversely, a batch by the master key that leaves room in every vector
(`Commands.Fits`) succeeds with exactly the run of its items: given a
sequential run of the items, the batch replies with its outcomes and commits
`compactL` of its writes. -/
theorem batch_complete (a : Principal) (s : Snapshot) (items : alloc.vec.Vec BatchItem) (W : List Write)
    (outs : List ItemOutcome) (hm : a.master = true) (hf : Fits s (.Batch items))
    (hrun : RunItems a (Snapshot.toSt s) items.val W outs) :
    ∃ (ws : alloc.vec.Vec Write) (outs' : alloc.vec.Vec ItemOutcome),
      transition a s (.Batch items) = ok (.Ok (ws, .Batch outs')) ∧ ws.val = compactL W ∧ outs'.val = outs := by
  obtain ⟨res, hres⟩ := transition_total a s _ hf
  obtain ⟨ws, rep, rfl⟩ := batch_master_ok hm (by simpa only [transition] using hres)
  obtain ⟨-, W', outs', hr, hrun', hws, -⟩ := batch_sequential a s items ws rep hres
  obtain ⟨rfl, rfl⟩ := runItems_det hrun hrun'
  subst hr
  exact ⟨ws, outs', hres, hws, rfl⟩

end gateway_kernel.Theorems