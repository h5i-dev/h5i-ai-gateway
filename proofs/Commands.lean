import Helpers
/-!
# What each command does

One lemma per kernel command: what a successful run writes and which facts it
checked (`admit_key_spec`: the whole policy `AdmitByKey`; `settle_spec`: the
reservation, `MayClose`, the price; management commands: their writes, with
`IsAdmin` from `transition` via `manage_of`). `transition_effect` sums them up
as `Effect` for every successful run, and `transition_total` shows the kernel
never fails as long as the write list fits in a vector (`Fits`, which every
successful run satisfies: `fits_of_ok`).
-/
open Aeneas Aeneas.Std Result gateway_kernel gateway_kernel.Spec gateway_kernel.Helpers H5iAppLib

namespace gateway_kernel.Commands

attribute [local simp] u64_val_eq

/-- `u` is the usage row of `(scope, id)` after one more request at `now`. -/
def Counted (st : St) (scope id : U64) (now : Nat) (u : Usage) : Prop :=
  u.scope = scope ∧ u.id = id ∧ u.window.val = window now ∧
    u.requests.val = sat ((usedIn st scope.val id.val (window now)).1 + 1) ∧
    u.tokens.val = (usedIn st scope.val id.val (window now)).2

theorem admit_master_spec (a : Principal) (s : Snapshot) (m pt mt : U64) (ex : alloc.vec.Vec U64) :
    admit_master a s m pt mt ex ⦃ r => ∀ ws rep, r = .Ok (ws, rep) →
      ∃ (d : Deployment) (id amt : U64) (u : Usage), Best (Snapshot.toSt s) a.now.val m.val (ex.val.map (·.val)) d ∧
        amt.val = price d.input_cost.val d.output_cost.val pt.val mt.val ∧
        id.val = s.settings.next_id.val + 1 ∧ rep = .Admitted id d.id amt ∧
        Counted (Snapshot.toSt s) 2#u64 d.id a.now.val u ∧
        ws.val = [.PutUsage u,
          .PutReservation { id := id, key_id := 0#u64, team := 0#u64, deployment := d.id, model := m, input_cost := d.input_cost, output_cost := d.output_cost, amount := amt, created_at := a.now },
          .SetSettings { s.settings with next_id := id }] ⦄ := by
  unfold admit_master
  step with route_best as ⟨o, ho⟩
  step*
  intro ws rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
  subst_vars
  simp only [SCOPE_DEPLOYMENT] at *
  refine ⟨d, id, amount, u, ho, amount_post, by simp_all, rfl, ⟨by simp_all, u_post, by simp_all, by simp_all [usedL_toSt], by simp_all [usedL_toSt]⟩, by simp [ws2_post, ws1_post, ws_post, alloc.vec.Vec.new]⟩

/-- `k'` is key `k` at time `now` (`key_now`): only the spend and the reset
time can change, and the spend restarts from 0 when the period ended. -/
def KeyNow (k k' : Key) (now : Nat) : Prop :=
  k' = { k with spend := k'.spend, budget_reset_at := k'.budget_reset_at } ∧
    k'.spend.val = spendAt k.spend.val k.budget_duration.val k.budget_reset_at.val now ∧
    k'.budget_reset_at.val = (if k.budget_duration.val ≠ 0 ∧ k.budget_reset_at.val ≤ now
      then sat (now + k.budget_duration.val) else k.budget_reset_at.val)

/-- `t'` is team `t` at time `now` (`team_now`). -/
def TeamNow (t t' : Team) (now : Nat) : Prop :=
  t' = { t with spend := t'.spend, budget_reset_at := t'.budget_reset_at } ∧
    t'.spend.val = spendAt t.spend.val t.budget_duration.val t.budget_reset_at.val now ∧
    t'.budget_reset_at.val = (if t.budget_duration.val ≠ 0 ∧ t.budget_reset_at.val ≤ now
      then sat (now + t.budget_duration.val) else t.budget_reset_at.val)

/-- The writes of an admission for the key's team: none without a team, else
the team at `now` and its counter after one more request. -/
def TeamWrites (st : St) (now : Nat) : Option Team → List Write → Prop
  | none, tw => tw = []
  | some t, tw => ∃ t2 u, TeamNow t t2 now ∧ Counted st 1#u64 t.id now u ∧ tw = [.PutTeam t2, .PutUsage u]

theorem KeyNow.limits {k k' : Key} {now : Nat} (h : KeyNow k k' now) :
    k'.id = k.id ∧ k'.team = k.team ∧ k'.user = k.user ∧ k'.max_budget = k.max_budget ∧ k'.rpm = k.rpm ∧
      k'.tpm = k.tpm ∧ k'.max_parallel = k.max_parallel ∧ k'.expires_at = k.expires_at ∧
      k'.budget_duration = k.budget_duration ∧ k'.blocked = k.blocked ∧ k'.admin = k.admin ∧
      k'.all_models = k.all_models := by
  rw [h.1]; simp

theorem TeamNow.limits {t t' : Team} {now : Nat} (h : TeamNow t t' now) :
    t'.id = t.id ∧ t'.max_budget = t.max_budget ∧ t'.rpm = t.rpm ∧ t'.tpm = t.tpm ∧
      t'.budget_duration = t.budget_duration ∧ t'.blocked = t.blocked ∧ t'.all_models = t.all_models := by
  rw [h.1]; simp

theorem key_now_spec' (k : Key) (now : U64) : key_now k now ⦃ k' => KeyNow k k' now.val ⦄ := by
  apply WP.spec_mono (key_now_spec k now)
  intro k' ⟨h1, h2, h3⟩; exact ⟨h3, h1, h2⟩

theorem team_now_spec' (t : Team) (now : U64) : team_now t now ⦃ t' => TeamNow t t' now.val ⦄ := by
  apply WP.spec_mono (team_now_spec t now)
  intro t' ⟨h1, h2, h3⟩; exact ⟨h3, h1, h2⟩

attribute [-step] key_now_spec team_now_spec
attribute [local step] key_now_spec' team_now_spec'

theorem admit_key_spec (a : Principal) (s : Snapshot) (m pt mt : U64) (ex : alloc.vec.Vec U64)
    (hm : a.master = false) :
    admit_key a s m pt mt ex ⦃ r => ∀ ws rep, r = .Ok (ws, rep) →
      ∃ (k : Key) (t : Option Team) (d : Deployment) (id amt : U64) (k2 : Key) (uk ud : Usage) (tw : List Write),
        AdmitByKey (Snapshot.toSt s) a m.val pt.val mt.val (ex.val.map (·.val)) k t d amt.val ∧
        id.val = s.settings.next_id.val + 1 ∧ rep = .Admitted id d.id amt ∧
        KeyNow k k2 a.now.val ∧ Counted (Snapshot.toSt s) 0#u64 k.id a.now.val uk ∧
        TeamWrites (Snapshot.toSt s) a.now.val t tw ∧ Counted (Snapshot.toSt s) 2#u64 d.id a.now.val ud ∧
        ws.val = [.PutKey k2, .PutUsage uk] ++ tw ++ [.PutUsage ud,
          .PutReservation { id := id, key_id := k.id, team := k.team, deployment := d.id, model := m, input_cost := d.input_cost, output_cost := d.output_cost, amount := amt, created_at := a.now },
          .SetSettings { s.settings with next_id := id }] ⦄ := by
  unfold admit_key
  have := usize_max_ge
  step*
  all_goals try (simp only [*, vec_new_val, List.length_append, List.length_cons, List.length_nil, List.nil_append]; omega)
  · intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    have hw : w.val = window a.now.val := by assumption
    simp only [SCOPE_KEY, SCOPE_TEAM, SCOPE_DEPLOYMENT] at *
    have hk : findKey (Snapshot.toSt s) a.key.val = some k := by rw [← findKey_toSt, ← o_post]; assumption
    have hd : Best (Snapshot.toSt s) a.now.val m.val (ex.val.map (·.val)) d := by
      have := o1_post; simp only [‹o1 = some d›] at this; exact this
    have hb1 := b1_post.1 ‹_›
    have hb2 := b2_post.1 ‹_›
    have hkn := k2_post.limits
    have hid : id.val = s.settings.next_id.val + 1 := by
      have := r_post; simp only [‹r = _›] at this; exact this.2
    refine ⟨k, none, d, id, amount, k2, u, u1, [], ⟨hm, hk, by simpa using ‹¬k.blocked = true›,
      by simpa using ‹¬a.now ≥ k.expires_at›, fun _ => rfl, fun h => absurd ‹k.team = 0#u64› (by simpa using h),
      b_post.1 ‹_›, ?_, ?_, ?_, (fun _ h => by cases h), hd, amount_post, ?_, (fun _ h => by cases h)⟩,
      hid, rfl, k2_post, ⟨by assumption, u_post, by rw [‹u.window = w›, hw], ?_, ?_⟩, rfl,
      ⟨by assumption, u1_post, by rw [‹u1.window = w›, hw], ?_, ?_⟩, ?_⟩
    · have := hb1.1; rw [kr_post, hw] at this; exact this
    · have := hb1.2; rw [kr_post1, hw] at this; exact this
    · have := ‹¬i ≥ k.max_parallel›; rw [ge_iff_le, UScalar.le_equiv, not_le, i_post] at this; exact this
    · have := hb2; rw [i1_post, k2_post.2.1, hkn.2.2.2.1] at this; exact this
    · rw [u_post1, hw]; rfl
    · rw [u_post2, hw]; rfl
    · rw [u1_post1, hw]; rfl
    · rw [u1_post2, hw]; rfl
    · simp [ws4_post, ws3_post, ws2_post, ws1_post, ws_post, vec_new_val, s1_post, ‹k.team = 0#u64›]
  · intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    have hw : w.val = window a.now.val := by assumption
    simp only [SCOPE_KEY, SCOPE_TEAM, SCOPE_DEPLOYMENT] at *
    have hk : findKey (Snapshot.toSt s) a.key.val = some k := by rw [← findKey_toSt, ← o_post]; assumption
    have ht : findTeam (Snapshot.toSt s) k.team.val = some t := by rw [← findTeam_toSt, ← o1_post]; assumption
    have hd : Best (Snapshot.toSt s) a.now.val m.val (ex.val.map (·.val)) d := by
      have := o2_post; simp only [‹o2 = some d›] at this; exact this
    have hb1 := b1_post.1 ‹_›
    have hb2 := b2_post.1 ‹_›
    have hb3 := b3_post.1 ‹_›
    have hb4 := b4_post.1 ‹_›
    have hkn := k2_post.limits
    have hid : id.val = s.settings.next_id.val + 1 := by
      have := r_post; simp only [‹r = _›] at this; exact this.2
    have htn := t2_post.limits
    have hm' := b_post.1 ‹_›
    refine ⟨k, some t, d, id, amount, k2, u, u2, [.PutTeam t2, .PutUsage u1], ⟨hm, hk, by simpa using ‹¬k.blocked = true›,
      by simpa using ‹¬a.now ≥ k.expires_at›, fun h => absurd h (by simpa using ‹¬k.team = 0#u64›),
      fun _ => ⟨t, ht, by simpa using ‹¬t.blocked = true›, rfl⟩,
      hm', ?_, ?_, ?_, ?_, hd, amount_post, ?_, ?_⟩,
      hid, rfl, k2_post, ⟨by assumption, u_post, by rw [‹u.window = w›, hw], ?_, ?_⟩,
      ⟨t2, u1, t2_post, ⟨by assumption, by rw [u1_post, htn.1], by rw [‹u1.window = w›, hw], ?_, ?_⟩, rfl⟩,
      ⟨by assumption, u2_post, by rw [‹u2.window = w›, hw], ?_, ?_⟩, ?_⟩
    · have := hb1.1; rw [kr_post, hw] at this; exact this
    · have := hb1.2; rw [kr_post1, hw] at this; exact this
    · have := ‹¬i ≥ k.max_parallel›; rw [ge_iff_le, UScalar.le_equiv, not_le, i_post] at this; exact this
    · intro t' h; cases h
      exact ⟨by have := hb2.1; rw [tr_post, hw] at this; exact this,
        by have := hb2.2; rw [tr_post1, hw] at this; exact this⟩
    · have := hb3; rw [i1_post, k2_post.2.1, hkn.2.2.2.1] at this; exact this
    · intro t' h; cases h
      have := hb4; rw [i2_post, t2_post.2.1, htn.2.1] at this; exact this
    · rw [u_post1, hw]; rfl
    · rw [u_post2, hw]; rfl
    · rw [u1_post1, hw, htn.1]; rfl
    · rw [u1_post2, hw, htn.1]; rfl
    · rw [u2_post1, hw]; rfl
    · rw [u2_post2, hw]; rfl
    · simp [ws6_post, ws5_post, ws4_post, ws3_post, ws2_post, ws1_post, ws_post, vec_new_val, s1_post]
/-- `u` is the usage row of `(scope, id)` after `n` more tokens at `now`. -/
def TokCounted (st : St) (scope id : U64) (now n : Nat) (u : Usage) : Prop :=
  u.scope = scope ∧ u.id = id ∧ u.window.val = window now ∧
    u.requests.val = (usedIn st scope.val id.val (window now)).1 ∧
    u.tokens.val = sat ((usedIn st scope.val id.val (window now)).2 + n)

/-- `d'` is deployment `d` after one more retryable failure at `now`
(`record_failure` with the state's settings): only its health changes. -/
def Failed (st : St) (d d' : Deployment) (now : Nat) : Prop :=
  d' = { d with fails := d'.fails, fail_window := d'.fail_window, cooldown_until := d'.cooldown_until } ∧
    d'.fail_window.val = window now ∧
    (if st.settings.allowed_fails.val < failsAfter d now
      then d'.fails.val = 0 ∧ d'.cooldown_until.val = sat (now + st.settings.cooldown_secs.val)
      else d'.fails.val = failsAfter d now ∧ d'.cooldown_until = d.cooldown_until)

/-- The caller may close reservation `r` (`may_close`): it is the key that
made it, or an admin. -/
def MayClose (st : St) (a : Principal) (r : Reservation) : Prop :=
  (a.master = false ∧ r.key_id = a.key) ∨ IsAdmin st a

theorem callstatus_eq_spec (x y : CallStatus) :
    CallStatus.Insts.CoreCmpPartialEqCallStatus.eq x y ⦃ b => (b = true ↔ x = y) ⦄ := by
  cases x <;> cases y <;> simp [CallStatus.Insts.CoreCmpPartialEqCallStatus.eq, read_discriminant, CallStatus.read_discriminant]

theorem may_close_spec (a : Principal) (s : Snapshot) (r : Reservation) :
    may_close a s r ⦃ b => (b = true ↔ MayClose (Snapshot.toSt s) a r) ⦄ := by
  unfold may_close MayClose
  step* <;> simp_all

attribute [local step] callstatus_eq_spec may_close_spec

/-- The key writes of a settlement: the key of the reservation (if it has one
and it still exists) at `now` with the cost added to its spend, and its
counter after the tokens. -/
def SettleKeyWrites (st : St) (now c tokens : Nat) (kid : U64) (kw : List Write) : Prop :=
  ((kid.val = 0 ∨ findKey st kid.val = none) ∧ kw = []) ∨
  ∃ (k k2 : Key) (sp : U64) (u : Usage), kid.val ≠ 0 ∧ findKey st kid.val = some k ∧ KeyNow k k2 now ∧
    sp.val = sat (k2.spend.val + c) ∧ TokCounted st 0#u64 k.id now tokens u ∧
    kw = [.PutKey { k2 with spend := sp }, .PutUsage u]

/-- The team writes of a settlement, as `SettleKeyWrites`. -/
def SettleTeamWrites (st : St) (now c tokens : Nat) (tid : U64) (tw : List Write) : Prop :=
  ((tid.val = 0 ∨ findTeam st tid.val = none) ∧ tw = []) ∨
  ∃ (t t2 : Team) (sp : U64) (u : Usage), tid.val ≠ 0 ∧ findTeam st tid.val = some t ∧ TeamNow t t2 now ∧
    sp.val = sat (t2.spend.val + c) ∧ TokCounted st 1#u64 t.id now tokens u ∧
    tw = [.PutTeam { t2 with spend := sp }, .PutUsage u]

/-- The deployment write of a settlement: a retryable failure counts against
the deployment, if it still exists. -/
def SettleDeploymentWrites (st : St) (now : Nat) (status : CallStatus) (did : U64) (dw : List Write) : Prop :=
  ((status ≠ .Retryable ∨ findDeployment st did.val = none) ∧ dw = []) ∨
  ∃ d d', status = .Retryable ∧ findDeployment st did.val = some d ∧ Failed st d d' now ∧ dw = [.PutDeployment d']

theorem ne0_of_bne {x : U64} (h : (x != 0#u64) = true) : x.val ≠ 0 := by
  intro e; apply (bne_iff_ne.1 h); exact (u64_val_eq _ _).1 (by simpa using e)

theorem eq0_of_not_bne {x : U64} (h : ¬(x != 0#u64) = true) : x.val = 0 := by
  simpa using h

theorem settle_key_spec (s : Snapshot) (r : Reservation) (now w c tokens : U64) (ws : alloc.vec.Vec Write)
    (hw : w.val = window now.val) (hl : ws.val.length < 100) :
    (if r.key_id != 0#u64
        then
          do
          let o1 ← find_key s.keys r.key_id
          match o1 with
          | none => ok ws
          | some k =>
            let k2 ← key_now k now
            let i ← sat_add k2.spend c
            let ws2 ←
              alloc.vec.Vec.push ws (Write.PutKey { k2 with spend := i })
            let u ← count_tokens s.usage SCOPE_KEY k.id w tokens
            alloc.vec.Vec.push ws2 (Write.PutUsage u)
        else ok ws) ⦃ ws1 => ∃ kw, SettleKeyWrites (Snapshot.toSt s) now.val c.val tokens.val r.key_id kw ∧
          ws1.val = ws.val ++ kw ∧ kw.length ≤ 2 ⦄ := by
  have := usize_max_ge
  h5i_steps
  all_goals try simp only [SCOPE_KEY] at *
  · exact ⟨[], Or.inl ⟨Or.inr (by rw [← findKey_toSt, ← o1_post]; assumption), rfl⟩, by simp, by simp⟩
  · simp only [ws2_post, List.length_append, List.length_cons, List.length_nil]; omega
  · refine ⟨_, Or.inr ⟨k, k2, i, u, ne0_of_bne ‹_›, by rw [← findKey_toSt, ← o1_post]; assumption, k2_post, i_post,
      ⟨by assumption, u_post, by rw [w_post, hw], ?_, ?_⟩, rfl⟩,
      by simp [ws1_post, ws2_post], by simp⟩
    · rw [u_post1, hw]; rfl
    · rw [u_post2, hw]; rfl
  · exact ⟨[], Or.inl ⟨Or.inl (eq0_of_not_bne ‹_›), rfl⟩, by simp, by simp⟩

theorem settle_team_spec (s : Snapshot) (r : Reservation) (now w c tokens : U64) (ws1 : alloc.vec.Vec Write)
    (hw : w.val = window now.val) (hl : ws1.val.length < 100) :
    (if r.team != 0#u64
        then
          do
          let o1 ← find_team s.teams r.team
          match o1 with
          | none => ok ws1
          | some t =>
            let t2 ← team_now t now
            let i ← sat_add t2.spend c
            let ws3 ←
              alloc.vec.Vec.push ws1 (Write.PutTeam { t2 with spend := i })
            let u ← count_tokens s.usage SCOPE_TEAM t.id w tokens
            alloc.vec.Vec.push ws3 (Write.PutUsage u)
        else ok ws1) ⦃ ws2 => ∃ tw, SettleTeamWrites (Snapshot.toSt s) now.val c.val tokens.val r.team tw ∧
          ws2.val = ws1.val ++ tw ∧ tw.length ≤ 2 ⦄ := by
  have := usize_max_ge
  h5i_steps
  all_goals try simp only [SCOPE_TEAM] at *
  · exact ⟨[], Or.inl ⟨Or.inr (by rw [← findTeam_toSt, ← o1_post]; assumption), rfl⟩, by simp, by simp⟩
  · simp only [ws3_post, List.length_append, List.length_cons, List.length_nil]; omega
  · refine ⟨_, Or.inr ⟨t, t2, i, u, ne0_of_bne ‹_›, by rw [← findTeam_toSt, ← o1_post]; assumption, t2_post, i_post,
      ⟨by assumption, u_post, by rw [w_post, hw], ?_, ?_⟩, rfl⟩,
      by simp [ws2_post, ws3_post], by simp⟩
    · rw [u_post1, hw]; rfl
    · rw [u_post2, hw]; rfl
  · exact ⟨[], Or.inl ⟨Or.inl (eq0_of_not_bne ‹_›), rfl⟩, by simp, by simp⟩

theorem settle_dep_spec (a : Principal) (s : Snapshot) (r : Reservation) (status : CallStatus) (b1 : Bool)
    (hb : b1 = true ↔ status = .Retryable) (ws3 : alloc.vec.Vec Write) (hl : ws3.val.length < 100) :
    (if b1
        then
          do
          let o1 ← find_deployment s.deployments r.deployment
          match o1 with
          | none => ok ws3
          | some d =>
            let d1 ←
              record_failure d s.settings.allowed_fails
                s.settings.cooldown_secs a.now
            alloc.vec.Vec.push ws3 (Write.PutDeployment d1)
        else ok ws3) ⦃ ws4 => ∃ dw, SettleDeploymentWrites (Snapshot.toSt s) a.now.val status r.deployment dw ∧
          ws4.val = ws3.val ++ dw ∧ dw.length ≤ 1 ⦄ := by
  have := usize_max_ge
  h5i_steps
  · exact ⟨[], Or.inl ⟨Or.inr (by rw [← findDeployment_toSt, ← o1_post]; assumption), rfl⟩, by simp, by simp⟩
  · exact ⟨_, Or.inr ⟨d, d1, hb.1 ‹_›, by rw [← findDeployment_toSt, ← o1_post]; assumption,
      ⟨d1_post2, d1_post, d1_post1⟩, rfl⟩, ws4_post, by simp⟩
  · exact ⟨[], Or.inl ⟨Or.inl (fun h => ‹¬b1 = true› (hb.2 h)), rfl⟩, by simp, by simp⟩

theorem settle_spec (a : Principal) (s : Snapshot) (id pt ct : U64) (status : CallStatus) :
    settle a s id pt ct status ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ (r : Reservation) (c tokens : U64) (kw tw : List Write) (ud : Usage) (dw : List Write),
        findReservation (Snapshot.toSt s) id.val = some r ∧ MayClose (Snapshot.toSt s) a r ∧
        c.val = price r.input_cost.val r.output_cost.val pt.val ct.val ∧ tokens.val = sat (pt.val + ct.val) ∧
        rep = .Settled c ∧
        SettleKeyWrites (Snapshot.toSt s) a.now.val c.val tokens.val r.key_id kw ∧
        SettleTeamWrites (Snapshot.toSt s) a.now.val c.val tokens.val r.team tw ∧
        TokCounted (Snapshot.toSt s) 2#u64 r.deployment a.now.val tokens.val ud ∧
        SettleDeploymentWrites (Snapshot.toSt s) a.now.val status r.deployment dw ∧
        ws.val = [.DelReservation id] ++ kw ++ tw ++ [.PutUsage ud] ++ dw ++
          [.Emit { reservation := id, key := r.key_id, team := r.team, deployment := r.deployment, model := r.model, prompt_tokens := pt, completion_tokens := ct, cost := c, «at» := a.now, status := status }] ⦄ := by
  unfold settle
  have := usize_max_ge
  step*
  step with settle_key_spec as ⟨kw, v1, hkw, hv1, hkl⟩
  step with settle_team_spec as ⟨tw, v2, htw, hv2, htl⟩
  step*
  step with settle_dep_spec as ⟨dw, v4, hdw, hv4, hdl⟩
  step*
  · simp only [hv4, ws3_post, hv2, hv1, ws_post, vec_new_val, List.length_append, List.length_cons,
      List.length_nil]; omega
  · intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    simp only [SCOPE_DEPLOYMENT] at *
    refine ⟨r, c, tokens, kw, tw, u, dw, by rw [← findReservation_toSt, ← o_post]; assumption, b_post.1 ‹_›,
      c_post, tokens_post, rfl, hkw, htw, ⟨by assumption, u_post, by rw [‹u.window = w›, ‹w.val = _›], ?_, ?_⟩, hdw, ?_⟩
    · rw [u_post1, ‹w.val = _›]; rfl
    · rw [u_post2, ‹w.val = _›]; rfl
    · simp [ws5_post, hv4, ws3_post, hv2, hv1, ws_post, vec_new_val]

theorem expire_spec (a : Principal) (s : Snapshot) (id : U64) :
    expire a s id ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ r, findReservation (Snapshot.toSt s) id.val = some r ∧ MayClose (Snapshot.toSt s) a r ∧
        sat (r.created_at.val + s.settings.reservation_ttl.val) ≤ a.now.val ∧ rep = .Settled 0#u64 ∧
        ws.val = [.DelReservation id,
          .Emit { reservation := id, key := r.key_id, team := r.team, deployment := r.deployment, model := r.model, prompt_tokens := 0#u64, completion_tokens := 0#u64, cost := 0#u64, «at» := a.now, status := .Expired }] ⦄ := by
  unfold expire
  have := usize_max_ge
  step*
  intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
  refine ⟨r, by rw [← findReservation_toSt, ← o_post]; assumption, b_post.1 ‹_›, ?_, rfl, by simp [ws1_post, ws_post]⟩
  rw [← i_post]; have := ‹¬a.now < i›; scalar_tac

/-! ## Loops that build write lists -/

theorem create_team_loop_spec (ids : alloc.vec.Vec U64) (id : U64) (ws : alloc.vec.Vec Write)
    (h : ws.val.length + ids.val.length ≤ Usize.max) :
    create_team_loop ids id ws 0#usize ⦃ out =>
      out.val = ws.val ++ ids.val.map (fun m => .PutTeamModel { team := id, model := m }) ⦄ := by
  unfold create_team_loop
  apply WP.spec_mono (loop_fold ids.val (fun out : alloc.vec.Vec Write => out.val)
    (fun acc m => acc ++ [.PutTeamModel { team := id, model := m }])
    (fun out i => out.val.length = ws.val.length + i) _ ?_ _ 0#usize (by simp) (by simp))
  · intro r hr; rw [hr]; simpa using foldl_map (fun m => Write.PutTeamModel { team := id, model := m }) ids.val ws.val
  · intro out j hj hinv; unfold create_team_loop.body; h5i_step

theorem clear_team_models_spec (v : alloc.vec.Vec TeamModel) (team : U64) (ws : alloc.vec.Vec Write)
    (h : ws.val.length + v.val.length ≤ Usize.max) :
    clear_team_models v team ws ⦃ out =>
      out.val = ws.val ++ (v.val.filter (fun g => g.team = team)).map (fun g => .DelTeamModel team g.model) ⦄ := by
  unfold clear_team_models clear_team_models_loop
  apply WP.spec_mono (loop_fold v.val (fun out : alloc.vec.Vec Write => out.val)
    (fun acc g => if g.team = team then acc ++ [.DelTeamModel team g.model] else acc)
    (fun out i => out.val.length ≤ ws.val.length + i) _ ?_ _ 0#usize (by simp) (by simp))
  · intro r hr; rw [hr]
    simpa using foldl_filter_map (fun g : TeamModel => decide (g.team = team)) (fun g => Write.DelTeamModel team g.model) v.val ws.val
  · intro out j hj hinv; unfold clear_team_models_loop.body; h5i_step

theorem set_team_models_loop_spec (id : U64) (ids : alloc.vec.Vec U64) (ws : alloc.vec.Vec Write)
    (h : ws.val.length + ids.val.length ≤ Usize.max) :
    set_team_models_loop id ids ws 0#usize ⦃ out =>
      out.val = ws.val ++ ids.val.map (fun m => .PutTeamModel { team := id, model := m }) ⦄ := by
  unfold set_team_models_loop
  apply WP.spec_mono (loop_fold ids.val (fun out : alloc.vec.Vec Write => out.val)
    (fun acc m => acc ++ [.PutTeamModel { team := id, model := m }])
    (fun out i => out.val.length = ws.val.length + i) _ ?_ _ 0#usize (by simp) (by simp))
  · intro r hr; rw [hr]; simpa using foldl_map (fun m => Write.PutTeamModel { team := id, model := m }) ids.val ws.val
  · intro out j hj hinv; unfold set_team_models_loop.body; h5i_step

theorem create_key_loop0_spec (ids : alloc.vec.Vec U64) (id : U64) (ws : alloc.vec.Vec Write)
    (h : ws.val.length + ids.val.length ≤ Usize.max) :
    create_key_loop0 ids id ws 0#usize ⦃ out =>
      out.val = ws.val ++ ids.val.map (fun m => .PutKeyModel { key := id, model := m }) ⦄ := by
  unfold create_key_loop0
  apply WP.spec_mono (loop_fold ids.val (fun out : alloc.vec.Vec Write => out.val)
    (fun acc m => acc ++ [.PutKeyModel { key := id, model := m }])
    (fun out i => out.val.length = ws.val.length + i) _ ?_ _ 0#usize (by simp) (by simp))
  · intro r hr; rw [hr]; simpa using foldl_map (fun m => Write.PutKeyModel { key := id, model := m }) ids.val ws.val
  · intro out j hj hinv; unfold create_key_loop0.body; h5i_step

theorem create_key_loop1_spec (ids : alloc.vec.Vec U64) (id : U64) (ws : alloc.vec.Vec Write)
    (h : ws.val.length + ids.val.length ≤ Usize.max) :
    create_key_loop1 ids id ws 0#usize ⦃ out =>
      out.val = ws.val ++ ids.val.map (fun m => .PutKeyModel { key := id, model := m }) ⦄ := by
  unfold create_key_loop1
  apply WP.spec_mono (loop_fold ids.val (fun out : alloc.vec.Vec Write => out.val)
    (fun acc m => acc ++ [.PutKeyModel { key := id, model := m }])
    (fun out i => out.val.length = ws.val.length + i) _ ?_ _ 0#usize (by simp) (by simp))
  · intro r hr; rw [hr]; simpa using foldl_map (fun m => Write.PutKeyModel { key := id, model := m }) ids.val ws.val
  · intro out j hj hinv; unfold create_key_loop1.body; h5i_step

theorem set_key_models_loop_spec (id : U64) (ids : alloc.vec.Vec U64) (ws : alloc.vec.Vec Write)
    (h : ws.val.length + ids.val.length ≤ Usize.max) :
    set_key_models_loop id ids ws 0#usize ⦃ out =>
      out.val = ws.val ++ ids.val.map (fun m => .PutKeyModel { key := id, model := m }) ⦄ := by
  unfold set_key_models_loop
  apply WP.spec_mono (loop_fold ids.val (fun out : alloc.vec.Vec Write => out.val)
    (fun acc m => acc ++ [.PutKeyModel { key := id, model := m }])
    (fun out i => out.val.length = ws.val.length + i) _ ?_ _ 0#usize (by simp) (by simp))
  · intro r hr; rw [hr]; simpa using foldl_map (fun m => Write.PutKeyModel { key := id, model := m }) ids.val ws.val
  · intro out j hj hinv; unfold set_key_models_loop.body; h5i_step

theorem clear_key_models_spec (v : alloc.vec.Vec KeyModel) (key : U64) (ws : alloc.vec.Vec Write)
    (h : ws.val.length + v.val.length ≤ Usize.max) :
    clear_key_models v key ws ⦃ out =>
      out.val = ws.val ++ (v.val.filter (fun g => g.key = key)).map (fun g => .DelKeyModel key g.model) ⦄ := by
  unfold clear_key_models clear_key_models_loop
  apply WP.spec_mono (loop_fold v.val (fun out : alloc.vec.Vec Write => out.val)
    (fun acc g => if g.key = key then acc ++ [.DelKeyModel key g.model] else acc)
    (fun out i => out.val.length ≤ ws.val.length + i) _ ?_ _ 0#usize (by simp) (by simp))
  · intro r hr; rw [hr]
    simpa using foldl_filter_map (fun g : KeyModel => decide (g.key = key)) (fun g => Write.DelKeyModel key g.model) v.val ws.val
  · intro out j hj hinv; unfold clear_key_models_loop.body; h5i_step

/-! ## Management commands -/

theorem configure_spec (s : Snapshot) (af cs ttl : U64) :
    configure s af cs ttl ⦃ res => ∀ ws rep, res = .Ok (ws, rep) → rep = .Done ∧
      ws.val = [.SetSettings { s.settings with allowed_fails := af, cooldown_secs := cs, reservation_ttl := ttl }] ⦄ := by
  unfold configure; step*

/-- The model ids of `names`, as `resolve_models` finds them. -/
def Resolved (st : St) (names : List (alloc.vec.Vec U8)) (ids : List U64) : Prop :=
  resolveL st.models names = some ids ∧ ids.length = names.length ∧ ∀ x ∈ ids, ∃ m ∈ st.models, m.id = x

theorem create_team_spec (a : Principal) (s : Snapshot) (spec : TeamSpec) (names : alloc.vec.Vec (alloc.vec.Vec U8))
    (hn : names.val.length + 1 < Usize.max) :
    create_team a s spec names ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ (ids : List U64) (id ra : U64), Resolved (Snapshot.toSt s) names.val ids ∧
        id.val = s.settings.next_id.val + 1 ∧ ra.val = sat (a.now.val + spec.budget_duration.val) ∧ rep = .Created id ∧
        ws.val = .PutTeam { id := id, max_budget := spec.max_budget, spend := 0#u64, rpm := spec.rpm, tpm := spec.tpm, budget_duration := spec.budget_duration, budget_reset_at := ra, blocked := false, all_models := spec.all_models } ::
          (ids.map (fun m => .PutTeamModel { team := id, model := m }) ++ [.SetSettings { s.settings with next_id := id }]) ⦄ := by
  unfold create_team
  have := usize_max_ge
  step*
  step with create_team_loop_spec as ⟨ws1, h1⟩
  step*
  intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
  have hr := r_post; simp only [‹r = _›] at hr
  have hid := r1_post; simp only [‹r1 = _›] at hid
  exact ⟨ids.val, id, i, hr, hid.2, i_post, rfl, by simp [ws2_post, h1, ws_post, s1_post]⟩

theorem update_team_spec (a : Principal) (s : Snapshot) (id : U64) (p : TeamPatch) :
    update_team a s id p ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ t t', findTeam (Snapshot.toSt s) id.val = some t ∧ rep = .Done ∧ ws.val = [.PutTeam t'] ∧
        t'.id = t.id ∧ t'.spend = t.spend ∧ t'.max_budget = p.max_budget.getD t.max_budget ∧
        t'.rpm = p.rpm.getD t.rpm ∧ t'.tpm = p.tpm.getD t.tpm ∧
        t'.budget_duration = p.budget_duration.getD t.budget_duration ∧
        (p.budget_duration = none → t'.budget_reset_at = t.budget_reset_at) ∧
        (∀ v, p.budget_duration = some v → t'.budget_reset_at.val = sat (a.now.val + v.val)) ∧
        t'.blocked = p.blocked.getD t.blocked ∧ t'.all_models = p.all_models.getD t.all_models ⦄ := by
  unfold update_team
  step*
  apply WP.spec_bind (Pₘ := fun x => x = { t with max_budget := p.max_budget.getD t.max_budget })
  · split <;> simp_all
  intro t1 h1
  apply WP.spec_bind (Pₘ := fun x => x = { t1 with rpm := p.rpm.getD t1.rpm })
  · split <;> simp_all
  intro t2 h2
  apply WP.spec_bind (Pₘ := fun x => x = { t2 with tpm := p.tpm.getD t2.tpm })
  · split <;> simp_all
  intro t3 h3
  apply WP.spec_bind (Pₘ := fun x => ∃ ra : U64, x = { t3 with budget_duration := p.budget_duration.getD t3.budget_duration, budget_reset_at := ra } ∧
      (p.budget_duration = none → ra = t3.budget_reset_at) ∧ (∀ v, p.budget_duration = some v → ra.val = sat (a.now.val + v.val)))
  · split
    · simp_all
    · step*; simp_all
  intro t4 ⟨ra, h4, h4a, h4b⟩
  apply WP.spec_bind (Pₘ := fun x => x = { t4 with blocked := p.blocked.getD t4.blocked })
  · split <;> simp_all
  intro t5 h5
  apply WP.spec_bind (Pₘ := fun x => x = { t5 with all_models := p.all_models.getD t5.all_models })
  · split <;> simp_all
  intro t6 h6
  step*
  intro ws rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
  refine ⟨t, t6, by rw [← findTeam_toSt, ← o_post]; assumption, rfl, v_post, ?_⟩
  subst h6 h5 h4 h3 h2 h1
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, h4a, h4b, rfl, rfl⟩

attribute [local step] clear_team_models_spec clear_key_models_spec set_team_models_loop_spec
  set_key_models_loop_spec create_key_loop0_spec create_key_loop1_spec

theorem delete_team_spec (s : Snapshot) (id : U64)
    (hs : (s.team_models.val.filter (fun g => g.team = id)).length < Usize.max) :
    delete_team s id ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ t, findTeam (Snapshot.toSt s) id.val = some t ∧ (∀ k ∈ (Snapshot.toSt s).keys, k.team ≠ id) ∧ rep = .Done ∧
        ws.val = (s.team_models.val.filter (fun g => g.team = id)).map (fun g => .DelTeamModel id g.model) ++
          [.DelTeam id] ⦄ := by
  unfold delete_team
  step*
  · intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    refine ⟨_, by rw [← findTeam_toSt, ← o_post]; assumption, fun k hk he => ‹¬b = true› (b_post.2 ⟨k, hk, he⟩),
      rfl, by simp [ws1_post, ws_post, vec_new_val]⟩

theorem set_team_models_spec (s : Snapshot) (id : U64) (names : alloc.vec.Vec (alloc.vec.Vec U8))
    (hs : (s.team_models.val.filter (fun g => g.team = id)).length + names.val.length ≤ Usize.max) :
    set_team_models s id names ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ t ids, findTeam (Snapshot.toSt s) id.val = some t ∧ Resolved (Snapshot.toSt s) names.val ids ∧ rep = .Done ∧
        ws.val = (s.team_models.val.filter (fun g => g.team = id)).map (fun g => .DelTeamModel id g.model) ++
          ids.map (fun m => .PutTeamModel { team := id, model := m }) ⦄ := by
  unfold set_team_models
  step*
  · intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    have hr := r_post; simp only [‹r = _›] at hr
    exact ⟨_, ids.val, by rw [← findTeam_toSt, ← o_post]; assumption, hr, rfl, by simp [ws1_post, ws_post, vec_new_val]⟩

theorem create_key_spec (a : Principal) (s : Snapshot) (spec : KeySpec) (names : alloc.vec.Vec (alloc.vec.Vec U8))
    (hn : names.val.length + 1 < Usize.max) :
    create_key a s spec names ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ (ids : List U64) (id ra : U64), (spec.team.val ≠ 0 → ∃ t, findTeam (Snapshot.toSt s) spec.team.val = some t) ∧
        Resolved (Snapshot.toSt s) names.val ids ∧
        id.val = s.settings.next_id.val + 1 ∧ ra.val = sat (a.now.val + spec.budget_duration.val) ∧ rep = .Created id ∧
        ws.val = .PutKey { id := id, team := spec.team, user := spec.user, max_budget := spec.max_budget, spend := 0#u64, rpm := spec.rpm, tpm := spec.tpm, max_parallel := spec.max_parallel, expires_at := spec.expires_at, budget_duration := spec.budget_duration, budget_reset_at := ra, blocked := false, admin := spec.admin, all_models := spec.all_models } ::
          (ids.map (fun m => .PutKeyModel { key := id, model := m }) ++ [.SetSettings { s.settings with next_id := id }]) ⦄ := by
  unfold create_key
  have := usize_max_ge
  step*
  · intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    have hr := r_post; simp only [‹r = _›] at hr
    have hid := r1_post; simp only [‹r1 = _›] at hid
    exact ⟨ids.val, id, i, fun _ => ⟨_, by rw [← findTeam_toSt, ← o_post]; assumption⟩, hr, hid.2, i_post, rfl,
      by simp [ws2_post, ws1_post, ws_post, vec_new_val, s1_post]⟩
  · intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    have hr := r_post; simp only [‹r = _›] at hr
    have hid := r1_post; simp only [‹r1 = _›] at hid
    exact ⟨ids.val, id, i, fun h => absurd (eq0_of_not_bne ‹_›) h, hr, hid.2, i_post, rfl,
      by simp [ws2_post, ws1_post, ws_post, vec_new_val, s1_post]⟩

theorem update_key_spec (a : Principal) (s : Snapshot) (id : U64) (p : KeyPatch) :
    update_key a s id p ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ k k', findKey (Snapshot.toSt s) id.val = some k ∧ rep = .Done ∧ ws.val = [.PutKey k'] ∧
        k'.id = k.id ∧ k'.team = k.team ∧ k'.user = k.user ∧ k'.spend = k.spend ∧ k'.admin = k.admin ∧
        k'.max_budget = p.max_budget.getD k.max_budget ∧
        k'.rpm = p.rpm.getD k.rpm ∧ k'.tpm = p.tpm.getD k.tpm ∧ k'.max_parallel = p.max_parallel.getD k.max_parallel ∧
        k'.expires_at = p.expires_at.getD k.expires_at ∧
        k'.budget_duration = p.budget_duration.getD k.budget_duration ∧
        (p.budget_duration = none → k'.budget_reset_at = k.budget_reset_at) ∧
        (∀ v, p.budget_duration = some v → k'.budget_reset_at.val = sat (a.now.val + v.val)) ∧
        k'.blocked = p.blocked.getD k.blocked ∧ k'.all_models = p.all_models.getD k.all_models ⦄ := by
  unfold update_key
  step*
  apply WP.spec_bind (Pₘ := fun x => x = { k with max_budget := p.max_budget.getD k.max_budget })
  · split <;> simp_all
  intro t1 h1
  apply WP.spec_bind (Pₘ := fun x => x = { t1 with rpm := p.rpm.getD t1.rpm })
  · split <;> simp_all
  intro t2 h2
  apply WP.spec_bind (Pₘ := fun x => x = { t2 with tpm := p.tpm.getD t2.tpm })
  · split <;> simp_all
  intro t3 h3
  apply WP.spec_bind (Pₘ := fun x => x = { t3 with max_parallel := p.max_parallel.getD t3.max_parallel })
  · split <;> simp_all
  intro t3a h3a
  apply WP.spec_bind (Pₘ := fun x => x = { t3a with expires_at := p.expires_at.getD t3a.expires_at })
  · split <;> simp_all
  intro t3b h3b
  apply WP.spec_bind (Pₘ := fun x => ∃ ra : U64, x = { t3b with budget_duration := p.budget_duration.getD t3b.budget_duration, budget_reset_at := ra } ∧
      (p.budget_duration = none → ra = t3b.budget_reset_at) ∧ (∀ v, p.budget_duration = some v → ra.val = sat (a.now.val + v.val)))
  · split
    · simp_all
    · step*; simp_all
  intro t4 ⟨ra, h4, h4a, h4b⟩
  apply WP.spec_bind (Pₘ := fun x => x = { t4 with blocked := p.blocked.getD t4.blocked })
  · split <;> simp_all
  intro t5 h5
  apply WP.spec_bind (Pₘ := fun x => x = { t5 with all_models := p.all_models.getD t5.all_models })
  · split <;> simp_all
  intro t6 h6
  step*
  intro ws rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
  refine ⟨k, t6, by rw [← findKey_toSt, ← o_post]; assumption, rfl, v_post, ?_⟩
  subst h6 h5 h4 h3b h3a h3 h2 h1
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h4a, h4b, rfl, rfl⟩

theorem delete_key_spec (s : Snapshot) (id : U64)
    (hs : (s.key_models.val.filter (fun g => g.key = id)).length < Usize.max) :
    delete_key s id ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ k, findKey (Snapshot.toSt s) id.val = some k ∧ rep = .Done ∧
        ws.val = (s.key_models.val.filter (fun g => g.key = id)).map (fun g => .DelKeyModel id g.model) ++
          [.DelKey id] ⦄ := by
  unfold delete_key
  step*
  · intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    exact ⟨_, by rw [← findKey_toSt, ← o_post]; assumption, rfl, by simp [ws1_post, ws_post, vec_new_val]⟩

theorem set_key_models_spec (s : Snapshot) (id : U64) (names : alloc.vec.Vec (alloc.vec.Vec U8))
    (hs : (s.key_models.val.filter (fun g => g.key = id)).length + names.val.length ≤ Usize.max) :
    set_key_models s id names ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ k ids, findKey (Snapshot.toSt s) id.val = some k ∧ Resolved (Snapshot.toSt s) names.val ids ∧ rep = .Done ∧
        ws.val = (s.key_models.val.filter (fun g => g.key = id)).map (fun g => .DelKeyModel id g.model) ++
          ids.map (fun m => .PutKeyModel { key := id, model := m }) ⦄ := by
  unfold set_key_models
  step*
  · intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    have hr := r_post; simp only [‹r = _›] at hr
    exact ⟨_, ids.val, by rw [← findKey_toSt, ← o_post]; assumption, hr, rfl, by simp [ws1_post, ws_post, vec_new_val]⟩

theorem reset_key_spend_spec (s : Snapshot) (id : U64) :
    reset_key_spend s id ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ k, findKey (Snapshot.toSt s) id.val = some k ∧ rep = .Done ∧ ws.val = [.PutKey { k with spend := 0#u64 }] ⦄ := by
  unfold reset_key_spend
  step*
  intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
  exact ⟨_, by rw [← findKey_toSt, ← o_post]; assumption, rfl, v_post⟩

theorem delete_deployment_spec (s : Snapshot) (id : U64) :
    delete_deployment s id ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ d, findDeployment (Snapshot.toSt s) id.val = some d ∧ rep = .Done ∧ ws.val = [.DelDeployment id] ⦄ := by
  unfold delete_deployment
  step*
  intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
  exact ⟨_, by rw [← findDeployment_toSt, ← o_post]; assumption, rfl, v_post⟩

/-- The health a deployment keeps across an upsert: the old one, or none. -/
def oldHealth (st : St) (id : U64) : U64 × U64 × U64 :=
  ((findDeployment st id.val).map (fun o => (o.fails, o.fail_window, o.cooldown_until))).getD (0#u64, 0#u64, 0#u64)

theorem upsert_deployment_spec (s : Snapshot) (nm : alloc.vec.Vec U8) (spec : DeploymentSpec) :
    upsert_deployment s nm spec ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ (m : U64) (pre : List Write), rep = .Created m ∧
        ((findModel (Snapshot.toSt s) nm.val = some m.val ∧ pre = []) ∨
          (findModel (Snapshot.toSt s) nm.val = none ∧ m.val = s.settings.next_id.val + 1 ∧
            pre = [.PutModel { id := m, «name» := nm }, .SetSettings { s.settings with next_id := m }])) ∧
        ws.val = pre ++ [.PutDeployment { id := spec.id, model := m, input_cost := spec.input_cost, output_cost := spec.output_cost, rpm := spec.rpm, tpm := spec.tpm, priority := spec.priority, enabled := spec.enabled, fails := (oldHealth (Snapshot.toSt s) spec.id).1, fail_window := (oldHealth (Snapshot.toSt s) spec.id).2.1, cooldown_until := (oldHealth (Snapshot.toSt s) spec.id).2.2 }] ⦄ := by
  unfold upsert_deployment
  have := usize_max_ge
  h5i_steps
  all_goals
    intro ws' rep h; obtain ⟨rfl, rfl⟩ := ok_inj h
    have hm : findModel (Snapshot.toSt s) nm.val = o.map (·.val) := by rw [← findModel_toSt, o_post]; rfl
    have hd := (findDeployment_toSt s spec.id).symm.trans o1_post.symm
  · have hid := r_post; simp only [‹r = _›] at hid
    refine ⟨id, _, rfl, Or.inr ⟨by rw [hm, ‹o = none›]; rfl, hid.2, rfl⟩, ?_⟩
    simp [ws2_post, ws1_post, ws_post, vec_new_val, s1_post, v_post, oldHealth, hd]
  · have hid := r_post; simp only [‹r = _›] at hid
    refine ⟨id, _, rfl, Or.inr ⟨by rw [hm, ‹o = none›]; rfl, hid.2, rfl⟩, ?_⟩
    simp [ws2_post, ws1_post, ws_post, vec_new_val, s1_post, v_post, oldHealth, hd]
  · refine ⟨m, _, rfl, Or.inl ⟨by rw [hm, ‹o = some m›]; rfl, rfl⟩, ?_⟩
    simp [ws_post, vec_new_val, oldHealth, hd]
  · refine ⟨m, _, rfl, Or.inl ⟨by rw [hm, ‹o = some m›]; rfl, rfl⟩, ?_⟩
    simp [ws_post, vec_new_val, oldHealth, hd]

/-! ## Admission -/

/-- What a successful admission by the master key writes: the deployment's
counter, a reservation of the quoted price against no key and no team, and
the counter moved past its id. -/
def MasterAdmitted (s : Snapshot) (a : Principal) (m pt mt : U64) (ex : List Nat) (ws : List Write) (rep : Reply) : Prop :=
  ∃ (d : Deployment) (id amt : U64) (u : Usage), Best (Snapshot.toSt s) a.now.val m.val ex d ∧
    amt.val = price d.input_cost.val d.output_cost.val pt.val mt.val ∧
    id.val = s.settings.next_id.val + 1 ∧ rep = .Admitted id d.id amt ∧
    Counted (Snapshot.toSt s) 2#u64 d.id a.now.val u ∧
    ws = [.PutUsage u,
      .PutReservation { id := id, key_id := 0#u64, team := 0#u64, deployment := d.id, model := m, input_cost := d.input_cost, output_cost := d.output_cost, amount := amt, created_at := a.now },
      .SetSettings { s.settings with next_id := id }]

/-- What a successful admission by a key writes, and the policy it passed. -/
def KeyAdmitted (s : Snapshot) (a : Principal) (m pt mt : U64) (ex : List Nat) (ws : List Write) (rep : Reply) : Prop :=
  ∃ (k : Key) (t : Option Team) (d : Deployment) (id amt : U64) (k2 : Key) (uk ud : Usage) (tw : List Write),
    AdmitByKey (Snapshot.toSt s) a m.val pt.val mt.val ex k t d amt.val ∧
    id.val = s.settings.next_id.val + 1 ∧ rep = .Admitted id d.id amt ∧
    KeyNow k k2 a.now.val ∧ Counted (Snapshot.toSt s) 0#u64 k.id a.now.val uk ∧
    TeamWrites (Snapshot.toSt s) a.now.val t tw ∧ Counted (Snapshot.toSt s) 2#u64 d.id a.now.val ud ∧
    ws = [.PutKey k2, .PutUsage uk] ++ tw ++ [.PutUsage ud,
      .PutReservation { id := id, key_id := k.id, team := k.team, deployment := d.id, model := m, input_cost := d.input_cost, output_cost := d.output_cost, amount := amt, created_at := a.now },
      .SetSettings { s.settings with next_id := id }]

theorem admit_spec (a : Principal) (s : Snapshot) (nm : alloc.vec.Vec U8) (pt mt : U64) (ex : alloc.vec.Vec U64) :
    admit a s nm pt mt ex ⦃ res => ∀ ws rep, res = .Ok (ws, rep) →
      ∃ m : U64, findModel (Snapshot.toSt s) nm.val = some m.val ∧
        (a.master = true → MasterAdmitted s a m pt mt (ex.val.map (·.val)) ws.val rep) ∧
        (a.master = false → KeyAdmitted s a m pt mt (ex.val.map (·.val)) ws.val rep) ⦄ := by
  unfold admit
  step*
  · have hm : findModel (Snapshot.toSt s) nm.val = some m.val := by
      rw [← findModel_toSt]; unfold findL; rw [← o_post, ‹o = some m›]; rfl
    apply WP.spec_mono (admit_master_spec a s m pt mt ex)
    intro res h ws rep hr
    exact ⟨m, hm, fun _ => h ws rep hr, fun h' => by simp_all⟩
  · have hm : findModel (Snapshot.toSt s) nm.val = some m.val := by
      rw [← findModel_toSt]; unfold findL; rw [← o_post, ‹o = some m›]; rfl
    have hm' : a.master = false := by simpa using ‹¬a.master = true›
    apply WP.spec_mono (admit_key_spec a s m pt mt ex hm')
    intro res h ws rep hr
    exact ⟨m, hm, fun h' => by simp_all, fun _ => h ws rep hr⟩

/-! ## Reads -/

theorem key_info_spec (a : Principal) (s : Snapshot) (id : U64) :
    key_info a s id ⦃ res => ∀ ws rep, res = .Ok (ws, rep) → ws.val = [] ⦄ := by
  unfold key_info; step*

theorem team_info_spec (a : Principal) (s : Snapshot) (id : U64) :
    team_info a s id ⦃ res => ∀ ws rep, res = .Ok (ws, rep) → ws.val = [] ⦄ := by
  unfold team_info; step*

/-! ## Who reaches management -/

/-- The management commands: all but the six a key may run. -/
def IsManage : Command → Prop
  | .Admit .. | .Settle .. | .Expire .. | .KeyInfo .. | .TeamInfo .. | .ListModels => False
  | _ => True

theorem manage_of {a : Principal} {s : Snapshot} {c : Command} {res}
    (h : transition a s c = ok res) (hc : IsManage c) (hr : ∀ e, res ≠ .Err e ∨ e ≠ .Forbidden) :
    IsAdmin (Snapshot.toSt s) a ∧ manage a s c = ok res := by
  cases c <;> simp only [IsManage] at hc <;> simp only [transition] at h <;>
  · obtain ⟨b, hb, h⟩ := bind_eq_ok.1 h
    have hb' := post_of_ok (is_admin_spec a s) hb
    split at h
    · exact ⟨hb'.1 ‹_›, h⟩
    · simp at h; subst h; simpa using hr .Forbidden

/-! ## Successful runs fit in a vector

The specs above of the commands with loops assume the write list fits in a
vector. A successful run shows that it did: the lemmas below read the loops
backwards (partial correctness). -/

theorem push_ok_len {α : Type} {v v' : alloc.vec.Vec α} {x : α} (h : v.push x = ok v') :
    v.val.length < Usize.max ∧ v'.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · rename_i hc
    simp at h; subst h
    refine ⟨?_, by simp⟩
    have := usize_max_ge
    simp only [U32.max_eq, Bool.or_eq_true, decide_eq_true_eq] at hc
    omega
  · simp at h

theorem create_team_loop_ok {ids : alloc.vec.Vec U64} {id : U64} {ws out : alloc.vec.Vec Write}
    (h : create_team_loop ids id ws 0#usize = ok out) :
    out.val = ws.val ++ ids.val.map (fun m => .PutTeamModel { team := id, model := m }) := by
  unfold create_team_loop at h
  refine loop_idx_ok _ (fun x => x.2) ids.val.length
    (fun x => x.1.val = ws.val ++ (ids.val.take x.2.val).map (fun m => .PutTeamModel { team := id, model := m }))
    (fun out => out.val = ws.val ++ ids.val.map (fun m => .PutTeamModel { team := id, model := m })) ?_ _ _ (by simp) (by simp) h
  rintro ⟨w, i⟩ r hI hi hr
  simp only at hI hi hr
  unfold create_team_loop.body at hr
  h5i_invert hr
  · obtain ⟨-, hw1⟩ := push_ok_len hws1
    have hget := vec_index_slice_ok_get? hi2
    have hi3' := add_ok_val hi3
    have hlt : i.val < ids.val.length := by scalar_tac
    simp only
    refine ⟨?_, by simp [hi3'], by simp [hi3']; omega⟩
    have h1 : (1#usize).val = 1 := rfl
    rw [hw1, hI, hi3', h1, List.take_add_one, hget]; simp
  · simp only
    rw [hI, List.take_of_length_le (by scalar_tac)]

theorem set_team_models_loop_ok {ids : alloc.vec.Vec U64} {id : U64} {ws out : alloc.vec.Vec Write}
    (h : set_team_models_loop id ids ws 0#usize = ok out) :
    out.val = ws.val ++ ids.val.map (fun m => .PutTeamModel { team := id, model := m }) := by
  unfold set_team_models_loop at h
  refine loop_idx_ok _ (fun x => x.2) ids.val.length
    (fun x => x.1.val = ws.val ++ (ids.val.take x.2.val).map (fun m => .PutTeamModel { team := id, model := m }))
    (fun out => out.val = ws.val ++ ids.val.map (fun m => .PutTeamModel { team := id, model := m })) ?_ _ _ (by simp) (by simp) h
  rintro ⟨w, i⟩ r hI hi hr
  simp only at hI hi hr
  unfold set_team_models_loop.body at hr
  h5i_invert hr
  · obtain ⟨-, hw1⟩ := push_ok_len hws1
    have hget := vec_index_slice_ok_get? hi2
    have hi3' := add_ok_val hi3
    have hlt : i.val < ids.val.length := by scalar_tac
    simp only
    refine ⟨?_, by simp [hi3'], by simp [hi3']; omega⟩
    have h1 : (1#usize).val = 1 := rfl
    rw [hw1, hI, hi3', h1, List.take_add_one, hget]; simp
  · simp only
    rw [hI, List.take_of_length_le (by scalar_tac)]

theorem create_key_loop0_ok {ids : alloc.vec.Vec U64} {id : U64} {ws out : alloc.vec.Vec Write}
    (h : create_key_loop0 ids id ws 0#usize = ok out) :
    out.val = ws.val ++ ids.val.map (fun m => .PutKeyModel { key := id, model := m }) := by
  unfold create_key_loop0 at h
  refine loop_idx_ok _ (fun x => x.2) ids.val.length
    (fun x => x.1.val = ws.val ++ (ids.val.take x.2.val).map (fun m => .PutKeyModel { key := id, model := m }))
    (fun out => out.val = ws.val ++ ids.val.map (fun m => .PutKeyModel { key := id, model := m })) ?_ _ _ (by simp) (by simp) h
  rintro ⟨w, i⟩ r hI hi hr
  simp only at hI hi hr
  unfold create_key_loop0.body at hr
  h5i_invert hr
  · obtain ⟨-, hw1⟩ := push_ok_len hws1
    have hget := vec_index_slice_ok_get? hi2
    have hi3' := add_ok_val hi3
    have hlt : i.val < ids.val.length := by scalar_tac
    simp only
    refine ⟨?_, by simp [hi3'], by simp [hi3']; omega⟩
    have h1 : (1#usize).val = 1 := rfl
    rw [hw1, hI, hi3', h1, List.take_add_one, hget]; simp
  · simp only
    rw [hI, List.take_of_length_le (by scalar_tac)]

theorem create_key_loop1_ok {ids : alloc.vec.Vec U64} {id : U64} {ws out : alloc.vec.Vec Write}
    (h : create_key_loop1 ids id ws 0#usize = ok out) :
    out.val = ws.val ++ ids.val.map (fun m => .PutKeyModel { key := id, model := m }) := by
  unfold create_key_loop1 at h
  refine loop_idx_ok _ (fun x => x.2) ids.val.length
    (fun x => x.1.val = ws.val ++ (ids.val.take x.2.val).map (fun m => .PutKeyModel { key := id, model := m }))
    (fun out => out.val = ws.val ++ ids.val.map (fun m => .PutKeyModel { key := id, model := m })) ?_ _ _ (by simp) (by simp) h
  rintro ⟨w, i⟩ r hI hi hr
  simp only at hI hi hr
  unfold create_key_loop1.body at hr
  h5i_invert hr
  · obtain ⟨-, hw1⟩ := push_ok_len hws1
    have hget := vec_index_slice_ok_get? hi2
    have hi3' := add_ok_val hi3
    have hlt : i.val < ids.val.length := by scalar_tac
    simp only
    refine ⟨?_, by simp [hi3'], by simp [hi3']; omega⟩
    have h1 : (1#usize).val = 1 := rfl
    rw [hw1, hI, hi3', h1, List.take_add_one, hget]; simp
  · simp only
    rw [hI, List.take_of_length_le (by scalar_tac)]

theorem set_key_models_loop_ok {ids : alloc.vec.Vec U64} {id : U64} {ws out : alloc.vec.Vec Write}
    (h : set_key_models_loop id ids ws 0#usize = ok out) :
    out.val = ws.val ++ ids.val.map (fun m => .PutKeyModel { key := id, model := m }) := by
  unfold set_key_models_loop at h
  refine loop_idx_ok _ (fun x => x.2) ids.val.length
    (fun x => x.1.val = ws.val ++ (ids.val.take x.2.val).map (fun m => .PutKeyModel { key := id, model := m }))
    (fun out => out.val = ws.val ++ ids.val.map (fun m => .PutKeyModel { key := id, model := m })) ?_ _ _ (by simp) (by simp) h
  rintro ⟨w, i⟩ r hI hi hr
  simp only at hI hi hr
  unfold set_key_models_loop.body at hr
  h5i_invert hr
  · obtain ⟨-, hw1⟩ := push_ok_len hws1
    have hget := vec_index_slice_ok_get? hi2
    have hi3' := add_ok_val hi3
    have hlt : i.val < ids.val.length := by scalar_tac
    simp only
    refine ⟨?_, by simp [hi3'], by simp [hi3']; omega⟩
    have h1 : (1#usize).val = 1 := rfl
    rw [hw1, hI, hi3', h1, List.take_add_one, hget]; simp
  · simp only
    rw [hI, List.take_of_length_le (by scalar_tac)]

theorem clear_team_models_ok {v : alloc.vec.Vec TeamModel} {x : U64} {ws out : alloc.vec.Vec Write}
    (h : clear_team_models v x ws = ok out) :
    out.val = ws.val ++ (v.val.filter (fun g => g.team = x)).map (fun g => .DelTeamModel x g.model) := by
  unfold clear_team_models clear_team_models_loop at h
  refine loop_idx_ok _ (fun x => x.2) v.val.length
    (fun y => y.1.val = ws.val ++ ((v.val.take y.2.val).filter (fun g => g.team = x)).map (fun g => .DelTeamModel x g.model))
    (fun out => out.val = ws.val ++ (v.val.filter (fun g => g.team = x)).map (fun g => .DelTeamModel x g.model)) ?_ _ _ (by simp) (by simp) h
  rintro ⟨w, i⟩ r hI hi hr
  simp only at hI hi hr
  unfold clear_team_models_loop.body at hr
  h5i_invert hr
  · have hget := vec_index_slice_ok_get? htm
    have hi3' := add_ok_val hi2
    have hlt : i.val < v.val.length := by scalar_tac
    simp only
    refine ⟨?_, by simp [hi3'], by simp [hi3']; omega⟩
    have h1 : (1#usize).val = 1 := rfl
    split at hws1
    · rename_i hcond
      obtain ⟨-, hw1⟩ := push_ok_len hws1
      rw [hw1, hI, hi3', h1, List.take_add_one, hget]; simp [hcond]
    · rename_i hcond
      simp at hws1; subst hws1
      rw [hI, hi3', h1, List.take_add_one, hget]; simp [hcond]
  · simp only
    rw [hI, List.take_of_length_le (by scalar_tac)]

theorem clear_key_models_ok {v : alloc.vec.Vec KeyModel} {x : U64} {ws out : alloc.vec.Vec Write}
    (h : clear_key_models v x ws = ok out) :
    out.val = ws.val ++ (v.val.filter (fun g => g.key = x)).map (fun g => .DelKeyModel x g.model) := by
  unfold clear_key_models clear_key_models_loop at h
  refine loop_idx_ok _ (fun x => x.2) v.val.length
    (fun y => y.1.val = ws.val ++ ((v.val.take y.2.val).filter (fun g => g.key = x)).map (fun g => .DelKeyModel x g.model))
    (fun out => out.val = ws.val ++ (v.val.filter (fun g => g.key = x)).map (fun g => .DelKeyModel x g.model)) ?_ _ _ (by simp) (by simp) h
  rintro ⟨w, i⟩ r hI hi hr
  simp only at hI hi hr
  unfold clear_key_models_loop.body at hr
  h5i_invert hr
  · have hget := vec_index_slice_ok_get? hkm
    have hi3' := add_ok_val hi2
    have hlt : i.val < v.val.length := by scalar_tac
    simp only
    refine ⟨?_, by simp [hi3'], by simp [hi3']; omega⟩
    have h1 : (1#usize).val = 1 := rfl
    split at hws1
    · rename_i hcond
      obtain ⟨-, hw1⟩ := push_ok_len hws1
      rw [hw1, hI, hi3', h1, List.take_add_one, hget]; simp [hcond]
    · rename_i hcond
      simp at hws1; subst hws1
      rw [hI, hi3', h1, List.take_add_one, hget]; simp [hcond]
  · simp only
    rw [hI, List.take_of_length_le (by scalar_tac)]

theorem create_team_fits {a : Principal} {s : Snapshot} {spec : TeamSpec} {names : alloc.vec.Vec (alloc.vec.Vec U8)} {ws rep}
    (h : create_team a s spec names = ok (.Ok (ws, rep))) : names.val.length + 1 < Usize.max := by
  unfold create_team at h
  h5i_invert h
  have h1 := post_of_ok (resolve_models_spec _ _) hr
  have h2 := create_team_loop_ok hws1
  have h3 := (push_ok_len hws2).1
  have h4 := (push_ok_len hws_1).2
  simp only at h1
  rw [h2, h4] at h3; simp only [vec_new_val, List.nil_append, List.length_append, List.length_singleton, List.length_map] at h3
  omega

theorem create_key_fits {a : Principal} {s : Snapshot} {spec : KeySpec} {names : alloc.vec.Vec (alloc.vec.Vec U8)} {ws rep}
    (h : create_key a s spec names = ok (.Ok (ws, rep))) : names.val.length + 1 < Usize.max := by
  unfold create_key at h
  h5i_invert h
  · have h1 := post_of_ok (resolve_models_spec _ _) hr
    have h2 := create_key_loop0_ok hws1
    have h3 := (push_ok_len hws2).1
    have h4 := (push_ok_len hws_1).2
    simp only at h1
    rw [h2, h4] at h3; simp only [vec_new_val, List.nil_append, List.length_append, List.length_singleton, List.length_map] at h3
    omega
  · have h1 := post_of_ok (resolve_models_spec _ _) hr
    have h2 := create_key_loop1_ok hws1
    have h3 := (push_ok_len hws2).1
    have h4 := (push_ok_len hws_1).2
    simp only at h1
    rw [h2, h4] at h3; simp only [vec_new_val, List.nil_append, List.length_append, List.length_singleton, List.length_map] at h3
    omega

theorem delete_team_fits {s : Snapshot} {id : U64} {ws rep} (h : delete_team s id = ok (.Ok (ws, rep))) :
    (s.team_models.val.filter (fun g => g.team = id)).length < Usize.max := by
  unfold delete_team at h
  h5i_invert h
  have h2 := clear_team_models_ok hws_1
  have h3 := (push_ok_len hws1).1
  rw [h2] at h3; simpa only [vec_new_val, List.nil_append, List.length_map] using h3

theorem set_team_models_fits {s : Snapshot} {id : U64} {names : alloc.vec.Vec (alloc.vec.Vec U8)} {ws rep}
    (h : set_team_models s id names = ok (.Ok (ws, rep))) :
    (s.team_models.val.filter (fun g => g.team = id)).length + names.val.length ≤ Usize.max := by
  unfold set_team_models at h
  h5i_invert h
  have h1 := post_of_ok (resolve_models_spec _ _) hr
  have h2 := clear_team_models_ok hws_1
  have h3 := set_team_models_loop_ok hws1
  have h4 := ws1.property
  simp only at h1
  rw [h3, h2] at h4; simp only [vec_new_val, List.nil_append, List.length_append, List.length_map] at h4
  omega

theorem delete_key_fits {s : Snapshot} {id : U64} {ws rep} (h : delete_key s id = ok (.Ok (ws, rep))) :
    (s.key_models.val.filter (fun g => g.key = id)).length < Usize.max := by
  unfold delete_key at h
  h5i_invert h
  have h2 := clear_key_models_ok hws_1
  have h3 := (push_ok_len hws1).1
  rw [h2] at h3; simpa only [vec_new_val, List.nil_append, List.length_map] using h3

theorem set_key_models_fits {s : Snapshot} {id : U64} {names : alloc.vec.Vec (alloc.vec.Vec U8)} {ws rep}
    (h : set_key_models s id names = ok (.Ok (ws, rep))) :
    (s.key_models.val.filter (fun g => g.key = id)).length + names.val.length ≤ Usize.max := by
  unfold set_key_models at h
  h5i_invert h
  have h1 := post_of_ok (resolve_models_spec _ _) hr
  have h2 := clear_key_models_ok hws_1
  have h3 := set_key_models_loop_ok hws1
  have h4 := ws1.property
  simp only at h1
  rw [h3, h2] at h4; simp only [vec_new_val, List.nil_append, List.length_append, List.length_map] at h4
  omega

theorem list_models_ok {a : Principal} {s : Snapshot} {ws rep} (h : list_models a s = ok (.Ok (ws, rep))) :
    ws.val = [] := by
  unfold list_models at h
  h5i_invert h <;> (rw [← h.1]; rfl)

theorem list_models_loop_spec (st : Settings) (v : alloc.vec.Vec Team) (v1 : alloc.vec.Vec Key)
    (v2 : alloc.vec.Vec Model) (v3 : alloc.vec.Vec Deployment) (v4 : alloc.vec.Vec KeyModel)
    (v5 : alloc.vec.Vec TeamModel) (v6 : alloc.vec.Vec Usage) (v7 : alloc.vec.Vec Reservation)
    (i i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 : U64) (b b1 b2 : Bool) (team : Option Team) :
    list_models_loop st v v1 v2 v3 v4 v5 v6 v7 i i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 b b1 b2 team
      (alloc.vec.Vec.new Model) 0#usize ⦃ _ => True ⦄ := by
  unfold list_models_loop
  apply loop_idx_spec _ (fun x => x.2) v2.val.length (fun x => x.1.val.length ≤ x.2.val) _ ?_ _ (by simp) (by simp)
  rintro ⟨out, j⟩ hI hj
  simp only at hI hj
  unfold list_models_loop.body
  h5i_steps
  have : j.val < v2.val.length := by scalar_tac
  refine ⟨by simp [out1_post]; omega, by omega, by omega⟩

/-! ## Every command -/

/-- What a successful management command writes (the caller is an admin). -/
def ManageEffect (s : Snapshot) (a : Principal) : Command → List Write → Reply → Prop
  | .Configure af cs ttl, ws, rep => rep = .Done ∧
      ws = [.SetSettings { s.settings with allowed_fails := af, cooldown_secs := cs, reservation_ttl := ttl }]
  | .CreateTeam spec names, ws, rep =>
      ∃ (ids : List U64) (id ra : U64), Resolved (Snapshot.toSt s) names.val ids ∧
        id.val = s.settings.next_id.val + 1 ∧ ra.val = sat (a.now.val + spec.budget_duration.val) ∧ rep = .Created id ∧
        ws = .PutTeam { id := id, max_budget := spec.max_budget, spend := 0#u64, rpm := spec.rpm, tpm := spec.tpm, budget_duration := spec.budget_duration, budget_reset_at := ra, blocked := false, all_models := spec.all_models } ::
          (ids.map (fun m => .PutTeamModel { team := id, model := m }) ++ [.SetSettings { s.settings with next_id := id }])
  | .UpdateTeam id p, ws, rep =>
      ∃ t t', findTeam (Snapshot.toSt s) id.val = some t ∧ rep = .Done ∧ ws = [.PutTeam t'] ∧
        t'.id = t.id ∧ t'.spend = t.spend ∧ t'.max_budget = p.max_budget.getD t.max_budget ∧
        t'.rpm = p.rpm.getD t.rpm ∧ t'.tpm = p.tpm.getD t.tpm ∧
        t'.budget_duration = p.budget_duration.getD t.budget_duration ∧
        (p.budget_duration = none → t'.budget_reset_at = t.budget_reset_at) ∧
        (∀ v, p.budget_duration = some v → t'.budget_reset_at.val = sat (a.now.val + v.val)) ∧
        t'.blocked = p.blocked.getD t.blocked ∧ t'.all_models = p.all_models.getD t.all_models
  | .DeleteTeam id, ws, rep =>
      ∃ t, findTeam (Snapshot.toSt s) id.val = some t ∧ (∀ k ∈ (Snapshot.toSt s).keys, k.team ≠ id) ∧ rep = .Done ∧
        ws = (s.team_models.val.filter (fun g => g.team = id)).map (fun g => .DelTeamModel id g.model) ++ [.DelTeam id]
  | .SetTeamModels id names, ws, rep =>
      ∃ t ids, findTeam (Snapshot.toSt s) id.val = some t ∧ Resolved (Snapshot.toSt s) names.val ids ∧ rep = .Done ∧
        ws = (s.team_models.val.filter (fun g => g.team = id)).map (fun g => .DelTeamModel id g.model) ++
          ids.map (fun m => .PutTeamModel { team := id, model := m })
  | .CreateKey spec names, ws, rep =>
      ∃ (ids : List U64) (id ra : U64), (spec.team.val ≠ 0 → ∃ t, findTeam (Snapshot.toSt s) spec.team.val = some t) ∧
        Resolved (Snapshot.toSt s) names.val ids ∧
        id.val = s.settings.next_id.val + 1 ∧ ra.val = sat (a.now.val + spec.budget_duration.val) ∧ rep = .Created id ∧
        ws = .PutKey { id := id, team := spec.team, user := spec.user, max_budget := spec.max_budget, spend := 0#u64, rpm := spec.rpm, tpm := spec.tpm, max_parallel := spec.max_parallel, expires_at := spec.expires_at, budget_duration := spec.budget_duration, budget_reset_at := ra, blocked := false, admin := spec.admin, all_models := spec.all_models } ::
          (ids.map (fun m => .PutKeyModel { key := id, model := m }) ++ [.SetSettings { s.settings with next_id := id }])
  | .UpdateKey id p, ws, rep =>
      ∃ k k', findKey (Snapshot.toSt s) id.val = some k ∧ rep = .Done ∧ ws = [.PutKey k'] ∧
        k'.id = k.id ∧ k'.team = k.team ∧ k'.user = k.user ∧ k'.spend = k.spend ∧ k'.admin = k.admin ∧
        k'.max_budget = p.max_budget.getD k.max_budget ∧
        k'.rpm = p.rpm.getD k.rpm ∧ k'.tpm = p.tpm.getD k.tpm ∧ k'.max_parallel = p.max_parallel.getD k.max_parallel ∧
        k'.expires_at = p.expires_at.getD k.expires_at ∧
        k'.budget_duration = p.budget_duration.getD k.budget_duration ∧
        (p.budget_duration = none → k'.budget_reset_at = k.budget_reset_at) ∧
        (∀ v, p.budget_duration = some v → k'.budget_reset_at.val = sat (a.now.val + v.val)) ∧
        k'.blocked = p.blocked.getD k.blocked ∧ k'.all_models = p.all_models.getD k.all_models
  | .DeleteKey id, ws, rep =>
      ∃ k, findKey (Snapshot.toSt s) id.val = some k ∧ rep = .Done ∧
        ws = (s.key_models.val.filter (fun g => g.key = id)).map (fun g => .DelKeyModel id g.model) ++ [.DelKey id]
  | .SetKeyModels id names, ws, rep =>
      ∃ k ids, findKey (Snapshot.toSt s) id.val = some k ∧ Resolved (Snapshot.toSt s) names.val ids ∧ rep = .Done ∧
        ws = (s.key_models.val.filter (fun g => g.key = id)).map (fun g => .DelKeyModel id g.model) ++
          ids.map (fun m => .PutKeyModel { key := id, model := m })
  | .ResetKeySpend id, ws, rep =>
      ∃ k, findKey (Snapshot.toSt s) id.val = some k ∧ rep = .Done ∧ ws = [.PutKey { k with spend := 0#u64 }]
  | .UpsertDeployment nm spec, ws, rep =>
      ∃ (m : U64) (pre : List Write), rep = .Created m ∧
        ((findModel (Snapshot.toSt s) nm.val = some m.val ∧ pre = []) ∨
          (findModel (Snapshot.toSt s) nm.val = none ∧ m.val = s.settings.next_id.val + 1 ∧
            pre = [.PutModel { id := m, «name» := nm }, .SetSettings { s.settings with next_id := m }])) ∧
        ws = pre ++ [.PutDeployment { id := spec.id, model := m, input_cost := spec.input_cost, output_cost := spec.output_cost, rpm := spec.rpm, tpm := spec.tpm, priority := spec.priority, enabled := spec.enabled, fails := (oldHealth (Snapshot.toSt s) spec.id).1, fail_window := (oldHealth (Snapshot.toSt s) spec.id).2.1, cooldown_until := (oldHealth (Snapshot.toSt s) spec.id).2.2 }]
  | .DeleteDeployment id, ws, rep =>
      ∃ d, findDeployment (Snapshot.toSt s) id.val = some d ∧ rep = .Done ∧ ws = [.DelDeployment id]
  | .Dump, ws, rep => ws = [] ∧ rep = .State s
  | _, _, _ => False

/-- What a successful command writes, and what it checked. -/
def Effect (s : Snapshot) (a : Principal) : Command → List Write → Reply → Prop
  | .Admit nm pt mt ex, ws, rep =>
      ∃ m : U64, findModel (Snapshot.toSt s) nm.val = some m.val ∧
        (a.master = true → MasterAdmitted s a m pt mt (ex.val.map (·.val)) ws rep) ∧
        (a.master = false → KeyAdmitted s a m pt mt (ex.val.map (·.val)) ws rep)
  | .Settle id pt ct status, ws, rep =>
      ∃ (r : Reservation) (c tokens : U64) (kw tw : List Write) (ud : Usage) (dw : List Write),
        findReservation (Snapshot.toSt s) id.val = some r ∧ MayClose (Snapshot.toSt s) a r ∧
        c.val = price r.input_cost.val r.output_cost.val pt.val ct.val ∧ tokens.val = sat (pt.val + ct.val) ∧
        rep = .Settled c ∧
        SettleKeyWrites (Snapshot.toSt s) a.now.val c.val tokens.val r.key_id kw ∧
        SettleTeamWrites (Snapshot.toSt s) a.now.val c.val tokens.val r.team tw ∧
        TokCounted (Snapshot.toSt s) 2#u64 r.deployment a.now.val tokens.val ud ∧
        SettleDeploymentWrites (Snapshot.toSt s) a.now.val status r.deployment dw ∧
        ws = [.DelReservation id] ++ kw ++ tw ++ [.PutUsage ud] ++ dw ++
          [.Emit { reservation := id, key := r.key_id, team := r.team, deployment := r.deployment, model := r.model, prompt_tokens := pt, completion_tokens := ct, cost := c, «at» := a.now, status := status }]
  | .Expire id, ws, rep =>
      ∃ r, findReservation (Snapshot.toSt s) id.val = some r ∧ MayClose (Snapshot.toSt s) a r ∧
        sat (r.created_at.val + s.settings.reservation_ttl.val) ≤ a.now.val ∧ rep = .Settled 0#u64 ∧
        ws = [.DelReservation id,
          .Emit { reservation := id, key := r.key_id, team := r.team, deployment := r.deployment, model := r.model, prompt_tokens := 0#u64, completion_tokens := 0#u64, cost := 0#u64, «at» := a.now, status := .Expired }]
  | .KeyInfo _, ws, _ => ws = []
  | .TeamInfo _, ws, _ => ws = []
  | .ListModels, ws, _ => ws = []
  | c, ws, rep => IsAdmin (Snapshot.toSt s) a ∧ ManageEffect s a c ws rep

theorem dump_eq (a : Principal) (s : Snapshot) :
    manage a s .Dump = ok (.Ok (alloc.vec.Vec.new Write, .State s)) := by
  simp [manage, gateway_kernel.Schema.Snapshot.clone_eq]

/-- Every successful run of the kernel, summed up by `Effect`. -/
theorem transition_effect {a : Principal} {s : Snapshot} {c : Command} {ws : alloc.vec.Vec Write} {rep : Reply}
    (h : transition a s c = ok (.Ok (ws, rep))) : Effect s a c ws.val rep := by
  have hr : ∀ e, (core.result.Result.Ok (ws, rep) : core.result.Result _ Error) ≠ .Err e ∨ e ≠ .Forbidden :=
    fun e => .inl (by simp)
  cases c with
  | Admit nm pt mt ex => exact post_of_ok (admit_spec a s nm pt mt ex) h ws rep rfl
  | Settle id pt ct st => exact post_of_ok (settle_spec a s id pt ct st) h ws rep rfl
  | Expire id => exact post_of_ok (expire_spec a s id) h ws rep rfl
  | KeyInfo id => exact post_of_ok (key_info_spec a s id) h ws rep rfl
  | TeamInfo id => exact post_of_ok (team_info_spec a s id) h ws rep rfl
  | ListModels => exact list_models_ok h
  | Configure af cs ttl =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (configure_spec s af cs ttl) hm ws rep rfl⟩
  | CreateTeam spec names =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (create_team_spec a s spec names (create_team_fits hm)) hm ws rep rfl⟩
  | UpdateTeam id p =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (update_team_spec a s id p) hm ws rep rfl⟩
  | DeleteTeam id =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (delete_team_spec s id (delete_team_fits hm)) hm ws rep rfl⟩
  | SetTeamModels id names =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (set_team_models_spec s id names (set_team_models_fits hm)) hm ws rep rfl⟩
  | CreateKey spec names =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (create_key_spec a s spec names (create_key_fits hm)) hm ws rep rfl⟩
  | UpdateKey id p =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (update_key_spec a s id p) hm ws rep rfl⟩
  | DeleteKey id =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (delete_key_spec s id (delete_key_fits hm)) hm ws rep rfl⟩
  | SetKeyModels id names =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (set_key_models_spec s id names (set_key_models_fits hm)) hm ws rep rfl⟩
  | ResetKeySpend id =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (reset_key_spend_spec s id) hm ws rep rfl⟩
  | UpsertDeployment nm spec =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (upsert_deployment_spec s nm spec) hm ws rep rfl⟩
  | DeleteDeployment id =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    exact ⟨hadm, post_of_ok (delete_deployment_spec s id) hm ws rep rfl⟩
  | Dump =>
    obtain ⟨hadm, hm⟩ := manage_of h trivial hr
    rw [dump_eq] at hm
    simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨hadm, rfl, rfl⟩

/-- The write list of a management command with model lists fits in a vector
(`Usize.max` entries). Every successful run satisfies this (`fits_of_ok`), and
it is the only way the kernel can fail: see `transition_total`. -/
def Fits (s : Snapshot) : Command → Prop
  | .CreateTeam _ names => names.val.length + 1 < Usize.max
  | .CreateKey _ names => names.val.length + 1 < Usize.max
  | .DeleteTeam id => (s.team_models.val.filter (fun g => g.team = id)).length < Usize.max
  | .DeleteKey id => (s.key_models.val.filter (fun g => g.key = id)).length < Usize.max
  | .SetTeamModels id names => (s.team_models.val.filter (fun g => g.team = id)).length + names.val.length ≤ Usize.max
  | .SetKeyModels id names => (s.key_models.val.filter (fun g => g.key = id)).length + names.val.length ≤ Usize.max
  | _ => True

theorem total_manage {a : Principal} {s : Snapshot} {c : Command} (hc : IsManage c) (hm : manage a s c ⦃ _ => True ⦄) :
    ∃ r, transition a s c = ok r := by
  obtain ⟨b, hb⟩ := ok_of (is_admin_spec a s)
  obtain ⟨r, hr⟩ := ok_of hm
  cases c <;> simp only [IsManage] at hc <;> simp only [transition, hb] <;>
  · cases b
    · exact ⟨.Err .Forbidden, by simp⟩
    · exact ⟨r, by simpa using hr⟩

theorem triv {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : m ⦃ _ => True ⦄ :=
  WP.spec_mono h (by simp [WP.qimp])

instance : CloneLaw Model.Insts.CoreCloneClone := ⟨gateway_kernel.Schema.Model.clone_eq⟩

attribute [local step] list_models_loop_spec

/-- No input makes the kernel fail (panic, overflow, out-of-bounds index),
as long as the write list it builds fits in a vector. -/
theorem transition_total (a : Principal) (s : Snapshot) (c : Command) (hf : Fits s c) :
    ∃ r, transition a s c = ok r := by
  cases c with
  | Admit nm pt mt ex => exact ok_of (admit_spec a s nm pt mt ex)
  | Settle id pt ct st => exact ok_of (settle_spec a s id pt ct st)
  | Expire id => exact ok_of (expire_spec a s id)
  | KeyInfo id => exact ok_of (key_info_spec a s id)
  | TeamInfo id => exact ok_of (team_info_spec a s id)
  | ListModels =>
    simp only [transition]
    apply ok_of (P := fun _ => True)
    unfold list_models
    h5i_steps
  | Configure af cs ttl => exact total_manage trivial (by simp only [manage]; exact triv (configure_spec ..))
  | CreateTeam spec names => exact total_manage trivial (by simp only [manage]; exact triv (create_team_spec a s spec names hf))
  | UpdateTeam id p => exact total_manage trivial (by simp only [manage]; exact triv (update_team_spec ..))
  | DeleteTeam id => exact total_manage trivial (by simp only [manage]; exact triv (delete_team_spec s id hf))
  | SetTeamModels id names => exact total_manage trivial (by simp only [manage]; exact triv (set_team_models_spec s id names hf))
  | CreateKey spec names => exact total_manage trivial (by simp only [manage]; exact triv (create_key_spec a s spec names hf))
  | UpdateKey id p => exact total_manage trivial (by simp only [manage]; exact triv (update_key_spec ..))
  | DeleteKey id => exact total_manage trivial (by simp only [manage]; exact triv (delete_key_spec s id hf))
  | SetKeyModels id names => exact total_manage trivial (by simp only [manage]; exact triv (set_key_models_spec s id names hf))
  | ResetKeySpend id => exact total_manage trivial (by simp only [manage]; exact triv (reset_key_spend_spec ..))
  | UpsertDeployment nm spec => exact total_manage trivial (by simp only [manage]; exact triv (upsert_deployment_spec ..))
  | DeleteDeployment id => exact total_manage trivial (by simp only [manage]; exact triv (delete_deployment_spec ..))
  | Dump => exact total_manage trivial (by rw [dump_eq]; simp)

/-- Every successful run fits in a vector, so `transition_total`'s hypothesis
excludes only inputs on which the kernel cannot succeed. -/
theorem fits_of_ok {a : Principal} {s : Snapshot} {c : Command} {ws : alloc.vec.Vec Write} {rep : Reply}
    (h : transition a s c = ok (.Ok (ws, rep))) : Fits s c := by
  have hr : ∀ e, (core.result.Result.Ok (ws, rep) : core.result.Result _ Error) ≠ .Err e ∨ e ≠ .Forbidden :=
    fun e => .inl (by simp)
  cases c <;> simp only [Fits] <;> first
    | trivial
    | (obtain ⟨-, hm⟩ := manage_of h trivial hr; simp only [manage] at hm
       first | exact create_team_fits hm | exact create_key_fits hm | exact delete_team_fits hm | exact delete_key_fits hm | exact set_team_models_fits hm | exact set_key_models_fits hm)

end gateway_kernel.Commands
