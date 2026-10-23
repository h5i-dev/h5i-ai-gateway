import Spec
/-!
# Committing a write set

The kernel's `apply` computes `Spec.applyAll`. `schema!` generated `apply`
and the table operations (`put`, `del`) with their lemmas in `Schema.lean`,
so only the dispatch over `Write` is left.
-/
open Aeneas Aeneas.Std Result gateway_kernel gateway_kernel.Spec gateway_kernel.Schema H5iAppLib

namespace gateway_kernel.Apply

theorem write_clone (w : Write) : Write.Insts.CoreCloneClone.clone w = ok w := by
  cases w <;> simp [Write.Insts.CoreCloneClone.clone, Settings.clone_eq, Team.clone_eq, Key.clone_eq,
    Model.clone_eq, Deployment.clone_eq, KeyModel.clone_eq, TeamModel.clone_eq, Usage.clone_eq,
    Reservation.clone_eq, SpendLog.Insts.CoreCloneClone.clone, core.clone.impls.CloneU64.clone, lift]

theorem apply_write_spec (s : Snapshot) (w : Write) (h : Snapshot.size s < Usize.max) :
    apply_write s w ⦃ s' => Snapshot.toSt s' = applyWrite (Snapshot.toSt s) w ∧
      Snapshot.size s' ≤ Snapshot.size s + 1 ⦄ := by
  unfold Snapshot.size at *
  unfold apply_write
  cases w <;> step* <;> simp_all [Snapshot.toSt, applyWrite, alloc.vec.Vec.length] <;>
    grind [upsert_length, List.length_filter_le]

/-- The kernel's `apply` computes `Spec.applyAll`, as long as no vector can
overflow (each write adds at most one row). -/
theorem apply_spec (s : Snapshot) (ws : alloc.vec.Vec Write) (h : Snapshot.size s + ws.length < Usize.max) :
    apply s ws ⦃ s' => Snapshot.toSt s' = applyAll (Snapshot.toSt s) ws.val ⦄ :=
  apply_spec' Snapshot.toSt applyWrite apply_write_spec write_clone s ws h

/-! ## Partial correctness

A successful `apply` computes `Spec.applyAll` whatever the sizes: a `put`
that needs to grow a full vector fails rather than returning something else.
`Commands.batch_spec` uses this, so the batch theorems need no size bound. -/

theorem loop_search_ok {α γ δ : Type} (l : List α) (P : α → Bool) (abs : γ → δ)
    (found : Nat → α → δ) (missing : δ)
    (body : Usize → Result (ControlFlow Usize γ))
    (hstep : ∀ (i : Usize) r, i.val ≤ l.length → body i = ok r → SearchStep l P abs found missing i r)
    (i : Usize) (hi : i.val ≤ l.length) (y : γ) (h : loop body i = ok y) :
    abs y = searchFrom l P found missing i.val := by
  refine H5iAppLib.loop_ok body (fun j => j.val ≤ l.length ∧
      searchFrom l P found missing i.val = searchFrom l P found missing j.val)
    (fun y => abs y = searchFrom l P found missing i.val) (fun j => l.length - j.val) ?_ i y ⟨hi, rfl⟩ h
  rintro j r ⟨hj, heq⟩ hr
  have h := hstep j r hj hr
  cases r with
  | done y =>
    rcases h with ⟨hlt, hp, hy⟩ | ⟨hle, hy⟩
    · simp only; rw [hy, heq, searchFrom_found hlt hp]
    · simp only; rw [hy, heq, searchFrom_end hle]
  | cont k =>
    obtain ⟨hlt, hp, hk⟩ := h
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    rw [heq, searchFrom_skip hlt hp, hk]

theorem push_ok {α : Type} {v v' : alloc.vec.Vec α} {x : α} (h : v.push x = ok v') : v'.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · simp at h; subst h; simp
  · simp at h

theorem index_slice_ok' {α} {v : alloc.vec.Vec α} {i : Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    ∃ h : i.val < v.val.length, v.val[i.val] = x := by
  have h1 := vec_index_slice_ok_get? h
  have hlt : i.val < v.val.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h1; cases h1
  exact ⟨hlt, by rw [List.getElem?_eq_getElem hlt] at h1; exact Option.some.inj h1⟩

theorem index_mut_slice_ok {α} {v : alloc.vec.Vec α} {i : Usize} {p : α × (α → alloc.vec.Vec α)}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok p) :
    i.val < v.val.length ∧ p.2 = v.set i := by
  rw [alloc.vec.Vec.index_mut_slice_index] at h
  unfold alloc.vec.Vec.index_mut_usize at h
  obtain ⟨y, hy, h⟩ := bind_eq_ok.1 h
  simp only [ok.injEq] at h; subst h
  exact ⟨(vec_index_ok hy).1, rfl⟩

set_option hygiene false in
macro "put_ok_tac " b:ident : tactic => `(tactic| (
  intro j r hj hr
  unfold $b at hr
  h5i_invert hr
  all_goals first
    | (right; exact ⟨by scalar_tac, push_ok ‹alloc.vec.Vec.push _ _ = ok _›⟩)
    | (obtain ⟨hlt, hget⟩ := index_slice_ok' ‹alloc.vec.Vec.index _ _ _ = ok _›
       subst hget
       obtain ⟨-, hp⟩ := index_mut_slice_ok ‹alloc.vec.Vec.index_mut _ _ _ = ok _›
       rcases hx : ‹_ × (_ → alloc.vec.Vec _)› with ⟨p1, p2⟩
       subst hx
       simp only at hp; subst hp
       simp at hr; subst hr


       left
       exact ⟨hlt, by simp_all, by simp [alloc.vec.Vec.set]⟩)
    | (obtain ⟨hlt, hget⟩ := index_slice_ok' ‹alloc.vec.Vec.index _ _ _ = ok _›
       subst hget
       try (simp at hr; subst hr)
       exact ⟨hlt, by simp_all, add_ok_val ‹_ + 1#usize = ok _›⟩)))

theorem Team.put_ok {v v' : alloc.vec.Vec Team} {x : Team} (h : Team.put v x = ok v') :
    v'.val = upsert (fun y => y.id) x v.val := by
  unfold Team.put Team.put_loop at h
  have := loop_search_ok v.val (fun q => decide (q.id = x.id))
    (fun y : alloc.vec.Vec Team => y.val) (fun j _ => v.val.set j x) (v.val ++ [x]) _ ?_ 0#usize (by simp) _ h
  · rw [this, show ((0#usize : Usize) : Nat) = 0 from rfl]
    exact upsert_loop_result _ x _ 0 (Nat.zero_le _) (by simp)
  · put_ok_tac Team.put_loop.body

theorem Key.put_ok {v v' : alloc.vec.Vec Key} {x : Key} (h : Key.put v x = ok v') :
    v'.val = upsert (fun y => y.id) x v.val := by
  unfold Key.put Key.put_loop at h
  have := loop_search_ok v.val (fun q => decide (q.id = x.id))
    (fun y : alloc.vec.Vec Key => y.val) (fun j _ => v.val.set j x) (v.val ++ [x]) _ ?_ 0#usize (by simp) _ h
  · rw [this, show ((0#usize : Usize) : Nat) = 0 from rfl]
    exact upsert_loop_result _ x _ 0 (Nat.zero_le _) (by simp)
  · put_ok_tac Key.put_loop.body

theorem Model.put_ok {v v' : alloc.vec.Vec Model} {x : Model} (h : Model.put v x = ok v') :
    v'.val = upsert (fun y => y.id) x v.val := by
  unfold Model.put Model.put_loop at h
  have := loop_search_ok v.val (fun q => decide (q.id = x.id))
    (fun y : alloc.vec.Vec Model => y.val) (fun j _ => v.val.set j x) (v.val ++ [x]) _ ?_ 0#usize (by simp) _ h
  · rw [this, show ((0#usize : Usize) : Nat) = 0 from rfl]
    exact upsert_loop_result _ x _ 0 (Nat.zero_le _) (by simp)
  · put_ok_tac Model.put_loop.body

theorem Deployment.put_ok {v v' : alloc.vec.Vec Deployment} {x : Deployment} (h : Deployment.put v x = ok v') :
    v'.val = upsert (fun y => y.id) x v.val := by
  unfold Deployment.put Deployment.put_loop at h
  have := loop_search_ok v.val (fun q => decide (q.id = x.id))
    (fun y : alloc.vec.Vec Deployment => y.val) (fun j _ => v.val.set j x) (v.val ++ [x]) _ ?_ 0#usize (by simp) _ h
  · rw [this, show ((0#usize : Usize) : Nat) = 0 from rfl]
    exact upsert_loop_result _ x _ 0 (Nat.zero_le _) (by simp)
  · put_ok_tac Deployment.put_loop.body

theorem KeyModel.put_ok {v v' : alloc.vec.Vec KeyModel} {x : KeyModel} (h : KeyModel.put v x = ok v') :
    v'.val = upsert (fun y => (y.key, y.model)) x v.val := by
  unfold KeyModel.put KeyModel.put_loop at h
  have := loop_search_ok v.val (fun q => decide ((q.key, q.model) = (x.key, x.model)))
    (fun y : alloc.vec.Vec KeyModel => y.val) (fun j _ => v.val.set j x) (v.val ++ [x]) _ ?_ 0#usize (by simp) _ h
  · rw [this, show ((0#usize : Usize) : Nat) = 0 from rfl]
    exact upsert_loop_result _ x _ 0 (Nat.zero_le _) (by simp)
  · put_ok_tac KeyModel.put_loop.body

theorem TeamModel.put_ok {v v' : alloc.vec.Vec TeamModel} {x : TeamModel} (h : TeamModel.put v x = ok v') :
    v'.val = upsert (fun y => (y.team, y.model)) x v.val := by
  unfold TeamModel.put TeamModel.put_loop at h
  have := loop_search_ok v.val (fun q => decide ((q.team, q.model) = (x.team, x.model)))
    (fun y : alloc.vec.Vec TeamModel => y.val) (fun j _ => v.val.set j x) (v.val ++ [x]) _ ?_ 0#usize (by simp) _ h
  · rw [this, show ((0#usize : Usize) : Nat) = 0 from rfl]
    exact upsert_loop_result _ x _ 0 (Nat.zero_le _) (by simp)
  · put_ok_tac TeamModel.put_loop.body

theorem Usage.put_ok {v v' : alloc.vec.Vec Usage} {x : Usage} (h : Usage.put v x = ok v') :
    v'.val = upsert (fun y => (y.scope, y.id)) x v.val := by
  unfold Usage.put Usage.put_loop at h
  have := loop_search_ok v.val (fun q => decide ((q.scope, q.id) = (x.scope, x.id)))
    (fun y : alloc.vec.Vec Usage => y.val) (fun j _ => v.val.set j x) (v.val ++ [x]) _ ?_ 0#usize (by simp) _ h
  · rw [this, show ((0#usize : Usize) : Nat) = 0 from rfl]
    exact upsert_loop_result _ x _ 0 (Nat.zero_le _) (by simp)
  · put_ok_tac Usage.put_loop.body

theorem Reservation.put_ok {v v' : alloc.vec.Vec Reservation} {x : Reservation} (h : Reservation.put v x = ok v') :
    v'.val = upsert (fun y => y.id) x v.val := by
  unfold Reservation.put Reservation.put_loop at h
  have := loop_search_ok v.val (fun q => decide (q.id = x.id))
    (fun y : alloc.vec.Vec Reservation => y.val) (fun j _ => v.val.set j x) (v.val ++ [x]) _ ?_ 0#usize (by simp) _ h
  · rw [this, show ((0#usize : Usize) : Nat) = 0 from rfl]
    exact upsert_loop_result _ x _ 0 (Nat.zero_le _) (by simp)
  · put_ok_tac Reservation.put_loop.body

theorem apply_write_ok {s s' : Snapshot} {w : Write} (h : apply_write s w = ok s') :
    Snapshot.toSt s' = applyWrite (Snapshot.toSt s) w := by
  unfold apply_write at h
  cases w with
  | SetSettings x => simp only [ok.injEq] at h; subst h; rfl
  | PutTeam x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := Team.put_ok hv
    simp [Snapshot.toSt, applyWrite, this]
  | DelTeam x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := post_of_ok (Team.del_spec _ _) hv
    simp [Snapshot.toSt, applyWrite, this]
  | PutKey x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := Key.put_ok hv
    simp [Snapshot.toSt, applyWrite, this]
  | DelKey x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := post_of_ok (Key.del_spec _ _) hv
    simp [Snapshot.toSt, applyWrite, this]
  | PutModel x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := Model.put_ok hv
    simp [Snapshot.toSt, applyWrite, this]
  | PutDeployment x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := Deployment.put_ok hv
    simp [Snapshot.toSt, applyWrite, this]
  | DelDeployment x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := post_of_ok (Deployment.del_spec _ _) hv
    simp [Snapshot.toSt, applyWrite, this]
  | PutKeyModel x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := KeyModel.put_ok hv
    simp [Snapshot.toSt, applyWrite, this]
  | DelKeyModel x y =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := post_of_ok (KeyModel.del_spec _ _ _) hv
    simp [Snapshot.toSt, applyWrite, this]
  | PutTeamModel x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := TeamModel.put_ok hv
    simp [Snapshot.toSt, applyWrite, this]
  | DelTeamModel x y =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := post_of_ok (TeamModel.del_spec _ _ _) hv
    simp [Snapshot.toSt, applyWrite, this]
  | PutUsage x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := Usage.put_ok hv
    simp [Snapshot.toSt, applyWrite, this]
  | PutReservation x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := Reservation.put_ok hv
    simp [Snapshot.toSt, applyWrite, this]
  | DelReservation x =>
    obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    have := post_of_ok (Reservation.del_spec _ _) hv
    simp [Snapshot.toSt, applyWrite, this]
  | Emit x => simp only [ok.injEq] at h; subst h; rfl

/-- Partial correctness of `apply`: whenever it returns, it returned
`Spec.applyAll` of the writes (no size bound needed). -/
theorem apply_ok {s s' : Snapshot} {ws : alloc.vec.Vec Write} (h : apply s ws = ok s') :
    Snapshot.toSt s' = applyAll (Snapshot.toSt s) ws.val := by
  unfold apply apply_loop at h
  rw [Snapshot.clone_eq] at h
  simp only [bind_ok] at h
  refine loop_idx_ok _ (fun x => x.2) ws.val.length
    (fun x => Snapshot.toSt x.1 = applyAll (Snapshot.toSt s) (ws.val.take x.2.val))
    (fun y => Snapshot.toSt y = applyAll (Snapshot.toSt s) ws.val) ?_ _ _ (by simp [applyAll]) (by simp) h
  rintro ⟨t, i⟩ r hI hi hr
  simp only at hI hi hr
  unfold apply_loop.body at hr
  h5i_invert hr
  · obtain ⟨hlt, rfl⟩ := index_slice_ok' hw
    rw [write_clone] at hw1; simp only [ok.injEq] at hw1; subst hw1
    have hi2' := add_ok_val hi2
    refine ⟨?_, by simp [hi2'], by simp [hi2']; omega⟩
    rw [apply_write_ok hs1, hI, hi2', show (1#usize : Usize).val = 1 from rfl, List.take_add_one,
      List.getElem?_eq_getElem hlt]
    simp only [applyAll, List.foldl_append, Option.toList, List.foldl_cons, List.foldl_nil]
  · simp only
    rw [hI, List.take_of_length_le (by scalar_tac)]

end gateway_kernel.Apply
