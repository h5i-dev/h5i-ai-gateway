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

end gateway_kernel.Apply
