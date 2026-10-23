import Spec
import H5iAppLib.ReadOnly
/-!
# Read-only commands

`Dump`, `KeyInfo`, `TeamInfo` and `ListModels` are the commands `read_only`
marks; every accepted run of one returns an empty write set, so the server
may run them in a read-only transaction.
-/
open Aeneas Aeneas.Std Result gateway_kernel

namespace gateway_kernel.ReadOnly

theorem bind_ok_inv {α β : Type} {m : Result α} {f : α → Result β} {y : β}
    (h : (m >>= f) = ok y) : ∃ x, m = ok x ∧ f x = ok y := by
  cases m <;> simp_all

/-- Every accepted read-only command writes nothing, for all actors and snapshots. -/
theorem sound : H5iAppLib.ReadOnly.Sound read_only transition (fun ws : alloc.vec.Vec Write => ws.val) := by
  intro a s c ws r hro h
  cases c <;> simp [read_only] at hro <;>
    simp only [transition, manage, key_info, team_info, list_models] at h <;>
    repeat' (first
      | (obtain ⟨_, _, h⟩ := bind_ok_inv h)
      | (split at h))
  all_goals simp only [ok.injEq, reduceCtorEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  all_goals (obtain ⟨rfl, -⟩ := h; rfl)

end gateway_kernel.ReadOnly
