import Spec
/-!
# What the store holds

The server stores a write set by running the plan of `sql_writes`, and loads
rows through `decode`. `H5iAppLib.Store` proves, for any schema, that the
database then holds the encoding of the state `applyAll` computes. This file
gives the encoding and table writes; spend logs go to the outbox, not a table.
-/
open Aeneas Aeneas.Std Result gateway_kernel gateway_kernel.Spec gateway_kernel.Schema H5iAppLib H5iAppLib.Sql H5iAppLib.Store

namespace gateway_kernel.Storage

/-- A state's rows, table by table. -/
def enc (s : St) : Tables Val
  | 0 => [Settings.row s.settings]
  | 1 => s.teams.map Team.row
  | 2 => s.keys.map Key.row
  | 3 => s.models.map Model.row
  | 4 => s.deployments.map Deployment.row
  | 5 => s.keyModels.map KeyModel.row
  | 6 => s.teamModels.map TeamModel.row
  | 7 => s.usage.map Usage.row
  | 8 => s.reservations.map Reservation.row
  | _ => []

/-- The table writes of one write. -/
def sqlA : Write → List (AWrite Val)
  | .SetSettings x => [Settings.putA x]
  | .PutTeam x => [Team.putA x]
  | .DelTeam id => [Team.delA id]
  | .PutKey x => [Key.putA x]
  | .DelKey id => [Key.delA id]
  | .PutModel x => [Model.putA x]
  | .PutDeployment x => [Deployment.putA x]
  | .DelDeployment id => [Deployment.delA id]
  | .PutKeyModel x => [KeyModel.putA x]
  | .DelKeyModel k m => [KeyModel.delA k m]
  | .PutTeamModel x => [TeamModel.putA x]
  | .DelTeamModel t m => [TeamModel.delA t m]
  | .PutUsage x => [Usage.putA x]
  | .PutReservation x => [Reservation.putA x]
  | .DelReservation id => [Reservation.delA id]
  | .Emit _ => []

set_option maxHeartbeats 400000 in
def app : App St Write Val where
  kl := kl
  enc := enc
  sql := sqlA
  step := applyWrite
  init := init
  IsRow := IsRow
  enc_step := by schema_step [enc, sqlA, applyWrite]
  sql_ok := by schema_ok [sqlA]
  init_ok := by schema_init [enc, init]
  init_rows := by schema_rows [enc, init]

theorem fits : Fits app Snapshot.toSt where
  kl := rfl
  rows := rfl
  enc s := by funext t; cases_table t <;> rfl
  init := by funext t; cases_table t <;> rfl
  nil s t h := by cases_table t <;> first | omega | rfl

theorem sql_fits : SqlFits app := by
  intro w out h
  unfold sql_write; cases w <;> simp only [app, sqlA, List.length_singleton] at h ⊢ <;> step* <;> simp_all

/-- The store holds what `apply` computes: the rows of the state `applyAll`
gives for its commits, and a load decodes to that state, up to row order. -/
theorem stored {db : Db Val} {s : St} (h : Served app Snapshot.toSt db s) :
    app.Holds db (enc s) ∧
      ∀ r, Lists kl db (Rows.tabs r) → decode r ⦃ o => ∃ snap, o = some snap ∧ app.Equiv (Snapshot.toSt snap) s ⦄ :=
  Schema.stored fits sql_fits h

/-! ## On PostgreSQL

`PgServed` is one tenant's history on a shared database (other tenants'
statements may run in between), with SQL from the extracted `h5i_app_pgsql`
run on the model in `H5iAppLib.Pg`. -/

/-- Write sets the kernel returns for a command it accepts, at any time. -/
def Accepted (snap : Snapshot) (ws : alloc.vec.Vec Write) : Prop :=
  ∃ a c r, transition a snap c = .ok (.Ok (ws, r))

/-- `stored` on PostgreSQL: the tenant's rows are those of the state its
commits computed with `Spec.applyAll`, and a load decodes to that state, up to
row order. -/
theorem pg_stored {ts : List Pg.Tab} {tv : Val} {Step : Snapshot → alloc.vec.Vec Write → Prop}
    (hv : Pg.Valid ts) (htv : valKind tv = some .int) (hkl : Pg.klOf ts = kl) (hlen : ts.length = 9)
    {db : Pg.PgDb Val} {s : St} (h : PgServed app Snapshot.toSt ts tv Step db s) :
    app.Holds (Pg.view ts tv db) (enc s) ∧
      ∀ r, Loads ts tv db r → decode r ⦃ o => ∃ snap, o = some snap ∧ app.Equiv (Snapshot.toSt snap) s ⦄ := by
  obtain ⟨hm, hS⟩ := pg_served sql_fits fits hv htv hkl hlen h
  refine ⟨(stored hS).1, fun r hr => (stored hS).2 r ?_⟩
  rw [← hkl]
  exact Pg.lists_of_selects valKind hv htv hm _ (fun t ht => Rows.tabs_nil _ t (hlen ▸ ht))
    (fun t ht => hr t (hlen ▸ ht))

/-- A property of states that holds initially, survives reordering rows, and
is kept by every write set the kernel accepts holds on PostgreSQL, and on
every snapshot a later load decodes. -/
theorem db_inv {ts : List Pg.Tab} {tv : Val} (hv : Pg.Valid ts) (htv : valKind tv = some .int)
    (hkl : Pg.klOf ts = kl) (hlen : ts.length = 9) (Inv : St → Prop) (hinit : Inv init)
    (hequiv : ∀ snap s', app.Equiv (Snapshot.toSt snap) s' → Inv s' → Inv (Snapshot.toSt snap))
    (hstep : ∀ snap ws, Accepted snap ws → Inv (Snapshot.toSt snap) → Inv (applyAll (Snapshot.toSt snap) ws.val))
    {db : Pg.PgDb Val} {s : St} (h : PgServed app Snapshot.toSt ts tv Accepted db s) :
    Inv s ∧ ∀ r, Loads ts tv db r → decode r ⦃ o => ∃ snap, o = some snap ∧ Inv (Snapshot.toSt snap) ⦄ :=
  pg_loaded_inv sql_fits fits hv htv hkl hlen Inv hinit hequiv hstep h

end gateway_kernel.Storage
