import Lake
open Lake DSL

-- Pinned to the Aeneas commit `h5i app` extracts with (`h5i app doctor`).
require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "b86120db3183b0107eb5f2637b11c424cd06ef1c" / "backends/lean"

-- h5i-app's lemmas and tactics. The h5i tag v0.5.1 carries the proofs that
-- ship with h5i-app-core 0.1.3 on crates.io.
require h5i_app_lib from git
  "https://github.com/h5i-dev/h5i" @ "v0.5.1" / "crates/h5i-app-core/proofs"

package gateway_proofs

-- The extracted kernel (`h5i app extract`). Do not edit.
lean_lib Generated where
  srcDir := "generated"
  roots := #[`GatewayKernel, `Schema]

-- Hand-written specification and proofs.
@[default_target] lean_lib Proofs where
  roots := #[`Spec]
