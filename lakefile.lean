import Lake
open Lake DSL

package Clean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Clean where
  -- every file under `Clean/` that Lake builds uses the module system; warn if a new one does not
  requiresModuleSystem := true

lean_lib CleanTests where
  roots := #[`Clean.Test, `Clean.Specs.BLAKE3.ChunkProcessingTests]

lean_lib ToClean where
  requiresModuleSystem := true

lean_lib ToCleanTest where
  requiresModuleSystem := true

require "leanprover-community" / "mathlib" @ git "v4.33.1"
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git"@"v4.33.1"

lean_exe export_fibonacci_ensemble_rust where
  root := `Clean.Examples.FibonacciVm.EnsembleRust

lean_exe export_femtocairo_flat_air_rust where
  root := `Clean.Examples.FemtoCairo.FlatAirRust

lean_exe export_public_checks_rust where
  root := `ToCleanTest.PublicChecks
