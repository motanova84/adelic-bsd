import Lake
open Lake DSL

package «bsd_experiment» where
  -- BSD Experimental Formalization Package
  -- Formalizes numerical BSD validation results in Lean 4

lean_lib «BSDExperiment» where
  -- Main library containing curve formalizations
  srcDir := "bsd_experiment"
  roots := #[`Main, `Common, `E5077a1, `E_11a1, `E_37a1, `E_389a1, `axioms_status]

lean_lib «MathlibIntegration» where
  -- Integration with Mathlib structures
  srcDir := "mathlib_integration"

@[default_target]
lean_exe «bsd_experiment» where
  root := `BSDExperiment.Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
