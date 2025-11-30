import Lake
open Lake DSL

package «adelic_bsd» where
  -- Add package configuration options here

lean_lib «AdelicBSD» where
  -- Add library configuration options here

lean_lib «RiemannAdelic» where
  -- Riemann-Adelic formalization library

lean_lib «RationalStructures» where
  -- BSD Rational Structures library for dR vs PT comparison
  srcDir := "rational_structures"

@[default_target]
lean_exe «adelic_bsd» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
