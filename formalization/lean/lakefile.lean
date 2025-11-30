import Lake
open Lake DSL

package «adelic_bsd» where
  -- Add package configuration options here

lean_lib «AdelicBSD» where
  -- Add library configuration options here

lean_lib «RiemannAdelic» where
  -- Riemann-Adelic formalization library

lean_lib «BSD» where
  -- BSD parity and Selmer formalization library

@[default_target]
lean_exe «adelic_bsd» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
