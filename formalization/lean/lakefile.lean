import Lake
open Lake DSL

package «adelic_bsd» where
  -- Add package configuration options here

lean_lib «AdelicBSD» where
  -- Add library configuration options here

@[default_target]
lean_exe «adelic_bsd» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
