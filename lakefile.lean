import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4"

package «natural-number-game» where
  -- add package configuration options here

lean_lib «NaturalNumberGame» where
  -- add library configuration options here

@[default_target]
lean_exe «natural-number-game» where
  root := `Main
