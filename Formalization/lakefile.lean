import Lake
open Lake DSL



package «utils» where

@[default_target]
lean_lib «utils» where
  srcDir := "."
set_option pp.notation true
set_option pp.unicode true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.foralls true

require REPL from git "https://github.com/leanprover-community/repl" @ "v4.24.0"

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

