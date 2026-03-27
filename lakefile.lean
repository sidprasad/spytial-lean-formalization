import Lake
open Lake DSL

package cndsemantics

@[default_target]
lean_lib Main

require mathlib from
  git "https://github.com/leanprover-community/mathlib4" @ "master"

require batteries from
  git "https://github.com/leanprover-community/batteries" @ "main"
