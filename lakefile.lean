import Lake
open Lake DSL

package «spacetalk» where
  -- add any package configuration options here

require batteries from
  git "https://github.com/leanprover-community/batteries" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Spacetalk» where
  -- add any library configuration options here
