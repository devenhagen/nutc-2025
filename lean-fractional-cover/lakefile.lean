import Lake
open Lake DSL

package «fractional-cover-lean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

@[default_target]
lean_lib CoprimeAdjacent where
  globs := #[`CoprimeAdjacent.+]
