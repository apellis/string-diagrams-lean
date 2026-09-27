import Lake
open Lake DSL

package StringDiagrams where
  moreLeanArgs := #["-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib StringDiagrams where
  globs := #[.andSubmodules `StringDiagrams]
