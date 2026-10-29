import Lake

open Lake DSL

package «cbmd-b5-m3-formal» where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Exact mathlib revision preserved by the CBMD Batch 4 compile envelope.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib OAI where
  srcDir := "lean"
  globs := #[`OAI.+]
