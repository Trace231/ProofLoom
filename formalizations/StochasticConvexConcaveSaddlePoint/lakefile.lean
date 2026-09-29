import Lake
open Lake DSL

package proofloom_artifact

-- The checked-in manifest pins the exact commit. Do not run lake update.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "stable"

lean_lib SOptLib where
  globs := #[.andSubmodules `SOptLib]

@[default_target]
lean_lib Algorithms where
  globs := #[.submodules `Algorithms]

