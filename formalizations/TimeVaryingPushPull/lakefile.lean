import Lake
open Lake DSL
package proofloom_artifact
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "8a178386ffc0f5fef0b77738bb5449d50efeea95"
lean_lib SOptLib
@[default_target]
lean_lib Algorithms where
  roots := #[`Algorithms.Unverified.TimeVaryingPushPull]
  leanOptions := #[⟨`maxHeartbeats, 1000000⟩]
