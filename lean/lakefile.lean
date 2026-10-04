import Lake
open Lake DSL

package «zk-soundness-reductions» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

@[default_target]
lean_lib «ZkReductions» where
