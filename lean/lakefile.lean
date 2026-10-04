import Lake
open Lake DSL

package «jacobian-diagnostics» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

@[default_target] lean_lib «R1CSChecker» where
@[default_target] lean_lib «AffineLineCert» where
@[default_target] lean_lib «RedundancyCert» where
@[default_target] lean_lib «Multiplicity» where
@[default_target] lean_lib «GnarkCheckDemo» where
@[default_target] lean_lib «GnarkFullDemo» where
