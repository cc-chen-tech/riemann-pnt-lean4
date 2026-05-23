import Lake
open Lake DSL

package «riemann-pnt» where
  version := v!"0.1.0"

@[default_target]
lean_lib RiemannPNT where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
