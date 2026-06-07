import Lake
open Lake DSL

package «riemann-pnt» where
  version := v!"0.1.0"

@[default_target]
lean_lib RiemannPNT where
  roots := #[
    `RiemannPNT,
    `RiemannExplorer,
    `RiemannExplorer.Conrey40,
    `GammaResidue,
    `HardyTheorem,
    `EulerAndLfunctions,
    `PrimeNumberTheorem,
    `ZeroFreeRegion
  ]

require mathlib from "./vendor/mathlib"
