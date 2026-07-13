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
    `PrimeNumberTheorem.FirstOrderPerron,
    `PrimeNumberTheorem.FirstOrderLSeriesPerron,
    `PrimeNumberTheorem.FirstOrderExplicitFormula,
    `PrimeNumberTheorem.QuantitativeGoodHeight,
    `PrimeNumberTheorem.CentralHorizontalEdge,
    `PrimeNumberTheorem.CofinalExplicitFormula,
    `PrimeNumberTheorem.PerronTruncation,
    `PrimeNumberTheorem.VonMangoldtPerronTruncated,
    `PrimeNumberTheorem.PerronExplicitError,
    `PrimeNumberTheorem.LSeriesPerron,
    `PrimeNumberTheorem.CompletePerron,
    `PrimeNumberTheorem.SecondOrderExplicitFormula,
    `PrimeNumberTheorem.SafeSecondOrderExplicitFormula,
    `PrimeNumberTheorem.RightHorizontalEdge,
    `PrimeNumberTheorem.ExplicitFormulaAux,
    `ZeroFreeRegion,
    `ZeroFreeRegion.MeromorphicAux,
    `ZeroFreeRegion.PhragmenLindelofZeta,
    `ZeroFreeRegion.ShiftedJensen,
    `HardyTheorem.Phase1Aux,
    `HardyTheorem.AFE,
    `MathlibAux.RectangleResidue,
    `MathlibAux.BoundaryRectResidue,
    `PrimeNumberTheorem.ExplicitFormulaTruncated
  ]

require mathlib from "./vendor/mathlib"
