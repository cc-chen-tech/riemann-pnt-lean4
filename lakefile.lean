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
    `PrimeNumberTheorem.GlobalZeroCount,
    `PrimeNumberTheorem.CentralHorizontalEdge,
    `PrimeNumberTheorem.CofinalExplicitFormula,
    `PrimeNumberTheorem.ExplicitFormulaAllHeights,
    `PrimeNumberTheorem.NontrivialZeroMultiplicity,
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
    `PrimeNumberTheorem.ExplicitFormulaTruncated,
    `Test.ExplicitFormulaAllHeightsContract,
    `Test.ExplicitFormulaBoundedGapContract,
    `Test.CofinalExplicitFormulaContract,
    `Test.CofinalWeightedApproxContract,
    `Test.CompleteHorizontalRateContract,
    `Test.ContourRemainderRateContract,
    `Test.ExplicitFormulaMultiplicityContract,
    `Test.ExplicitFormulaTruncatedUniformContract,
    `Test.FarLeftHorizontalRateContract,
    `Test.FiniteZeroMultiplicityMassContract,
    `Test.FirstOrderExplicitFormulaRateContract,
    `Test.FirstOrderPerronRateContract,
    `Test.GlobalZeroCountContract,
    `Test.LocalZeroContributionBoundContract,
    `Test.LocalZeroMultiplicityBoundContract,
    `Test.MultiplicityAxiomAudit,
    `Test.NontrivialZeroContributionBoundContract,
    `Test.NontrivialZeroDivisorMultiplicityContract,
    `Test.NontrivialZeroMultiplicitySymmetryContract,
    `Test.SelectedHeightTruncatedExplicitFormulaRateContract
  ]

require mathlib from "./vendor/mathlib"
