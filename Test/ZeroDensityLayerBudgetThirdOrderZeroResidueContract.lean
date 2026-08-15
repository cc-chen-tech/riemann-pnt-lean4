import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroResidue

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example (x : ℝ) (z : ℂ) :
    thirdOrderZeroCore x z =
      -logDeriv riemannZeta z * (x : ℂ) ^ z := rfl

example (x : ℝ) :
    thirdOrderZeroCore x 0 =
      -deriv riemannZeta 0 / riemannZeta 0 :=
  thirdOrderZeroCore_zero x

example {x : ℝ} (hx : 0 < x) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      (fun z : ℂ => thirdOrderExplicitFormulaIntegrand x z) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z : ℂ =>
          G z +
            z⁻¹ * (iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2) +
            z⁻¹ ^ 2 * deriv (thirdOrderZeroCore x) 0 +
            z⁻¹ ^ 3 * (-deriv riemannZeta 0 / riemannZeta 0)) :=
  exists_analyticAt_eventuallyEq_thirdOrderExplicitFormulaIntegrand_zeroPrincipalParts
    hx

end PrimeNumberTheorem.ExplicitFormulaResidues
