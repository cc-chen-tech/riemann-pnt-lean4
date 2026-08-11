import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroPoleRegularization

open Complex Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K)
    (h0K : 0 ∈ K) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ)
        (quadratic cubic : ℂ) (G : ℂ → ℂ),
      0 ∈ poles ∧
      (∀ p ∈ poles, p = 0 ∨ p ∈ K) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 0 then residue 0
        else if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      AnalyticOnNhd ℂ G K ∧
      ∀ z ∈ K, z ∉ poles →
        thirdOrderExplicitFormulaIntegrand x z =
          G z + ∑ p ∈ poles, (z - p)⁻¹ * residue p +
            quadratic * z⁻¹ ^ 2 + cubic * z⁻¹ ^ 3 :=
  exists_thirdOrderExplicitFormula_zeroPole_regularization hx hK h0K

end PrimeNumberTheorem.ExplicitFormulaResidues
