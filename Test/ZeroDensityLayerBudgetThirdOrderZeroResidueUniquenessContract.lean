import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroResidueUniqueness

open Complex Set Filter Topology

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K)
    (hKnhds : K ∈ 𝓝 (0 : ℂ)) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ)
        (quadratic cubic : ℂ) (G : ℂ → ℂ),
      0 ∈ poles ∧
      (∀ p ∈ poles, p = 0 ∨ p ∈ K) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 0 then residue 0
        else if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      residue 0 = iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2 ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      AnalyticOnNhd ℂ G K ∧
      ∀ z ∈ K, z ∉ poles →
        thirdOrderExplicitFormulaIntegrand x z =
          G z + ∑ p ∈ poles, (z - p)⁻¹ * residue p +
            quadratic * z⁻¹ ^ 2 + cubic * z⁻¹ ^ 3 :=
  exists_thirdOrderExplicitFormula_zeroPole_regularization_explicit_zero_residue
    hx hK hKnhds

end PrimeNumberTheorem.ExplicitFormulaResidues
