import HardyTheorem.ConreyCoprimeMobiusResidue

open Complex MeasureTheory Metric
open scoped BigOperators

namespace HardyTheorem

-- Uniform radius and error constant are selected BEFORE d and the shifts.
-- Both functions are literal: there is no assumed analytic surrogate,
-- no pole-residue hypothesis, and no assumed Euler-integrand identity.
example : ∃ r C : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ 0 < C ∧ ∀ d : ℕ,
    let E : ℂ → ℂ := fun z =>
      (∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹
    let W : ℂ → ℂ := fun z =>
      z * (ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + z))⁻¹ * E z
    AnalyticOnNhd ℂ W (closedBall 0 r) ∧ W 0 = 0 ∧ deriv W 0 = E 0 ∧
    (∀ z : ℂ, ‖z‖ ≤ r →
      ‖W z - z * E z‖ ≤ C * ‖z‖ ^ 2 * ‖E z‖) ∧
    (∀ z : ℂ, ‖z‖ ≤ r → z ≠ 0 →
      W z = (riemannZeta (1 + z) *
        ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹) ∧
    ∀ (α : ℂ) (X ρ : ℝ), 0 < X → ‖α‖ < ρ → ‖α‖ + ρ ≤ r →
      CircleIntegrable (fun w : ℂ => (X : ℂ) ^ w *
        (riemannZeta (1 + α + w) *
          ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
        (1 / w ^ 2)) 0 ρ ∧
      (∮ w in C(0, ρ), (X : ℂ) ^ w *
        (riemannZeta (1 + α + w) *
          ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
        (1 / w ^ 2)) =
      (2 * Real.pi * I) * ((Real.log X : ℂ) * W α + deriv W α) :=
  exists_conrey_coprime_mobius_local_residue

#print axioms exists_conrey_coprime_mobius_local_residue
#print axioms conreyCoprimeMobiusRegularized_eq_euler

end HardyTheorem
