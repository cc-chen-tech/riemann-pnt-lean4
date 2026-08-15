import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroResidueLSeriesBridge

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem

example {x a c W : ℝ} (hx : 0 < x) (ha : a < 0)
    (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ
        uIcc (-(2 * Real.pi * W)) (2 * Real.pi * W),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ) (cubic : ℂ),
      0 ∈ poles ∧
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 0 then residue 0
        else if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      residue 0 = iteratedDeriv 2
        (ExplicitFormulaResidues.thirdOrderZeroCore x) 0 / 2 ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      ‖∑ p ∈ poles, residue p -
          ExplicitFormulaResidues.thirdOrderContourRemainder x a c W -
          (secondSmoothedChebyshevPsi x : ℂ)‖ ≤
        ∑' n : ℕ, vonMangoldt n * (x / n) ^ c /
          (8 * Real.pi ^ 3 * W ^ 2) :=
  exists_thirdOrderExplicitZeroPoleFormula_secondSmoothedPsi_error_le
    hx ha hc hW hboundary

end PrimeNumberTheorem
