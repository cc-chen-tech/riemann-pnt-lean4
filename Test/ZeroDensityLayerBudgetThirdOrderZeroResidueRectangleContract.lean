import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroResidueRectangle

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ uIcc (-W) W,
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ) (cubic : ℂ),
      0 ∈ poles ∧
      (∀ p ∈ poles,
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 0 then residue 0
        else if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      residue 0 = iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2 ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      MathlibAux.boundaryRectIntegral
          (thirdOrderExplicitFormulaIntegrand x) a c (-W) W =
        2 * Real.pi * I * ∑ p ∈ poles, residue p :=
  exists_boundaryRectIntegral_thirdOrderExplicitFormulaIntegrand_eq_residue_sum_explicit_zeroPole
    hx ha hc hW hboundary

end PrimeNumberTheorem.ExplicitFormulaResidues
