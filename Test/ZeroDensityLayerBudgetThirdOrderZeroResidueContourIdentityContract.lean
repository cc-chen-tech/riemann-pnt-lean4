import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroResidueContourIdentity

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
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
      residue 0 = iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2 ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      ∫ w in -W..W,
          thirdOrderExplicitFormulaIntegrand x
            ((c : ℂ) + 2 * Real.pi * w * I) =
        ∑ p ∈ poles, residue p - thirdOrderContourRemainder x a c W :=
  exists_scaledRightIntegral_eq_explicitZeroPoleResidue_sum_sub_thirdOrderContourRemainder
    hx ha hc hW hboundary

end PrimeNumberTheorem.ExplicitFormulaResidues
