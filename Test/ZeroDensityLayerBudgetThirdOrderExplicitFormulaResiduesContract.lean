import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderExplicitFormulaResidues

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example
    {K : Set ℂ} {f g : ℂ → ℂ} (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hzero : ∀ z ∈ K, z ≠ 0)
    (hpolesZero : ∀ p ∈ poles, p ≠ 0)
    (hg : AnalyticOnNhd ℂ g K)
    (heq : ∀ z ∈ K, z ∉ poles →
      f z = g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p) :
    ∃ g' : ℂ → ℂ,
      AnalyticOnNhd ℂ g' K ∧
      ∀ z ∈ K, z ∉ poles →
        f z / z = g' z +
          ∑ p ∈ poles, (z - p)⁻¹ * (residue p / p) :=
  exists_analyticOnNhd_div_id_regularization poles residue
    hzero hpolesZero hg heq

example (x : ℝ) (s : ℂ) :
    thirdOrderExplicitFormulaIntegrand x s =
      explicitFormulaIntegrand x s / s ^ 2 := rfl

example (x : ℝ) (s : ℂ) :
    thirdOrderExplicitFormulaIntegrand x s =
      secondOrderExplicitFormulaIntegrand x s / s :=
  thirdOrderExplicitFormulaIntegrand_eq_secondOrder_div x s

example {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z ∈ K, z ≠ 0) :
    ∃ (poles : Finset ℂ) (residue g : ℂ → ℂ),
      (∀ p ∈ poles, p ∈ K ∧ p ≠ 0) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p) ∧
      AnalyticOnNhd ℂ g K ∧
      ∀ z ∈ K, z ∉ poles →
        explicitFormulaIntegrand x z =
          g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p :=
  exists_explicitFormula_regularization_without_zero hx hK hzero

example {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z ∈ K, z ≠ 0) :
    ∃ (poles : Finset ℂ) (residue g : ℂ → ℂ),
      (∀ p ∈ poles, p ∈ K ∧ p ≠ 0) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      AnalyticOnNhd ℂ g K ∧
      ∀ z ∈ K, z ∉ poles →
        thirdOrderExplicitFormulaIntegrand x z =
          g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p :=
  exists_thirdOrderExplicitFormula_analytic_regularized_remainder hx hK hzero

example {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ uIcc (-W) W,
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles, a < p.re ∧ p.re < c ∧ -W < p.im ∧ p.im < W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      MathlibAux.boundaryRectIntegral
          (thirdOrderExplicitFormulaIntegrand x) a c (-W) W =
        2 * Real.pi * Complex.I * ∑ p ∈ poles, residue p :=
  exists_boundaryRectIntegral_thirdOrderExplicitFormulaIntegrand_eq_residue_sum
    hx ha hac hboundary

example (x a c W : ℝ) :
    thirdOrderContourRemainder x a c W =
      ((∫ σ : ℝ in a..c,
            thirdOrderExplicitFormulaIntegrand x
              ((σ : ℂ) + (-(2 * Real.pi * W) : ℝ) * Complex.I)) -
          (∫ σ : ℝ in a..c,
            thirdOrderExplicitFormulaIntegrand x
              ((σ : ℂ) + (2 * Real.pi * W : ℝ) * Complex.I)) -
        Complex.I *
          (∫ t : ℝ in -(2 * Real.pi * W)..2 * Real.pi * W,
            thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * Complex.I))) /
        (2 * Real.pi * Complex.I) := rfl

example {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ
        uIcc (-(2 * Real.pi * W)) (2 * Real.pi * W),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles, a < p.re ∧ p.re < c ∧
        -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      (∫ w : ℝ in -W..W,
        thirdOrderExplicitFormulaIntegrand x
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
        ∑ p ∈ poles, residue p - thirdOrderContourRemainder x a c W :=
  exists_scaledRightIntegral_eq_residue_sum_sub_thirdOrderContourRemainder
    hx ha hac hboundary

end PrimeNumberTheorem.ExplicitFormulaResidues
