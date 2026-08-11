import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroPoleRectangle

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem.ExplicitFormulaResidues

/-- The scaled right-edge integral across a negative left boundary equals the
zero-pole-corrected residue sum minus the genuine third-order contour remainder. -/
theorem exists_scaledRightIntegral_eq_zeroPoleResidue_sum_sub_thirdOrderContourRemainder
    {x a c W : ℝ} (hx : 0 < x) (ha : a < 0) (hc : 0 < c)
    (hW : 0 < W)
    (hboundary : ∀ p ∈ uIcc a c ×ℂ
        uIcc (-(2 * Real.pi * W)) (2 * Real.pi * W),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ) (cubic : ℂ),
      0 ∈ poles ∧
      (∀ p ∈ poles, a < p.re ∧ p.re < c ∧
        -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 0 then residue 0
        else if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      (∫ w : ℝ in -W..W,
        thirdOrderExplicitFormulaIntegrand x
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
        ∑ p ∈ poles, residue p - thirdOrderContourRemainder x a c W := by
  have hheight : 0 < 2 * Real.pi * W :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) hW
  obtain ⟨poles, residue, cubic, h0mem, hpoles, hpolesType,
      hresidue, hcubic, hrect⟩ :=
    exists_boundaryRectIntegral_thirdOrderExplicitFormulaIntegrand_eq_residue_sum_zeroPole
      hx ha hc hheight hboundary
  refine ⟨poles, residue, cubic, h0mem, hpoles, hpolesType,
    hresidue, hcubic, ?_⟩
  have hscale := I_mul_verticalIntegral_eq_two_pi_I_mul_scaledIntegral
    (thirdOrderExplicitFormulaIntegrand x) c W
  unfold MathlibAux.boundaryRectIntegral at hrect
  simp only [smul_eq_mul] at hrect
  rw [hscale] at hrect
  let B : ℂ := ∫ σ : ℝ in a..c,
    thirdOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + (-(2 * Real.pi * W) : ℝ) * Complex.I)
  let T : ℂ := ∫ σ : ℝ in a..c,
    thirdOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + (2 * Real.pi * W : ℝ) * Complex.I)
  let L : ℂ := ∫ t : ℝ in -(2 * Real.pi * W)..2 * Real.pi * W,
    thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * Complex.I)
  let R : ℂ := ∫ w : ℝ in -W..W,
    thirdOrderExplicitFormulaIntegrand x
      ((c : ℂ) + 2 * Real.pi * w * Complex.I)
  let S : ℂ := ∑ p ∈ poles, residue p
  let q : ℂ := 2 * Real.pi * Complex.I
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  change B - T + q * R - Complex.I * L = q * S at hrect
  change R = S - (B - T - Complex.I * L) / q
  field_simp [hq]
  linear_combination hrect

end PrimeNumberTheorem.ExplicitFormulaResidues
