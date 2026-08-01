import PrimeNumberTheorem.ZeroDensityLayerBudgetAutomaticCubicContourIntegrability

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

noncomputable def desmoothedCubicBottomContourIntegral
    (x h a c W : ℝ) : ℂ :=
  ∫ sigma : ℝ in a..c,
    desmoothedCubicContourIntegrand x h (cubicBottomContourPoint W sigma)

noncomputable def desmoothedCubicTopContourIntegral
    (x h a c W : ℝ) : ℂ :=
  ∫ sigma : ℝ in a..c,
    desmoothedCubicContourIntegrand x h (cubicTopContourPoint W sigma)

noncomputable def desmoothedCubicLeftContourIntegral
    (x h a _c W : ℝ) : ℂ :=
  ∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
    desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)

/-- The actual bottom/top/left contour after cubic de-smoothing. -/
noncomputable def desmoothedCubicContourRemainder
    (x h a c W : ℝ) : ℂ :=
  (desmoothedCubicBottomContourIntegral x h a c W -
      desmoothedCubicTopContourIntegral x h a c W -
      I * desmoothedCubicLeftContourIntegral x h a c W) /
    (2 * Real.pi * I)

/-- The normalized second difference of the original cubic contour remainder
is exactly the de-smoothed first-order contour remainder. -/
theorem cubicContourSecondDifference_div_sq_eq_desmoothed
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h)
    (ha : 0 < a) (hac : a < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    cubicContourSecondDifference x h a c W / (h : ℂ) ^ 2 =
      desmoothedCubicContourRemainder x h a c W := by
  have hbottom := intervalIntegral_bottom_thirdOrder_secondDifference_div_sq_eq
    hx hh ha hac hW hboundary
  have htop := intervalIntegral_top_thirdOrder_secondDifference_div_sq_eq
    hx hh ha hac hW hboundary
  have hleft := intervalIntegral_left_thirdOrder_secondDifference_div_sq_eq
    hx hh ha hac hW hboundary
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hden : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  dsimp [cubicBottomContourPoint, cubicTopContourPoint,
    cubicLeftContourPoint, desmoothedCubicBottomContourIntegral,
    desmoothedCubicTopContourIntegral, desmoothedCubicLeftContourIntegral]
    at hbottom htop hleft
  unfold cubicContourSecondDifference thirdOrderContourRemainder
  unfold desmoothedCubicContourRemainder
  unfold desmoothedCubicBottomContourIntegral
    desmoothedCubicTopContourIntegral desmoothedCubicLeftContourIntegral
  dsimp [cubicBottomContourPoint, cubicTopContourPoint,
    cubicLeftContourPoint]
  field_simp [hhC, hden] at hbottom htop hleft ⊢
  linear_combination hbottom - htop - I * hleft

/-- A direct triangle budget for the assembled de-smoothed contour. -/
theorem norm_desmoothedCubicContourRemainder_le
    (x h a c W : ℝ) :
    ‖desmoothedCubicContourRemainder x h a c W‖ ≤
      (‖desmoothedCubicBottomContourIntegral x h a c W‖ +
          ‖desmoothedCubicTopContourIntegral x h a c W‖ +
          ‖desmoothedCubicLeftContourIntegral x h a c W‖) /
        (2 * Real.pi) := by
  rw [desmoothedCubicContourRemainder, norm_div]
  have hnum :
      ‖desmoothedCubicBottomContourIntegral x h a c W -
          desmoothedCubicTopContourIntegral x h a c W -
          I * desmoothedCubicLeftContourIntegral x h a c W‖ ≤
        ‖desmoothedCubicBottomContourIntegral x h a c W‖ +
          ‖desmoothedCubicTopContourIntegral x h a c W‖ +
          ‖desmoothedCubicLeftContourIntegral x h a c W‖ := by
    calc
      ‖desmoothedCubicBottomContourIntegral x h a c W -
          desmoothedCubicTopContourIntegral x h a c W -
          I * desmoothedCubicLeftContourIntegral x h a c W‖ ≤
          ‖desmoothedCubicBottomContourIntegral x h a c W -
            desmoothedCubicTopContourIntegral x h a c W‖ +
            ‖I * desmoothedCubicLeftContourIntegral x h a c W‖ :=
        norm_sub_le _ _
      _ ≤ (‖desmoothedCubicBottomContourIntegral x h a c W‖ +
            ‖desmoothedCubicTopContourIntegral x h a c W‖) +
            ‖desmoothedCubicLeftContourIntegral x h a c W‖ := by
        simpa using add_le_add
          (norm_sub_le
            (desmoothedCubicBottomContourIntegral x h a c W)
            (desmoothedCubicTopContourIntegral x h a c W))
          (le_refl ‖desmoothedCubicLeftContourIntegral x h a c W‖)
  have hden : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hden]
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- Pole, finite zero sum, and contour all share one normalized first-order
kernel after the cubic second difference. -/
theorem cubicPoleZeroContour_secondDifference_div_sq_eq
    {P : Finset ℂ} {x h a c W : ℝ}
    (hx : 0 < x) (hh : 0 < h)
    (ha : 0 < a) (hac : a < c) (hW : 0 < W)
    (hnonzero : ∀ rho ∈ P.erase 1, rho ≠ 0)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    (cubicPoleOneSecondDifference x h +
          (∑ rho ∈ P.erase 1, cubicZeroResidueSecondDifference rho x h) -
          cubicContourSecondDifference x h a c W) / (h : ℂ) ^ 2 =
      (x : ℂ) * ((((Real.exp h - 1) / h : ℝ) : ℂ) ^ 2) +
        (∑ rho ∈ P.erase 1,
          cubicSimpleZeroKernel rho x * cubicKernelMultiplier rho h) -
        desmoothedCubicContourRemainder x h a c W := by
  have hpole := cubicPoleOneSecondDifference_div_sq_eq (x := x) hh
  have hcontour := cubicContourSecondDifference_div_sq_eq_desmoothed
    hx hh ha hac hW hboundary
  have hzeros :
      (∑ rho ∈ P.erase 1, cubicZeroResidueSecondDifference rho x h) /
          (h : ℂ) ^ 2 =
        ∑ rho ∈ P.erase 1,
          cubicSimpleZeroKernel rho x * cubicKernelMultiplier rho h := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro rho hrho
    exact cubicZeroResidueSecondDifference_div_sq_eq_simple_mul_multiplier
      hx hh (hnonzero rho hrho)
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  field_simp [hhC] at hpole hcontour hzeros ⊢
  linear_combination hpole + hzeros - hcontour

end ExplicitFormulaResidues
end PrimeNumberTheorem
