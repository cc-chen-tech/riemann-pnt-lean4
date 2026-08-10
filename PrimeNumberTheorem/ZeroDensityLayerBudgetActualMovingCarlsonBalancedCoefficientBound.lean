import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonBalancedMajorant
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingCoefficientGrowth

namespace PrimeNumberTheorem

/-- A fixed constant controlling both balanced low/high pointwise
coefficients. -/
noncomputable def actualMovingCarlsonBalancedQuadraticConstant
    (A alpha : ℝ) : ℝ :=
  375 * carlsonMovingActualCoefficientQuadraticConstant A *
    alpha ^ (4 : ℕ)

/-- The complete balanced low/high coefficient grows at most quadratically in
the reciprocal moving gap. -/
theorem actualMovingCarlsonBalancedPointwiseCoefficient_le_quadratic
    {A alpha delta : ℝ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8) :
    actualMovingCarlsonBalancedPointwiseCoefficient A alpha delta ≤
      actualMovingCarlsonBalancedQuadraticConstant A alpha / delta ^ 2 := by
  have hquarter : delta < 1 / 4 := hdeltaUpper.trans_lt (by norm_num)
  have hsigma : 1 / 2 < 1 - 2 * delta := by linarith
  have hsigmaOne : 1 - 2 * delta < 1 := by linarith
  have hsigmaPos : 0 < 1 - 2 * delta := lt_trans (by norm_num) hsigma
  have hK :
      0 ≤ CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) :=
    CarlsonZeroDensity.zero_le_carlsonFinalCoefficient
      hA hsigma hsigmaOne
  have hcut0 :
      0 ≤ carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha :=
    (carlsonMovingBalancedCut_pos hdelta hquarter halpha).le
  have hcutAlpha :
      carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha ≤ alpha :=
    (carlsonMovingBalancedCut_lt_alpha hdelta hquarter halpha).le
  have hcutPow :
      (carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha) ^ (4 : ℕ) ≤
        alpha ^ (4 : ℕ) :=
    pow_le_pow_left₀ hcut0 hcutAlpha 4
  have halphaPow0 : 0 ≤ alpha ^ (4 : ℕ) := by positivity
  have hinvSigma : (1 - 2 * delta)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hsigmaPos]
    linarith
  have hcutDiv :
      (carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha) ^ (4 : ℕ) /
          (1 - 2 * delta) ≤
        2 * alpha ^ (4 : ℕ) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha) ^ (4 : ℕ) *
            2 :=
        mul_le_mul_of_nonneg_left hinvSigma (pow_nonneg hcut0 _)
      _ ≤ alpha ^ (4 : ℕ) * 2 :=
        mul_le_mul_of_nonneg_right hcutPow (by norm_num)
      _ = _ := by ring
  have hlow :
      125 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
          (carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha) ^ (4 : ℕ) /
            (1 - 2 * delta) ≤
        250 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
          alpha ^ (4 : ℕ) := by
    have hscale : 0 ≤
        125 * CarlsonZeroDensity.carlsonFinalCoefficient A
          (1 - 2 * delta) := mul_nonneg (by norm_num) hK
    have := mul_le_mul_of_nonneg_left hcutDiv hscale
    convert this using 1 <;> ring
  have hcombined :
      actualMovingCarlsonBalancedPointwiseCoefficient A alpha delta ≤
        375 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
          alpha ^ (4 : ℕ) := by
    unfold actualMovingCarlsonBalancedPointwiseCoefficient
    linarith
  have hcoefficient :=
    carlsonFinalCoefficient_moving_le_quadratic
      (A := A) hdelta hdeltaUpper
  have hscale : 0 ≤ 375 * alpha ^ (4 : ℕ) := by positivity
  calc
    _ ≤ 375 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
        alpha ^ (4 : ℕ) := hcombined
    _ = (375 * alpha ^ (4 : ℕ)) *
        CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) := by ring
    _ ≤ (375 * alpha ^ (4 : ℕ)) *
        (carlsonMovingActualCoefficientQuadraticConstant A / delta ^ 2) :=
      mul_le_mul_of_nonneg_left hcoefficient hscale
    _ = actualMovingCarlsonBalancedQuadraticConstant A alpha / delta ^ 2 := by
      unfold actualMovingCarlsonBalancedQuadraticConstant
      ring

end PrimeNumberTheorem
