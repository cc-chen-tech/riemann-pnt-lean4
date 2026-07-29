import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonBalancedCoefficientBound
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingLogPowerAbsorption

namespace PrimeNumberTheorem

/-- A strictly positive fixed envelope for the complete balanced coefficient.
-/
noncomputable def actualMovingCarlsonBalancedPositiveConstant
    (A alpha : ℝ) : ℝ :=
  1 + |actualMovingCarlsonBalancedQuadraticConstant A alpha|

theorem actualMovingCarlsonBalancedPositiveConstant_pos
    (A alpha : ℝ) :
    0 < actualMovingCarlsonBalancedPositiveConstant A alpha := by
  unfold actualMovingCarlsonBalancedPositiveConstant
  positivity

theorem actualMovingCarlsonBalancedPointwiseCoefficient_le_positiveQuadratic
    {A alpha delta : ℝ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8) :
    actualMovingCarlsonBalancedPointwiseCoefficient A alpha delta ≤
      actualMovingCarlsonBalancedPositiveConstant A alpha / delta ^ 2 := by
  apply
    (actualMovingCarlsonBalancedPointwiseCoefficient_le_quadratic
      hA halpha hdelta hdeltaUpper).trans
  have hconstant :
      actualMovingCarlsonBalancedQuadraticConstant A alpha ≤
        actualMovingCarlsonBalancedPositiveConstant A alpha := by
    unfold actualMovingCarlsonBalancedPositiveConstant
    exact le_trans (le_abs_self _) (le_add_of_nonneg_left zero_le_one)
  exact div_le_div_of_nonneg_right hconstant (sq_nonneg delta)

/-- Exponentiating the honest log-power envelope gives exactly
`C * delta⁻² * (log x)^4`. -/
theorem exp_carlsonMovingQuadraticLogPowerEnvelope
    {C delta x : ℝ} (hC : 0 < C) (hdelta : 0 < delta) (hx : 1 < x) :
    Real.exp
        (Real.log C + 2 * Real.log delta⁻¹ +
          4 * Real.log (Real.log x)) =
      C / delta ^ 2 * (Real.log x) ^ (4 : ℕ) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [show Real.log C + 2 * Real.log delta⁻¹ +
      4 * Real.log (Real.log x) =
        (Real.log C + 2 * Real.log delta⁻¹) +
          4 * Real.log (Real.log x) by ring]
  rw [Real.exp_add,
    exp_carlsonMovingQuadraticLogEnvelope hC hdelta]
  have hfour :
      Real.exp (4 * Real.log (Real.log x)) =
        (Real.log x) ^ (4 : ℕ) := by
    calc
      _ = Real.exp
          (Real.log (Real.log x) + Real.log (Real.log x) +
            Real.log (Real.log x) + Real.log (Real.log x)) := by
          congr 1
          ring
      _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add,
          Real.exp_log hlog]
        ring
  rw [hfour]

/-- The existing moving balanced ratio with the log-power envelope is exactly
the normalized polynomial-height pointwise majorant. -/
theorem carlsonMovingBalancedLogPowerRatio_eq
    {alpha C delta x : ℝ}
    (hC : 0 < C) (hdelta : 0 < delta) (hx : 1 < x) :
    Real.exp
        ((Real.log C + 2 * Real.log delta⁻¹ +
            4 * Real.log (Real.log x)) +
          carlsonTwoHeightBalancedExponent
              (1 - 2 * delta) (1 - delta) alpha *
            Real.log x) =
      C / delta ^ 2 *
        (x ^ carlsonTwoHeightBalancedExponent
            (1 - 2 * delta) (1 - delta) alpha *
          (Real.log x) ^ (4 : ℕ)) := by
  rw [Real.exp_add,
    exp_carlsonMovingQuadraticLogPowerEnvelope hC hdelta hx]
  rw [show
      carlsonTwoHeightBalancedExponent
          (1 - 2 * delta) (1 - delta) alpha * Real.log x =
        Real.log x * carlsonTwoHeightBalancedExponent
          (1 - 2 * delta) (1 - delta) alpha by ring]
  rw [← Real.rpow_def_of_pos (lt_trans zero_lt_one hx)]
  ring

/-- The complete actual balanced pointwise majorant is bounded by the honest
log-power moving ratio. -/
theorem actualMovingCarlsonTwoHeightPointwiseMajorant_le_logPowerRatio
    {A alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hm : 2 ≤ m) (hdelta : 0 < delta m) (hdeltaUpper : delta m ≤ 1 / 8) :
    actualMovingCarlsonTwoHeightPointwiseMajorant
        A alpha delta (carlsonMovingBalancedCut alpha delta) m ≤
      carlsonMovingBalancedCoefficientRatio alpha delta
        (carlsonMovingQuadraticLogPowerEnvelope
          (actualMovingCarlsonBalancedPositiveConstant A alpha) delta) m := by
  have hmOne : 1 ≤ m := le_trans (by norm_num) hm
  have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hquarter : delta m < 1 / 4 :=
    hdeltaUpper.trans_lt (by norm_num)
  rw [actualMovingCarlsonTwoHeightPointwiseMajorant_balanced_eq
    hmOne hdelta hquarter]
  have hbase0 :
      0 ≤ (m : ℝ) ^
            carlsonTwoHeightBalancedExponent
              (1 - 2 * delta m) (1 - delta m) alpha *
          (Real.log (m : ℝ)) ^ (4 : ℕ) := by positivity
  apply
    (mul_le_mul_of_nonneg_right
      (actualMovingCarlsonBalancedPointwiseCoefficient_le_positiveQuadratic
        hA halpha hdelta hdeltaUpper) hbase0).trans_eq
  unfold carlsonMovingBalancedCoefficientRatio
    carlsonMovingQuadraticLogPowerEnvelope
  symm
  exact carlsonMovingBalancedLogPowerRatio_eq
    (actualMovingCarlsonBalancedPositiveConstant_pos A alpha)
      hdelta hmReal

end PrimeNumberTheorem
