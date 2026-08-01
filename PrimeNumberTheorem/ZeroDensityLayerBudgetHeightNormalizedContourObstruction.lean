import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay

/-!
# Obstruction at the reciprocal-height zero scale

The selected unsmoothed explicit formula has a leading relative contour
majorant of size `x^(-alpha) (1 + log x)^2` at height `x^alpha`.
Normalizing against the natural high-zero scale
`targetZeroPowerAmplitude beta x / x^alpha` cancels the height exponent
exactly and leaves `x^(1-beta) (1 + log x)^2`.

Thus, for every `beta < 1`, the present contour majorant diverges rather than
tending to zero at the reciprocal-height scale.  This is an obstruction for
this majorant method, not a lower bound for the actual explicit-formula
remainder.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- The leading selected-contour term after normalization by the target zero
amplitude divided by the polynomial truncation height. -/
noncomputable def heightNormalizedContourMainRatio
    (C beta alpha x : ℝ) : ℝ :=
  (x ^ alpha *
      (10 * C * x ^ (-alpha) * (1 + Real.log x) ^ 2)) /
    targetZeroPowerAmplitude beta x

/-- The polynomial height cancels exactly from the leading normalized
contour term. -/
theorem heightNormalizedContourMainRatio_eq
    {C beta alpha x : ℝ} (hx : 0 < x) :
    heightNormalizedContourMainRatio C beta alpha x =
      10 * C * (1 + Real.log x) ^ 2 * x ^ (1 - beta) := by
  have hpow :
      x ^ alpha * x ^ (-alpha) * x ^ (-(beta - 1)) =
        x ^ (1 - beta) := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  unfold heightNormalizedContourMainRatio targetZeroPowerAmplitude
  rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
  calc
    x ^ alpha *
          (10 * C * x ^ (-alpha) * (1 + Real.log x) ^ 2) *
        x ^ (-(beta - 1)) =
        10 * C * (1 + Real.log x) ^ 2 *
          (x ^ alpha * x ^ (-alpha) * x ^ (-(beta - 1))) := by ring
    _ = 10 * C * (1 + Real.log x) ^ 2 * x ^ (1 - beta) := by
      rw [hpow]

/-- For positive contour constant and every target real part below one, the
leading reciprocal-height normalized contour term tends to infinity. -/
theorem tendsto_heightNormalizedContourMainRatio_atTop
    {C beta alpha : ℝ} (hC : 0 < C) (hbetaOne : beta < 1) :
    Tendsto
      (heightNormalizedContourMainRatio C beta alpha)
      atTop atTop := by
  have hpower :
      Tendsto (fun x : ℝ => x ^ (1 - beta)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  have hscaled :
      Tendsto (fun x : ℝ => 10 * C * x ^ (1 - beta)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) hpower
  apply tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  rw [heightNormalizedContourMainRatio_eq hxPos]
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsquare : 1 ≤ (1 + Real.log x) ^ 2 := by nlinarith
  have hcoef : 0 ≤ 10 * C := by positivity
  have hpowNonneg : 0 ≤ x ^ (1 - beta) := Real.rpow_nonneg hxPos.le _
  calc
    10 * C * x ^ (1 - beta) =
        (10 * C * 1) * x ^ (1 - beta) := by ring
    _ ≤ (10 * C * (1 + Real.log x) ^ 2) * x ^ (1 - beta) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare hcoef) hpowNonneg
    _ = 10 * C * (1 + Real.log x) ^ 2 * x ^ (1 - beta) := by ring

/-- The complete displayed two-power contour majorant, normalized at natural
points by the reciprocal polynomial-height target scale. -/
noncomputable def selectedPolynomialHeightNormalizedContourRatio
    (C beta alpha : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) ^ alpha *
      selectedPolynomialNaturalContourMajorant C alpha m) /
    targetZeroPowerAmplitude beta (m : ℝ)

/-- The complete selected contour majorant also diverges at the
reciprocal-height target scale. -/
theorem tendsto_selectedPolynomialHeightNormalizedContourRatio_atTop
    {C beta alpha : ℝ} (hC : 0 < C) (hbetaOne : beta < 1) :
    Tendsto
      (selectedPolynomialHeightNormalizedContourRatio C beta alpha)
      atTop atTop := by
  have hmain :
      Tendsto
        (fun m : ℕ =>
          heightNormalizedContourMainRatio C beta alpha (m : ℝ))
        atTop atTop :=
    (tendsto_heightNormalizedContourMainRatio_atTop hC hbetaOne).comp
      tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop ?_ hmain
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hxPos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have htarget :
      0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    Real.rpow_pos_of_pos hxPos _
  have hheight : 0 ≤ (m : ℝ) ^ alpha := Real.rpow_nonneg hxPos.le _
  have htail :
      0 ≤ 2 * cofinalPNTZeroDepthTailConstant *
          (m : ℝ) ^ (-1 : ℝ) *
          (1 + Real.log (m : ℝ)) ^ 2 := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          cofinalPNTZeroDepthTailConstant_nonneg)
        (Real.rpow_nonneg hxPos.le _))
      (sq_nonneg _)
  unfold heightNormalizedContourMainRatio
    selectedPolynomialHeightNormalizedContourRatio
    selectedPolynomialNaturalContourMajorant
  apply div_le_div_of_nonneg_right _ htarget.le
  apply mul_le_mul_of_nonneg_left _ hheight
  exact le_add_of_nonneg_right htail

/-- In particular, the displayed reciprocal-height normalized contour
majorant cannot tend to zero. -/
theorem not_tendsto_selectedPolynomialHeightNormalizedContourRatio_zero
    {C beta alpha : ℝ} (hC : 0 < C) (hbetaOne : beta < 1) :
    ¬ Tendsto
      (selectedPolynomialHeightNormalizedContourRatio C beta alpha)
      atTop (nhds 0) := by
  intro hzero
  have hlt :
      ∀ᶠ m : ℕ in atTop,
        selectedPolynomialHeightNormalizedContourRatio C beta alpha m < 1 :=
    hzero.eventually_lt_const zero_lt_one
  have hge :
      ∀ᶠ m : ℕ in atTop,
        1 ≤ selectedPolynomialHeightNormalizedContourRatio C beta alpha m :=
    (tendsto_atTop.1
      (tendsto_selectedPolynomialHeightNormalizedContourRatio_atTop
        hC hbetaOne)) 1
  rcases (hlt.and hge).exists with ⟨m, hmLt, hmGe⟩
  exact (not_lt_of_ge hmGe) hmLt

end
end PrimeNumberTheorem
