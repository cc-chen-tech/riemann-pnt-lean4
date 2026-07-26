import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderBridge
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPolynomialRemainderCriterion
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFormulaRemainderDecay

/-!
# Target decay of the selected polynomial-height natural remainder

For `0 < alpha <= 1`, a selected height in
`[m ^ alpha - 1, m ^ alpha]` turns the depth-zero contour bound into

`O(m ^ (-alpha) (1 + log m)^2) + O(m ^ (-1) (1 + log m)^2)`.

After division by the target-zero amplitude `m ^ (beta - 1)`, both terms tend
to zero under the sharp polynomial margin `1 - beta < alpha` and `beta > 0`.
The closed logarithmic trivial-zero term is handled separately and then added
back to the explicit selected-height majorant.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Two-power majorant for the selected polynomial-height relative contour
remainder. -/
noncomputable def selectedPolynomialNaturalContourMajorant
    (C alpha : ℝ) (m : ℕ) : ℝ :=
  10 * C * (m : ℝ) ^ (-alpha) *
      (1 + Real.log (m : ℝ)) ^ 2 +
    2 * cofinalPNTZeroDepthTailConstant * (m : ℝ) ^ (-1 : ℝ) *
      (1 + Real.log (m : ℝ)) ^ 2

theorem selectedPolynomialNaturalContourMajorant_nonneg
    {C alpha : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    0 ≤ selectedPolynomialNaturalContourMajorant C alpha m := by
  unfold selectedPolynomialNaturalContourMajorant
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) hC)
        (Real.rpow_nonneg (Nat.cast_nonneg m) (-alpha)))
      (sq_nonneg _))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          cofinalPNTZeroDepthTailConstant_nonneg)
        (Real.rpow_nonneg (Nat.cast_nonneg m) (-1 : ℝ)))
      (sq_nonneg _))

set_option maxHeartbeats 1200000 in
/-- Pointwise polynomial-height reduction of the exact depth-zero contour
bound to the two target-compatible power scales. -/
theorem
    cofinalPNTFormulaRemainderBound_zero_relative_le_selectedPolynomialMajorant
    {C alpha T : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hm : 5 ≤ m) (hpower : 2 ≤ (m : ℝ) ^ alpha)
    (hT :
      T ∈ Set.Icc ((m : ℝ) ^ alpha - 1) ((m : ℝ) ^ alpha)) :
    cofinalPNTFormulaRemainderBound C
        ((m : ℝ) ^ alpha - 1) T m 0 / (m : ℝ) ≤
      selectedPolynomialNaturalContourMajorant C alpha m := by
  let x : ℝ := m
  let P : ℝ := x ^ alpha
  let L : ℝ := 1 + Real.log x
  let K0 : ℝ :=
    ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
      ‖Complex.log (Real.pi : ℂ)‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) +
      Real.pi
  have hx5 : (5 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hm
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  have hPdef : P = x ^ alpha := rfl
  have hPtwo : 2 ≤ P := by simpa [P, x] using hpower
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hPtwo
  have hP_le_x : P ≤ x := by
    dsimp [P]
    exact Real.rpow_le_self_of_one_le hxone halphaOne
  have hTlower : P - 1 ≤ T := by simpa [P, x] using hT.1
  have hTupper : T ≤ P := by simpa [P, x] using hT.2
  have hTpos : 0 < T := by linarith
  have hHalfPpos : 0 < P / 2 := by positivity
  have hHalfP_le_T : P / 2 ≤ T := by linarith
  have hAplus : P + 5 ≤ 2 * x := by linarith
  have hlogPplus :
      Real.log (P + 5) ≤ 2 * Real.log x := by
    have hmono : Real.log (P + 5) ≤ Real.log (2 * x) :=
      Real.log_le_log (by linarith) hAplus
    have hlogTwo_le : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_mul (by norm_num) hxpos.ne'] at hmono
    linarith
  have hLP0 : 0 ≤ 1 + Real.log (P + 5) := by
    have harg : 1 ≤ P + 5 := by linarith
    linarith [Real.log_nonneg harg]
  have hlogSquares :
      L ^ 2 + (1 + Real.log (P + 5)) ^ 2 ≤ 5 * L ^ 2 := by
    have hLP :
        1 + Real.log (P + 5) ≤ 1 + 2 * Real.log x := by
      linarith
    have hLPsq :
        (1 + Real.log (P + 5)) ^ 2 ≤
          (1 + 2 * Real.log x) ^ 2 := by
      nlinarith
    have hdouble :
        (1 + 2 * Real.log x) ^ 2 ≤ 4 * L ^ 2 := by
      dsimp [L]
      nlinarith
    nlinarith
  have hmain :
      (C * x *
          (L ^ 2 + (1 + Real.log (P + 5)) ^ 2) / T) / x ≤
        10 * C * x ^ (-alpha) * L ^ 2 := by
    calc
      (C * x *
          (L ^ 2 + (1 + Real.log (P + 5)) ^ 2) / T) / x =
          C * (L ^ 2 + (1 + Real.log (P + 5)) ^ 2) / T := by
            field_simp [hxpos.ne']
      _ ≤ C * (5 * L ^ 2) / T := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogSquares hC) hTpos.le
      _ ≤ C * (5 * L ^ 2) / (P / 2) := by
        exact div_le_div_of_nonneg_left (by positivity)
          hHalfPpos hHalfP_le_T
      _ = 10 * C * x ^ (-alpha) * L ^ 2 := by
        rw [Real.rpow_neg hxpos.le]
        rw [hPdef]
        field_simp [ne_of_gt hPpos]
        ring
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    have hseries :
        0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    positivity
  have hlogT :
      Real.log (T + 4) ≤ 2 * Real.log x := by
    have hT4 : T + 4 ≤ 2 * x := by
      linarith
    have hmono : Real.log (T + 4) ≤ Real.log (2 * x) :=
      Real.log_le_log (by linarith) hT4
    have hlogTwo_le : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_mul (by norm_num) hxpos.ne'] at hmono
    linarith
  have hcoeff0 :
      0 ≤ K0 + 2 * Real.log (T + 4) := by
    have hlog0 : 0 ≤ Real.log (T + 4) :=
      Real.log_nonneg (by linarith)
    positivity
  have hK :
      cofinalPNTZeroDepthTailConstant = K0 + 4 := by
    rfl
  have hcoeff :
      K0 + 2 * Real.log (T + 4) ≤
        cofinalPNTZeroDepthTailConstant * L := by
    rw [hK]
    have hfirst :
        K0 + 2 * Real.log (T + 4) ≤
          K0 + 4 * Real.log x := by linarith
    calc
      K0 + 2 * Real.log (T + 4) ≤
          K0 + 4 * Real.log x := hfirst
      _ ≤ (K0 + 4) * L := by
        dsimp [L]
        nlinarith [mul_nonneg hK0 hlogx0]
  have hinvT : x ^ (-1 : ℝ) * T ≤ 1 := by
    rw [Real.rpow_neg_one]
    exact (inv_mul_le_iff₀ hxpos).2 (by
      simpa [mul_comm] using hTupper.trans hP_le_x)
  have hpi : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have htail :
      (((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
          (2 * T) / (2 * Real.pi)) / x ≤
        2 * cofinalPNTZeroDepthTailConstant * x ^ (-1 : ℝ) *
          L ^ 2 := by
    have hnum0 :
        0 ≤ ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
          (2 * T) := by
      positivity
    have hdrop :
        ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
              (2 * T) / (2 * Real.pi) ≤
          ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
              (2 * T) :=
      div_le_self hnum0 hpi
    have hbefore :
        (((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
            (2 * T) / (2 * Real.pi)) / x ≤
          2 * cofinalPNTZeroDepthTailConstant * L / x := by
      apply div_le_div_of_nonneg_right (hdrop.trans ?_) hxpos.le
      calc
        ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
            (2 * T) =
          2 * (K0 + 2 * Real.log (T + 4)) *
            (x ^ (-1 : ℝ) * T) := by ring
        _ ≤ 2 * (cofinalPNTZeroDepthTailConstant * L) *
            (x ^ (-1 : ℝ) * T) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hcoeff (by norm_num)
          · exact mul_nonneg (Real.rpow_nonneg hxpos.le _) hTpos.le
        _ ≤ 2 * (cofinalPNTZeroDepthTailConstant * L) * 1 := by
          apply mul_le_mul_of_nonneg_left hinvT
          exact mul_nonneg (by norm_num)
            (mul_nonneg cofinalPNTZeroDepthTailConstant_nonneg
              (zero_le_one.trans hLone))
        _ = 2 * cofinalPNTZeroDepthTailConstant * L := by ring
    calc
      (((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
          (2 * T) / (2 * Real.pi)) / x ≤
          2 * cofinalPNTZeroDepthTailConstant * L / x := hbefore
      _ ≤ 2 * cofinalPNTZeroDepthTailConstant * L ^ 2 / x := by
        have hLL : L ≤ L ^ 2 := by
          calc
            L = L * 1 := by ring
            _ ≤ L * L :=
              mul_le_mul_of_nonneg_left hLone (le_trans (by norm_num) hLone)
            _ = L ^ 2 := by ring
        rw [div_le_div_iff_of_pos_right hxpos]
        exact mul_le_mul_of_nonneg_left hLL
          (mul_nonneg (by norm_num) cofinalPNTZeroDepthTailConstant_nonneg)
      _ = 2 * cofinalPNTZeroDepthTailConstant * x ^ (-1 : ℝ) *
          L ^ 2 := by
        rw [Real.rpow_neg_one]
        field_simp [hxpos.ne']
  have hremainder :
      cofinalPNTFormulaRemainderBound C
          ((m : ℝ) ^ alpha - 1) T m 0 =
        C * x * (L ^ 2 + (1 + Real.log (P + 5)) ^ 2) / T +
          ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
            (2 * T) / (2 * Real.pi) := by
    simp [cofinalPNTFormulaRemainderBound, x, P, L, K0]
    ring
    all_goals simp
  rw [hremainder, add_div]
  simpa [selectedPolynomialNaturalContourMajorant, x, L] using
    add_le_add hmain htail

/-- The exact selected-height depth-zero contour bound is eventually
nonnegative. -/
theorem eventually_selectedPolynomialContourRelative_nonneg
    {alpha : ℝ} (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      0 ≤
        cofinalPNTFormulaRemainderBound selection.constant
          ((m : ℝ) ^ alpha - 1)
          (selectedUniformGoodHeight alpha selection (m : ℝ)) m 0 /
          (m : ℝ) := by
  have hpower :
      Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlargeReal : ∀ᶠ x : ℝ in atTop, 9 ≤ x ^ alpha :=
    (tendsto_atTop.1 hpower) 9
  have hlargeNat : ∀ᶠ m : ℕ in atTop, 9 ≤ (m : ℝ) ^ alpha :=
    tendsto_natCast_atTop_atTop.eventually hlargeReal
  filter_upwards [hlargeNat, eventually_ge_atTop (3 : ℕ)] with
      m hlarge hm
  have hbase : 8 ≤ (m : ℝ) ^ alpha - 1 := by linarith
  rcases
      selectedUniformGoodHeight_truncatedCertificate
        selection m 0 hm hbase with
    ⟨certificate, _htrivial, hremainder⟩
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hm)
  rw [← hremainder]
  exact div_nonneg certificate.remainder_nonneg hmpos.le

/-- The selected contour relative bound is eventually dominated by the
polynomial two-power majorant. -/
theorem eventually_selectedPolynomialContourRelative_le_majorant
    {alpha : ℝ} (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      cofinalPNTFormulaRemainderBound selection.constant
          ((m : ℝ) ^ alpha - 1)
          (selectedUniformGoodHeight alpha selection (m : ℝ)) m 0 /
          (m : ℝ) ≤
        selectedPolynomialNaturalContourMajorant
          selection.constant alpha m := by
  have hheight :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedUniformGoodHeight_mem halpha selection)
  have hpowerReal :
      Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hpowerNat : ∀ᶠ m : ℕ in atTop, 2 ≤ (m : ℝ) ^ alpha :=
    tendsto_natCast_atTop_atTop.eventually
      ((tendsto_atTop.1 hpowerReal) 2)
  filter_upwards [hheight, hpowerNat, eventually_ge_atTop (5 : ℕ)] with
      m hT hpower hm
  exact
    cofinalPNTFormulaRemainderBound_zero_relative_le_selectedPolynomialMajorant
      selection.constant_nonneg halpha halphaOne hm hpower hT

/-- The polynomial two-power majorant is negligible relative to the target
zero amplitude under the strict exponent margin. -/
theorem selectedPolynomialNaturalContourMajorant_targetNegligible
    {C beta alpha : ℝ} (hC : 0 ≤ C) (hbeta : 0 < beta)
    (hmargin : 1 - beta < alpha) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (selectedPolynomialNaturalContourMajorant C alpha) := by
  have hmain :=
    (tendsto_actualPolynomialRemainderTargetMajorant
      (C := 10 * C) (beta := beta) (alpha := alpha)
      (mul_nonneg (by norm_num) hC) hmargin).comp
        tendsto_natCast_atTop_atTop
  have honeMargin : 1 - beta < (1 : ℝ) := by linarith
  have htail :=
    (tendsto_actualPolynomialRemainderTargetMajorant
      (C := 2 * cofinalPNTZeroDepthTailConstant)
      (beta := beta) (alpha := 1)
      (mul_nonneg (by norm_num)
        cofinalPNTZeroDepthTailConstant_nonneg)
      honeMargin).comp tendsto_natCast_atTop_atTop
  unfold NaturalPointTargetAmplitudeNegligible
  have hsum :
      Tendsto
        (fun m : ℕ =>
          actualPolynomialRemainderTargetMajorant
              (10 * C) beta alpha (m : ℝ) +
            actualPolynomialRemainderTargetMajorant
              (2 * cofinalPNTZeroDepthTailConstant) beta 1 (m : ℝ))
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, add_zero] using hmain.add htail
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hxpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hm)
  have hmajorant0 :
      0 ≤ selectedPolynomialNaturalContourMajorant C alpha m :=
    selectedPolynomialNaturalContourMajorant_nonneg hC m
  rw [abs_of_nonneg hmajorant0]
  unfold selectedPolynomialNaturalContourMajorant
    actualPolynomialRemainderTargetMajorant targetZeroPowerAmplitude
  rw [add_div]
  have hpowAlpha :
      (m : ℝ) ^ (-alpha) *
          (m : ℝ) ^ (-(beta - 1)) =
        (m : ℝ) ^ (1 - beta - alpha) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hpowOne :
      (m : ℝ) ^ (-1 : ℝ) *
          (m : ℝ) ^ (-(beta - 1)) =
        (m : ℝ) ^ (1 - beta - 1) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  congr 1
  · rw [div_eq_mul_inv, ← Real.rpow_neg hxpos.le, ← hpowAlpha]
    ring
  · rw [div_eq_mul_inv, ← Real.rpow_neg hxpos.le, ← hpowOne]
    ring

/-- The selected depth-zero contour bound itself is target-negligible. -/
theorem selectedUniformGoodHeight_contourRelative_targetNegligible
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        cofinalPNTFormulaRemainderBound selection.constant
          ((m : ℝ) ^ alpha - 1)
          (selectedUniformGoodHeight alpha selection (m : ℝ)) m 0 /
          (m : ℝ)) := by
  apply NaturalPointTargetAmplitudeNegligible.of_eventually_abs_le
    (eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta))
    (selectedPolynomialNaturalContourMajorant_targetNegligible
      selection.constant_nonneg hbeta hmargin)
  filter_upwards
      [eventually_selectedPolynomialContourRelative_nonneg halpha selection,
        eventually_selectedPolynomialContourRelative_le_majorant
          halpha halphaOne selection] with m hnonneg hle
  rwa [abs_of_nonneg hnonneg]

/-- The closed logarithmic term left by the depth-zero truncation is
target-negligible at natural points for every positive target real part. -/
theorem selectedNaturalClosedLogRelative_targetNegligible
    {beta : ℝ} (hbeta : 0 < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        ‖(1 / 2 : ℂ) *
          (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ / (m : ℝ)) := by
  have hlog :=
    tendsto_log_one_sub_rpow_neg_two_atTop.comp
      tendsto_natCast_atTop_atTop
  have hnorm :
      Tendsto
        (fun m : ℕ =>
          ‖(1 / 2 : ℂ) *
            (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖)
        atTop (nhds 0) := by
    have habs := hlog.abs
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      habs.const_mul (1 / 2 : ℝ)
  have hpower :=
    (tendsto_rpow_neg_atTop hbeta).comp
      tendsto_natCast_atTop_atTop
  unfold NaturalPointTargetAmplitudeNegligible
  have hproduct :
      Tendsto
        (fun m : ℕ =>
          ‖(1 / 2 : ℂ) *
            (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ *
            (m : ℝ) ^ (-beta))
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using hnorm.mul hpower
  apply hproduct.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hxpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hm)
  have hterm0 :
      0 ≤
        ‖(1 / 2 : ℂ) *
          (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ / (m : ℝ) :=
    div_nonneg (norm_nonneg _) hxpos.le
  rw [abs_of_nonneg hterm0]
  unfold targetZeroPowerAmplitude
  rw [div_div]
  have hden :
      (m : ℝ) * (m : ℝ) ^ (beta - 1) =
        (m : ℝ) ^ beta := by
    calc
      (m : ℝ) * (m : ℝ) ^ (beta - 1) =
          (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (beta - 1) :=
        congrArg (fun y => y * (m : ℝ) ^ (beta - 1))
          (Real.rpow_one (m : ℝ)).symm
      _ = (m : ℝ) ^ ((1 : ℝ) + (beta - 1)) :=
        (Real.rpow_add hxpos 1 (beta - 1)).symm
      _ = (m : ℝ) ^ beta := by congr 1 <;> ring
  rw [hden, div_eq_mul_inv]
  congr 1
  exact Real.rpow_neg hxpos.le beta

/-- The complete explicit selected-height natural remainder upper bound is
target-negligible. -/
theorem selectedUniformGoodHeightNaturalRemainderUpperBound_targetNegligible
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (selectedUniformGoodHeightNaturalRemainderUpperBound
        alpha selection) := by
  have hcontour :=
    selectedUniformGoodHeight_contourRelative_targetNegligible
      hbeta halpha halphaOne hmargin selection
  have hclosed :=
    selectedNaturalClosedLogRelative_targetNegligible hbeta
  unfold NaturalPointTargetAmplitudeNegligible at hcontour hclosed ⊢
  have hsum :
      Tendsto
        (fun m : ℕ =>
          |cofinalPNTFormulaRemainderBound selection.constant
              ((m : ℝ) ^ alpha - 1)
              (selectedUniformGoodHeight alpha selection (m : ℝ)) m 0 /
              (m : ℝ)| /
              targetZeroPowerAmplitude beta (m : ℝ) +
            |‖(1 / 2 : ℂ) *
                (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ /
              (m : ℝ)| /
              targetZeroPowerAmplitude beta (m : ℝ))
        atTop (nhds 0) := by
    simpa only [add_zero] using hcontour.add hclosed
  apply hsum.congr'
  filter_upwards
      [eventually_selectedPolynomialContourRelative_nonneg halpha selection,
        eventually_ge_atTop (1 : ℕ)] with m hcontour0 hm
  have hxpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hm)
  let contour : ℝ :=
    cofinalPNTFormulaRemainderBound selection.constant
      ((m : ℝ) ^ alpha - 1)
      (selectedUniformGoodHeight alpha selection (m : ℝ)) m 0 / (m : ℝ)
  let closed : ℝ :=
    ‖(1 / 2 : ℂ) *
      (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ / (m : ℝ)
  have hclosed0 : 0 ≤ closed := by
    dsimp [closed]
    exact div_nonneg (norm_nonneg _) hxpos.le
  have hsum0 : 0 ≤ contour + closed := by
    exact add_nonneg hcontour0 hclosed0
  rw [selectedUniformGoodHeightNaturalRemainderUpperBound, add_div,
    abs_of_nonneg hcontour0, abs_of_nonneg hclosed0,
    abs_of_nonneg hsum0, add_div]

/-- The uniform good-height selector automatically supplies the explicit
majorant certificate under the polynomial exponent conditions. -/
theorem selectedUniformGoodHeightNaturalRemainderMajorantCertificate
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    SelectedUniformGoodHeightNaturalRemainderMajorantCertificate
      beta alpha selection where
  negligible :=
    selectedUniformGoodHeightNaturalRemainderUpperBound_targetNegligible
      hbeta halpha halphaOne hmargin selection

/-- The analytic good-height theorem now constructs the actual selected-height
natural-point remainder certificate with no abstract remainder input. -/
theorem selectedUniformGoodHeight_actualNaturalRemainderCertificate
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ActualSelectedHeightNaturalPointRemainderCertificate beta
      (selectedUniformGoodHeight alpha selection) :=
  (selectedUniformGoodHeightNaturalRemainderMajorantCertificate
    hbeta halpha halphaOne hmargin selection).actualRemainderCertificate
      halpha

end PrimeNumberTheorem
