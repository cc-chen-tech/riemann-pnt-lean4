import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpFullPNT
import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeBarrier

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

noncomputable def classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio
    (D rate beta : ℝ) (m : ℕ) : ℝ :=
  classicalDyadicCarlsonThetaSqrtLogMajorant D rate (1 / 2) m /
    targetZeroPowerAmplitude beta (m : ℝ)

lemma classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio_eq
    (D rate beta : ℝ) {m : ℕ} (hm : 0 < m) :
    classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio
        D rate beta m =
      Real.exp (Real.log D - 3 * Real.log rate) *
        (1 + pntSqrtLog m) ^ 11 *
        pntContourKernelToTargetAmplitudeRatio beta (rate / 2) m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  unfold classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio
  rw [classicalDyadicCarlsonThetaSqrtLogMajorant_eq]
  unfold pntContourKernelToTargetAmplitudeRatio
    targetZeroPowerAmplitude
  rw [Real.rpow_def_of_pos hmR]
  rw [show Real.log (m : ℝ) * (beta - 1) =
      (beta - 1) * Real.log (m : ℝ) by ring]
  rw [show -((1 / 2) * rate) * pntSqrtLog m =
      -(rate / 2) * pntSqrtLog m by ring]
  ring

theorem classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio_tendsto_atTop
    (D rate : ℝ) {beta : ℝ} (hbeta : beta < 1) :
    Tendsto
      (classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio D rate beta)
      atTop atTop := by
  let K : ℝ := Real.exp (Real.log D - 3 * Real.log rate)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hbase :=
    pntContourKernelToTargetAmplitudeRatio_tendsto_atTop
      hbeta (rate / 2)
  have hscaled : Tendsto
      (fun m : ℕ =>
        K * pntContourKernelToTargetAmplitudeRatio beta (rate / 2) m)
      atTop atTop :=
    hbase.const_mul_atTop hK
  rw [tendsto_atTop]
  intro A
  filter_upwards [
      hscaled.eventually (eventually_ge_atTop A),
      eventually_ge_atTop (1 : ℕ)] with m hlarge hm
  rw [classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio_eq
    D rate beta (Nat.zero_lt_of_lt hm)]
  have hs : 0 ≤ pntSqrtLog m := Real.sqrt_nonneg _
  have hpow : 1 ≤ (1 + pntSqrtLog m) ^ 11 :=
    one_le_pow₀ (by linarith)
  have hbasePos :
      0 < pntContourKernelToTargetAmplitudeRatio
        beta (rate / 2) m := by
    unfold pntContourKernelToTargetAmplitudeRatio
    positivity
  calc
    A ≤ K * pntContourKernelToTargetAmplitudeRatio
        beta (rate / 2) m := hlarge
    _ = (K * 1) *
        pntContourKernelToTargetAmplitudeRatio beta (rate / 2) m := by
      ring
    _ ≤ (K * (1 + pntSqrtLog m) ^ 11) *
        pntContourKernelToTargetAmplitudeRatio beta (rate / 2) m :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hK.le) hbasePos.le
    _ = Real.exp (Real.log D - 3 * Real.log rate) *
        (1 + pntSqrtLog m) ^ 11 *
        pntContourKernelToTargetAmplitudeRatio beta (rate / 2) m := by
      simp [K]

lemma classicalSevenEighthsLowMajorant_nonneg_of_nonneg
    {C kappa : ℝ} (hC : 0 ≤ C) (hkappa : 0 < kappa) (m : ℕ) :
    0 ≤ classicalSevenEighthsLowMajorant C kappa m := by
  unfold classicalSevenEighthsLowMajorant
    actualHybridLowNormalizedLogPowerMajorant
  positivity

lemma classicalCriticalHalfMajorant_nonneg_of_nonneg
    {C kappa : ℝ} (hC : 0 ≤ C) (hkappa : 0 < kappa) (m : ℕ) :
    0 ≤ classicalCriticalHalfMajorant C kappa m := by
  unfold classicalCriticalHalfMajorant
    actualHybridLowNormalizedLogPowerMajorant
  positivity

lemma classicalAdmissibleClosedFormNaturalRemainderMajorant_nonneg
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection) (m : ℕ) :
    0 ≤ classicalAdmissibleClosedFormNaturalRemainderMajorant
      b selection m := by
  have hselection : 0 ≤ selection.constant := selection.constant_nonneg
  have htail : 0 ≤ cofinalPNTZeroDepthTailConstant :=
    cofinalPNTZeroDepthTailConstant_nonneg
  have hsqrt : 0 ≤ pntSqrtLog m := Real.sqrt_nonneg _
  have hmain : 0 ≤
      26 * selection.constant * pntSqrtLog m ^ 4 *
        Real.exp (-(classicalAdmissibleBalancedRate b) * pntSqrtLog m) := by
    positivity
  have htailTerm : 0 ≤
      2 * cofinalPNTZeroDepthTailConstant * pntSqrtLog m / (m : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) htail)
        hsqrt)
      (Nat.cast_nonneg m)
  have hclosed : 0 ≤
      ‖(1 / 2 : ℂ) *
        (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ / (m : ℝ) := by
    exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg m)
  unfold classicalAdmissibleClosedFormNaturalRemainderMajorant
    cofinalPNTZeroDepthRelativeRemainderMajorant
    classicalClosedLogRelativeMajorant
  exact add_nonneg (add_nonneg hmain htailTerm) hclosed

lemma classicalDyadicCarlsonThetaHalfKernel_le_closedFormFullPNTErrorMajorant
    {E eta C kappa D rate : ℝ}
    (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection) (m : ℕ) :
    classicalDyadicCarlsonThetaSqrtLogMajorant D rate (1 / 2) m ≤
      classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant
        b selection E eta C kappa D rate m := by
  have htheta :
      0 ≤ classicalDyadicCarlsonThetaSqrtLogMajorant
        D rate (1 / 2) m := by
    unfold classicalDyadicCarlsonThetaSqrtLogMajorant
    positivity
  have hlow :=
    classicalSevenEighthsLowMajorant_nonneg_of_nonneg hC hkappa m
  have hcritical :=
    classicalCriticalHalfMajorant_nonneg_of_nonneg hE heta m
  have hreal := classicalRealOrdinateFixedMajorant_nonneg m
  have haxis :
      0 ≤ |actualPNTClosedRealAxisRelativeTerm (m : ℝ)| := abs_nonneg _
  have hremainder :=
    classicalAdmissibleClosedFormNaturalRemainderMajorant_nonneg
      b selection m
  unfold classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant
    classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
    classicalDyadicCarlsonThetaFullZeroTailMajorant
    classicalDyadicCarlsonThetaPositiveZeroTailMajorant
    classicalDyadicCarlsonThetaMiddleMajorant
  linarith

noncomputable def
    classicalDyadicCarlsonHalfClosedFormFullPNTToTargetAmplitudeRatio
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (E eta C kappa D rate beta : ℝ) (m : ℕ) : ℝ :=
  classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant
      b selection E eta C kappa D rate m /
    targetZeroPowerAmplitude beta (m : ℝ)

theorem
    classicalDyadicCarlsonHalfClosedFormFullPNTToTargetAmplitudeRatio_tendsto_atTop
    {E eta C kappa : ℝ}
    (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (D rate : ℝ) {beta : ℝ} (hbeta : beta < 1) :
    Tendsto
      (classicalDyadicCarlsonHalfClosedFormFullPNTToTargetAmplitudeRatio
        b selection E eta C kappa D rate beta)
      atTop atTop := by
  have hkernel :=
    classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio_tendsto_atTop
      D rate hbeta
  rw [tendsto_atTop]
  intro A
  filter_upwards [
      hkernel.eventually (eventually_ge_atTop A),
      eventually_ge_atTop (1 : ℕ)] with m hlarge hm
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hamplitude :
      0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    Real.rpow_pos_of_pos hmR _
  have hratio :
      classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio
          D rate beta m ≤
        classicalDyadicCarlsonHalfClosedFormFullPNTToTargetAmplitudeRatio
          b selection E eta C kappa D rate beta m := by
    unfold classicalDyadicCarlsonThetaHalfToTargetAmplitudeRatio
      classicalDyadicCarlsonHalfClosedFormFullPNTToTargetAmplitudeRatio
    exact (div_le_div_iff_of_pos_right hamplitude).2
      (classicalDyadicCarlsonThetaHalfKernel_le_closedFormFullPNTErrorMajorant
        hE heta hC hkappa b selection m)
  exact hlarge.trans hratio

theorem
    not_eventually_classicalDyadicCarlsonHalfClosedFormFullPNTMajorant_le_mul_targetAmplitude
    {E eta C kappa : ℝ}
    (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (D rate : ℝ) {beta : ℝ} (hbeta : beta < 1) (q : ℝ) :
    ¬ ∀ᶠ m : ℕ in atTop,
        classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant
            b selection E eta C kappa D rate m ≤
          q * targetZeroPowerAmplitude beta (m : ℝ) := by
  intro hbound
  have hratio :=
    classicalDyadicCarlsonHalfClosedFormFullPNTToTargetAmplitudeRatio_tendsto_atTop
      hE heta hC hkappa b selection D rate hbeta
  have hlarge : ∀ᶠ m : ℕ in atTop,
      q <
        classicalDyadicCarlsonHalfClosedFormFullPNTToTargetAmplitudeRatio
          b selection E eta C kappa D rate beta m :=
    hratio.eventually (eventually_gt_atTop q)
  rcases
      (hbound.and (hlarge.and (eventually_ge_atTop (1 : ℕ)))).exists with
    ⟨m, hboundM, hlargeM, hm⟩
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hamplitude :
      0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    Real.rpow_pos_of_pos hmR _
  have hratioLe :
      classicalDyadicCarlsonHalfClosedFormFullPNTToTargetAmplitudeRatio
          b selection E eta C kappa D rate beta m ≤ q := by
    unfold
      classicalDyadicCarlsonHalfClosedFormFullPNTToTargetAmplitudeRatio
    exact (div_le_iff₀ hamplitude).2 hboundM
  linarith

end PrimeNumberTheorem
