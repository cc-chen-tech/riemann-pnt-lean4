import HardyTheorem.SelbergSqrtZetaSignedCollectedGapBound
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Shift-averaged collected correlation budget

The fixed-shift collected frequency-gap estimate is uniform for
`v, w ∈ [0, delta]`.  This module proves the three-variable kernel is
Bochner integrable on the compact shift-height box and integrates the
fixed-shift estimate over the two shift variables.  The resulting cost is
exactly the square area `delta ^ 2`.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The collected ordinary-correlation remainder as a function of the two
shift variables and the long height variable. -/
noncomputable def selbergSqrtZetaSignedCollectedCorrelationShiftKernel
    (kappa T : ℝ) (X : ℕ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  selbergSqrtZetaSignedComplexModel kappa T X (p.2 + p.1.1) *
      (starRingEnd ℂ)
        (selbergSqrtZetaSignedComplexModel kappa T X (p.2 + p.1.2)) -
    hardyCorrelationAmplitude p.1.1 p.1.2 p.2 *
      selbergSqrtZetaSignedCollectedCorrelationDiagonal
        T X p.1.1 p.1.2

private theorem
    continuousAt_selbergSqrtZetaSignedCollectedCorrelationShiftKernel
    (kappa T : ℝ) (X : ℕ) {p : (ℝ × ℝ) × ℝ}
    (htv : 0 < p.2 + p.1.1) (htw : 0 < p.2 + p.1.2) :
    ContinuousAt
      (selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X) p := by
  have hthetaV : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ => thetaModel (q.2 + q.1.1)) p := by
    change ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ =>
        (q.2 + q.1.1) / 2 *
            Real.log ((q.2 + q.1.1) / (2 * Real.pi)) -
          (q.2 + q.1.1) / 2 - Real.pi / 8) p
    fun_prop (disch := positivity)
  have hthetaW : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ => thetaModel (q.2 + q.1.2)) p := by
    change ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ =>
        (q.2 + q.1.2) / 2 *
            Real.log ((q.2 + q.1.2) / (2 * Real.pi)) -
          (q.2 + q.1.2) / 2 - Real.pi / 8) p
    fun_prop (disch := positivity)
  have hamp : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ =>
        hardyCorrelationAmplitude q.1.1 q.1.2 q.2) p := by
    unfold hardyCorrelationAmplitude
    exact
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp
          (hthetaV.sub hthetaW))).cexp
  have hoff : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ =>
        selbergSqrtZetaSignedCollectedCorrelationOffDiagonal
          T X q.1.1 q.1.2 q.2) p := by
    unfold selbergSqrtZetaSignedCollectedCorrelationOffDiagonal
      MathlibAux.exponentialOffDiagonalForm
    apply tendsto_finset_sum
    intro omega homega
    apply tendsto_finset_sum
    intro nu hnu
    by_cases hfreq : omega = nu
    · simp [hfreq]
    · simp only [hfreq, ↓reduceIte]
      have hleft : ContinuousAt
          (fun q : (ℝ × ℝ) × ℝ =>
            selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega *
              Complex.exp (I * ((omega * q.1.1 : ℝ) : ℂ))) p := by
        fun_prop
      have hright : ContinuousAt
          (fun q : (ℝ × ℝ) × ℝ =>
            (starRingEnd ℂ)
                (selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X nu) *
              Complex.exp (-I * ((nu * q.1.2 : ℝ) : ℂ))) p := by
        fun_prop
      have hosc : ContinuousAt
          (fun q : (ℝ × ℝ) × ℝ =>
            Complex.exp
              (I * (((omega - nu) * q.2 : ℝ) : ℂ))) p := by
        fun_prop
      simpa only [ofReal_sub, ofReal_mul] using
        (hleft.mul hright).mul hosc
  have hproduct : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ =>
        hardyCorrelationAmplitude q.1.1 q.1.2 q.2 *
          selbergSqrtZetaSignedCollectedCorrelationOffDiagonal
            T X q.1.1 q.1.2 q.2) p :=
    hamp.mul hoff
  apply hproduct.congr_of_eventuallyEq
  filter_upwards with q
  unfold selbergSqrtZetaSignedCollectedCorrelationShiftKernel
  rw [
    selbergSqrtZetaSignedComplexModel_mul_conj_shift_eq_diagonal_add_offDiagonal']
  ring

/-- The collected correlation remainder is Bochner integrable on the compact
shift-height box used by the shift-averaged estimate. -/
theorem integrable_selbergSqrtZetaSignedCollectedCorrelationShiftKernel
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (_hroom : delta ≤ T) :
    Integrable
      (selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X)
      (((volume.restrict (Ioc 0 delta)).prod
          (volume.restrict (Ioc 0 delta))).prod
        (volume.restrict (Ioc T (2 * T - delta)))) := by
  let box : Set ((ℝ × ℝ) × ℝ) :=
    (Icc 0 delta ×ˢ Icc 0 delta) ×ˢ Icc T (2 * T - delta)
  have hcompact : IsCompact box :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hcontinuous : ContinuousOn
      (selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X) box := by
    intro p hp
    exact
      (continuousAt_selbergSqrtZetaSignedCollectedCorrelationShiftKernel
        kappa T X
        (by linarith [hT, hp.2.1, hp.1.1.1])
        (by linarith [hT, hp.2.1, hp.1.2.1])).continuousWithinAt
  have hbox : IntegrableOn
      (selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X) box
      ((volume.prod volume).prod volume) :=
    hcontinuous.integrableOn_compact hcompact
  have hsmall : IntegrableOn
      (selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X)
      ((Ioc 0 delta ×ˢ Ioc 0 delta) ×ˢ Ioc T (2 * T - delta))
      ((volume.prod volume).prod volume) :=
    hbox.mono_set <| Set.prod_mono
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      Ioc_subset_Icc_self
  simpa only [Measure.prod_restrict, IntegrableOn] using hsmall

/-- Averaging the fixed-shift collected gap estimate over
`[0, delta]²` costs exactly the area `delta²`. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedComplexCorrelation_sub_diagonal_le_coeff
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        (selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) -
          hardyCorrelationAmplitude v w t *
            selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w)‖ ≤
      delta ^ 2 *
        ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          ∑ nu ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            if omega = nu then 0
            else
              ‖selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega‖ *
              ‖selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X nu‖ *
              ((2 + delta / 2) / |omega - nu|) := by
  have hlong : T ≤ 2 * T - delta := by linarith
  let nuShift : Measure ℝ := volume.restrict (Ioc 0 delta)
  let muHeight : Measure ℝ := volume.restrict (Ioc T (2 * T - delta))
  let F : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X
  let B : ℝ :=
    ∑ omega ∈
        selbergSqrtZetaSignedCollectedFrequencySupport
          (firstZetaApproximationCutoff T) X,
      ∑ nu ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        if omega = nu then 0
        else
          ‖selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega‖ *
          ‖selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X nu‖ *
          ((2 + delta / 2) / |omega - nu|)
  have hF : Integrable F ((nuShift.prod nuShift).prod muHeight) := by
    simpa only [nuShift, muHeight, F] using
      (integrable_selbergSqrtZetaSignedCollectedCorrelationShiftKernel
        kappa T X hT hroom)
  have houter : Integrable
      (fun p : ℝ × ℝ => ∫ t, F (p, t) ∂muHeight)
      (nuShift.prod nuShift) :=
    hF.integral_prod_left
  have hpoint : ∀ᵐ p ∂nuShift.prod nuShift,
      ‖∫ t, F (p, t) ∂muHeight‖ ≤ B := by
    dsimp only [nuShift]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hv : p.1 ∈ Icc 0 delta := ⟨le_of_lt hp.1.1, hp.1.2⟩
    have hw : p.2 ∈ Icc 0 delta := ⟨le_of_lt hp.2.1, hp.2.2⟩
    simpa only [muHeight, F, B, intervalIntegral.integral_of_le hlong,
      selbergSqrtZetaSignedCollectedCorrelationShiftKernel] using
      norm_integral_selbergSqrtZetaSignedComplexCorrelation_sub_diagonal_le_coeff
        kappa T X hT hdelta hroom hv hw
  have hmeasure : (nuShift.prod nuShift).real Set.univ = delta ^ 2 := by
    dsimp only [nuShift]
    rw [Measure.prod_restrict, measureReal_def,
      Measure.restrict_apply_univ, Measure.prod_prod,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hdelta]
    ring
  calc
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        (selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) -
          hardyCorrelationAmplitude v w t *
            selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w)‖ =
        ‖∫ p, ∫ t, F (p, t) ∂muHeight ∂nuShift.prod nuShift‖ := by
      rw [integral_prod _ houter]
      simp only [nuShift, muHeight, F,
        intervalIntegral.integral_of_le hdelta,
        intervalIntegral.integral_of_le hlong,
        selbergSqrtZetaSignedCollectedCorrelationShiftKernel]
    _ ≤ B * (nuShift.prod nuShift).real Set.univ :=
      norm_integral_le_of_norm_le_const hpoint
    _ = delta ^ 2 * B := by rw [hmeasure]; ring
    _ = delta ^ 2 *
        ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          ∑ nu ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            if omega = nu then 0
            else
              ‖selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega‖ *
              ‖selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X nu‖ *
              ((2 + delta / 2) / |omega - nu|) := rfl

end HardyTheorem
