import HardyTheorem.SelbergSqrtZetaSignedPseudoPhase
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Shift-averaged signed pseudo-correlation budget

The fixed-shift signed pseudo-correlation estimate is uniform for
`v, w ∈ [0, delta]`. This module proves that the corresponding
three-variable kernel is Bochner integrable on the compact shift-height box
and integrates the fixed-shift estimate over both shift variables. The
resulting cost is exactly `delta ^ 2`.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The signed pseudo-correlation as a function of the two shift variables
and the long height variable. -/
noncomputable def selbergSqrtZetaSignedPseudoShiftKernel
    (kappa T : ℝ) (X : ℕ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  selbergSqrtZetaSignedComplexModel kappa T X (p.2 + p.1.1) *
    selbergSqrtZetaSignedComplexModel kappa T X (p.2 + p.1.2)

private theorem continuousAt_selbergSqrtZetaSignedPseudoShiftKernel
    (kappa T : ℝ) (X : ℕ) {p : (ℝ × ℝ) × ℝ}
    (htv : 0 < p.2 + p.1.1) (htw : 0 < p.2 + p.1.2) :
    ContinuousAt (selbergSqrtZetaSignedPseudoShiftKernel kappa T X) p := by
  have hargV : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.1) p :=
    (continuous_snd.add continuous_fst.fst).continuousAt
  have hargW : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.2) p :=
    (continuous_snd.add continuous_fst.snd).continuousAt
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
  have hmodelV : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ =>
        selbergSqrtZetaSignedComplexModel kappa T X
          (q.2 + q.1.1)) p := by
    unfold selbergSqrtZetaSignedComplexModel
      selbergSqrtZetaSignedPhasePolynomial
    apply continuousAt_const.mul
    apply tendsto_finset_sum
    intro a ha
    exact continuousAt_const.mul <|
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp
          (hthetaV.add (continuousAt_const.mul hargV)))).cexp
  have hmodelW : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ =>
        selbergSqrtZetaSignedComplexModel kappa T X
          (q.2 + q.1.2)) p := by
    unfold selbergSqrtZetaSignedComplexModel
      selbergSqrtZetaSignedPhasePolynomial
    apply continuousAt_const.mul
    apply tendsto_finset_sum
    intro a ha
    exact continuousAt_const.mul <|
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp
          (hthetaW.add (continuousAt_const.mul hargW)))).cexp
  exact hmodelV.mul hmodelW

/-- The signed pseudo-correlation kernel is Bochner integrable on the compact
shift-height box used by the shift-averaged estimate. -/
theorem integrable_selbergSqrtZetaSignedPseudoShiftKernel
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (_hroom : delta ≤ T) :
    Integrable
      (selbergSqrtZetaSignedPseudoShiftKernel kappa T X)
      (((volume.restrict (Ioc 0 delta)).prod
          (volume.restrict (Ioc 0 delta))).prod
        (volume.restrict (Ioc T (2 * T - delta)))) := by
  let box : Set ((ℝ × ℝ) × ℝ) :=
    (Icc 0 delta ×ˢ Icc 0 delta) ×ˢ Icc T (2 * T - delta)
  have hcompact : IsCompact box :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hcontinuous : ContinuousOn
      (selbergSqrtZetaSignedPseudoShiftKernel kappa T X) box := by
    intro p hp
    exact
      (continuousAt_selbergSqrtZetaSignedPseudoShiftKernel
        kappa T X
        (by linarith [hT, hp.2.1, hp.1.1.1])
        (by linarith [hT, hp.2.1, hp.1.2.1])).continuousWithinAt
  have hbox : IntegrableOn
      (selbergSqrtZetaSignedPseudoShiftKernel kappa T X) box
      ((volume.prod volume).prod volume) :=
    hcontinuous.integrableOn_compact hcompact
  have hsmall : IntegrableOn
      (selbergSqrtZetaSignedPseudoShiftKernel kappa T X)
      ((Ioc 0 delta ×ˢ Ioc 0 delta) ×ˢ Ioc T (2 * T - delta))
      ((volume.prod volume).prod volume) :=
    hbox.mono_set <| Set.prod_mono
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      Ioc_subset_Icc_self
  simpa only [Measure.prod_restrict, IntegrableOn] using hsmall

/-- Fubini for the signed pseudo-correlation on the compact
shift-height box. -/
theorem selbergSqrtZetaSignedPseudoShiftKernel_fubini
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)) =
      ∫ t in T..2 * T - delta, ∫ v in 0..delta, ∫ w in 0..delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w) := by
  have hlong : T ≤ 2 * T - delta := by linarith
  let nuShift : Measure ℝ := volume.restrict (Ioc 0 delta)
  let muHeight : Measure ℝ := volume.restrict (Ioc T (2 * T - delta))
  let F : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedPseudoShiftKernel kappa T X
  have hF : Integrable F ((nuShift.prod nuShift).prod muHeight) := by
    simpa only [nuShift, muHeight, F] using
      (integrable_selbergSqrtZetaSignedPseudoShiftKernel
        kappa T X hT hroom)
  have hswap :
      (∫ p, ∫ t, F (p, t) ∂muHeight ∂nuShift.prod nuShift) =
        ∫ t, ∫ p, F (p, t) ∂nuShift.prod nuShift ∂muHeight :=
    integral_integral_swap hF
  calc
    (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)) =
        ∫ p, ∫ t, F (p, t) ∂muHeight ∂nuShift.prod nuShift := by
      rw [integral_prod _ hF.integral_prod_left]
      simp only [nuShift, muHeight, F,
        intervalIntegral.integral_of_le hdelta,
        intervalIntegral.integral_of_le hlong,
        selbergSqrtZetaSignedPseudoShiftKernel]
    _ = ∫ t, ∫ p, F (p, t) ∂nuShift.prod nuShift ∂muHeight := hswap
    _ = ∫ t in T..2 * T - delta, ∫ v in 0..delta, ∫ w in 0..delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w) := by
      rw [intervalIntegral.integral_of_le hlong]
      apply integral_congr_ae
      filter_upwards [hF.prod_left_ae] with t ht
      rw [integral_prod _ ht]
      simp only [nuShift, F, intervalIntegral.integral_of_le hdelta,
        selbergSqrtZetaSignedPseudoShiftKernel]

/-- Averaging the fixed-shift signed pseudo-correlation estimate over
`[0, delta]²` costs exactly the area `delta²`. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le
    (kappa : ℝ) {T delta : ℝ} (X : ℕ)
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)‖ ≤
      delta ^ 2 *
        ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          ∑ nu ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            (12 * Real.sqrt (4 * T)) *
              (‖selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X omega‖ *
                ‖selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X nu‖) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlong : T ≤ 2 * T - delta := by linarith
  let nuShift : Measure ℝ := volume.restrict (Ioc 0 delta)
  let muHeight : Measure ℝ := volume.restrict (Ioc T (2 * T - delta))
  let F : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedPseudoShiftKernel kappa T X
  let B : ℝ :=
    ∑ omega ∈
        selbergSqrtZetaSignedCollectedFrequencySupport
          (firstZetaApproximationCutoff T) X,
      ∑ nu ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        (12 * Real.sqrt (4 * T)) *
          (‖selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X omega‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X nu‖)
  have hF : Integrable F ((nuShift.prod nuShift).prod muHeight) := by
    simpa only [nuShift, muHeight, F] using
      (integrable_selbergSqrtZetaSignedPseudoShiftKernel
        kappa T X hTpos hroom)
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
      selbergSqrtZetaSignedPseudoShiftKernel] using
      norm_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le
        kappa X hT hdelta hroom hv hw
  have hmeasure : (nuShift.prod nuShift).real Set.univ = delta ^ 2 := by
    dsimp only [nuShift]
    rw [Measure.prod_restrict, measureReal_def,
      Measure.restrict_apply_univ, Measure.prod_prod,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hdelta]
    ring
  calc
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)‖ =
        ‖∫ p, ∫ t, F (p, t) ∂muHeight ∂nuShift.prod nuShift‖ := by
      rw [integral_prod _ houter]
      simp only [nuShift, muHeight, F,
        intervalIntegral.integral_of_le hdelta,
        intervalIntegral.integral_of_le hlong,
        selbergSqrtZetaSignedPseudoShiftKernel]
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
            (12 * Real.sqrt (4 * T)) *
              (‖selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X omega‖ *
                ‖selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X nu‖) := rfl

end HardyTheorem
