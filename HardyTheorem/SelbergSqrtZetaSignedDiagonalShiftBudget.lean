import HardyTheorem.SelbergSqrtZetaSignedCollectedEnergy
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Shift-averaged signed diagonal correlation budget

The same-frequency block of the collected ordinary correlation is uniformly
bounded by the exact raw frequency-fiber multiplicity energy. This module
proves joint integrability on the shift-height box and integrates that bound
over both shifts and the long height interval.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The same-frequency ordinary-correlation block as a function of the two
shift variables and the long height variable. -/
noncomputable def selbergSqrtZetaSignedDiagonalShiftKernel
    (T : ℝ) (X : ℕ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  hardyCorrelationAmplitude p.1.1 p.1.2 p.2 *
    selbergSqrtZetaSignedCollectedCorrelationDiagonal T X p.1.1 p.1.2

private theorem continuousAt_selbergSqrtZetaSignedDiagonalShiftKernel
    (T : ℝ) (X : ℕ) {p : (ℝ × ℝ) × ℝ}
    (htv : 0 < p.2 + p.1.1) (htw : 0 < p.2 + p.1.2) :
    ContinuousAt (selbergSqrtZetaSignedDiagonalShiftKernel T X) p := by
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
  have hdiag : ContinuousAt
      (fun q : (ℝ × ℝ) × ℝ =>
        selbergSqrtZetaSignedCollectedCorrelationDiagonal
          T X q.1.1 q.1.2) p := by
    unfold selbergSqrtZetaSignedCollectedCorrelationDiagonal
    apply tendsto_finset_sum
    intro omega homega
    have hphase : ContinuousAt
        (fun q : (ℝ × ℝ) × ℝ =>
          omega * q.1.1 - omega * q.1.2) p :=
      (continuousAt_const.mul continuous_fst.fst.continuousAt).sub
        (continuousAt_const.mul continuous_fst.snd.continuousAt)
    exact
      (continuousAt_const.mul continuousAt_const).mul
        ((continuousAt_const.mul
          (Complex.continuous_ofReal.continuousAt.comp hphase)).cexp)
  exact hamp.mul hdiag

/-- The same-frequency diagonal kernel is Bochner integrable on the compact
shift-height box. -/
theorem integrable_selbergSqrtZetaSignedDiagonalShiftKernel
    (T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (_hroom : delta ≤ T) :
    Integrable
      (selbergSqrtZetaSignedDiagonalShiftKernel T X)
      (((volume.restrict (Ioc 0 delta)).prod
          (volume.restrict (Ioc 0 delta))).prod
        (volume.restrict (Ioc T (2 * T - delta)))) := by
  let box : Set ((ℝ × ℝ) × ℝ) :=
    (Icc 0 delta ×ˢ Icc 0 delta) ×ˢ Icc T (2 * T - delta)
  have hcompact : IsCompact box :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hcontinuous : ContinuousOn
      (selbergSqrtZetaSignedDiagonalShiftKernel T X) box := by
    intro p hp
    exact
      (continuousAt_selbergSqrtZetaSignedDiagonalShiftKernel
        T X
        (by linarith [hT, hp.2.1, hp.1.1.1])
        (by linarith [hT, hp.2.1, hp.1.2.1])).continuousWithinAt
  have hbox : IntegrableOn
      (selbergSqrtZetaSignedDiagonalShiftKernel T X) box
      ((volume.prod volume).prod volume) :=
    hcontinuous.integrableOn_compact hcompact
  have hsmall : IntegrableOn
      (selbergSqrtZetaSignedDiagonalShiftKernel T X)
      ((Ioc 0 delta ×ˢ Ioc 0 delta) ×ˢ Ioc T (2 * T - delta))
      ((volume.prod volume).prod volume) :=
    hbox.mono_set <| Set.prod_mono
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      Ioc_subset_Icc_self
  simpa only [Measure.prod_restrict, IntegrableOn] using hsmall

/-- The threefold integral of the same-frequency ordinary-correlation block
is bounded by the shift area, the height length, and the exact raw
frequency-fiber multiplicity energy. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedCollectedCorrelationDiagonal_le_fiber_budget
    (T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        hardyCorrelationAmplitude v w t *
          selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w‖ ≤
      delta ^ 2 * (T - delta) *
        ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          (((selbergSqrtZetaSignedPhaseSupport
              (firstZetaApproximationCutoff T) X).filter
            (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
          ∑ p ∈
              (selbergSqrtZetaSignedPhaseSupport
                (firstZetaApproximationCutoff T) X).filter
                (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
            Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) := by
  have hlong : T ≤ 2 * T - delta := by linarith
  have hheightNonneg : 0 ≤ T - delta := sub_nonneg.mpr hroom
  let nuShift : Measure ℝ := volume.restrict (Ioc 0 delta)
  let muHeight : Measure ℝ := volume.restrict (Ioc T (2 * T - delta))
  let muBox : Measure ((ℝ × ℝ) × ℝ) :=
    (nuShift.prod nuShift).prod muHeight
  let F : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedDiagonalShiftKernel T X
  let B : ℝ :=
    ∑ omega ∈
        selbergSqrtZetaSignedCollectedFrequencySupport
          (firstZetaApproximationCutoff T) X,
      (((selbergSqrtZetaSignedPhaseSupport
          (firstZetaApproximationCutoff T) X).filter
        (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
      ∑ p ∈
          (selbergSqrtZetaSignedPhaseSupport
            (firstZetaApproximationCutoff T) X).filter
            (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
        Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p)
  have hF : Integrable F muBox := by
    simpa only [nuShift, muHeight, muBox, F] using
      (integrable_selbergSqrtZetaSignedDiagonalShiftKernel
        T X hT hroom)
  have houter : Integrable
      (fun p : ℝ × ℝ => ∫ t, F (p, t) ∂muHeight)
      (nuShift.prod nuShift) := by
    simpa only [muBox] using hF.integral_prod_left
  have hnormAmplitude (v w t : ℝ) :
      ‖hardyCorrelationAmplitude v w t‖ = 1 := by
    unfold hardyCorrelationAmplitude
    exact Complex.norm_exp_I_mul_ofReal
      (thetaModel (t + v) - thetaModel (t + w))
  have hpoint : ∀ᵐ p ∂muBox, ‖F p‖ ≤ B := by
    filter_upwards with p
    dsimp only [F, selbergSqrtZetaSignedDiagonalShiftKernel]
    rw [norm_mul, hnormAmplitude, one_mul]
    exact
      norm_selbergSqrtZetaSignedCollectedCorrelationDiagonal_le_fiber_budget
        T X p.1.1 p.1.2
  have hshiftMeasure :
      (nuShift.prod nuShift).real Set.univ = delta ^ 2 := by
    dsimp only [nuShift]
    rw [Measure.prod_restrict, measureReal_def,
      Measure.restrict_apply_univ, Measure.prod_prod,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hdelta]
    ring
  have hheightMeasure :
      muHeight.real Set.univ = T - delta := by
    dsimp only [muHeight]
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
      show 2 * T - delta - T = T - delta by ring,
      ENNReal.toReal_ofReal hheightNonneg]
  have hboxMeasure :
      muBox.real Set.univ = delta ^ 2 * (T - delta) := by
    dsimp only [muBox]
    rw [measureReal_def,
      show (Set.univ : Set ((ℝ × ℝ) × ℝ)) =
          Set.univ ×ˢ Set.univ by ext; simp,
      Measure.prod_prod, ENNReal.toReal_mul]
    change
      (nuShift.prod nuShift).real Set.univ *
          muHeight.real Set.univ =
        delta ^ 2 * (T - delta)
    rw [hshiftMeasure, hheightMeasure]
  calc
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        hardyCorrelationAmplitude v w t *
          selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w‖ =
        ‖∫ p, ∫ t, F (p, t) ∂muHeight ∂nuShift.prod nuShift‖ := by
      rw [integral_prod _ houter]
      simp only [nuShift, muHeight, F,
        intervalIntegral.integral_of_le hdelta,
        intervalIntegral.integral_of_le hlong,
        selbergSqrtZetaSignedDiagonalShiftKernel]
    _ = ‖∫ p, F p ∂muBox‖ := by
      congr 1
      simpa only [muBox] using (integral_prod F hF).symm
    _ ≤ B * muBox.real Set.univ :=
      norm_integral_le_of_norm_le_const hpoint
    _ = delta ^ 2 * (T - delta) * B := by
      rw [hboxMeasure]
      ring
    _ = delta ^ 2 * (T - delta) *
        ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          (((selbergSqrtZetaSignedPhaseSupport
              (firstZetaApproximationCutoff T) X).filter
            (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
          ∑ p ∈
              (selbergSqrtZetaSignedPhaseSupport
                (firstZetaApproximationCutoff T) X).filter
                (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
            Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) := rfl

end HardyTheorem
