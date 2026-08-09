import HardyTheorem.SelbergSqrtZetaSignedRationalShortModel
import MathlibAux.SlidingIntegralFourierEnergy

/-!
# Fourier transfer for the signed rational short model

The finite signed theta-phase polynomial is cut off to the dyadic interval
`[T, 2T]`.  On starts in `[T, 2T-H]`, its genuine sliding integral is exactly
the rational short model.  The generic sliding-window Parseval estimate then
reduces its second moment to low- and high-frequency Fourier energy.
-/

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace HardyTheorem

/-- The signed theta-phase polynomial, extended by zero outside `[T, 2T]`. -/
noncomputable def selbergSqrtZetaSignedTruncatedPhase
    (T : ℝ) (X : ℕ) : ℝ → ℂ :=
  (Icc T (2 * T)).indicator
    (selbergSqrtZetaSignedPhasePolynomial
      (firstZetaApproximationCutoff T) X)

private theorem continuousOn_selbergSqrtZetaSignedPhasePolynomial_Icc
    (T : ℝ) (X : ℕ) (hT : 0 < T) :
    ContinuousOn
      (selbergSqrtZetaSignedPhasePolynomial
        (firstZetaApproximationCutoff T) X)
      (Icc T (2 * T)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold selbergSqrtZetaSignedPhasePolynomial
  apply tendsto_finset_sum
  intro p hp
  have htpos : 0 < t := hT.trans_le ht.1
  have htheta : ContinuousAt thetaModel t := by
    change ContinuousAt (fun x : ℝ =>
      x / 2 * Real.log (x / (2 * Real.pi)) - x / 2 - Real.pi / 8) t
    fun_prop (disch := positivity)
  have hphase : ContinuousAt (fun x : ℝ =>
      thetaModel x + selbergSqrtZetaSignedPhaseFrequency p * x) t :=
    htheta.add (continuousAt_const.mul continuousAt_id)
  exact continuousAt_const.mul
    ((continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp hphase)).cexp)

/-- The dyadically truncated phase polynomial is integrable. -/
theorem integrable_selbergSqrtZetaSignedTruncatedPhase
    (T : ℝ) (X : ℕ) (hT : 0 < T) :
    Integrable (selbergSqrtZetaSignedTruncatedPhase T X) := by
  unfold selbergSqrtZetaSignedTruncatedPhase
  exact
    ((continuousOn_selbergSqrtZetaSignedPhasePolynomial_Icc T X hT
      ).integrableOn_compact isCompact_Icc).integrable_indicator
        measurableSet_Icc

/-- The dyadically truncated phase polynomial belongs to `L²`. -/
theorem memLp_two_selbergSqrtZetaSignedTruncatedPhase
    (T : ℝ) (X : ℕ) (hT : 0 < T) :
    MemLp (selbergSqrtZetaSignedTruncatedPhase T X) 2 := by
  let f : ℝ → ℂ :=
    selbergSqrtZetaSignedPhasePolynomial
      (firstZetaApproximationCutoff T) X
  let s : Set ℝ := Icc T (2 * T)
  have hfCont : ContinuousOn f s := by
    simpa only [f, s] using
      continuousOn_selbergSqrtZetaSignedPhasePolynomial_Icc T X hT
  have hsqOn : IntegrableOn (fun t => ‖f t‖ ^ 2) s := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_norm.comp_continuousOn hfCont).pow 2
  have hsq :
      Integrable (s.indicator fun t => ‖f t‖ ^ 2) :=
    hsqOn.integrable_indicator measurableSet_Icc
  have hF1 :=
    integrable_selbergSqrtZetaSignedTruncatedPhase T X hT
  apply
    (memLp_two_iff_integrable_sq_norm hF1.aestronglyMeasurable).2
  apply hsq.congr
  filter_upwards with t
  by_cases ht : t ∈ s
  · simp [selbergSqrtZetaSignedTruncatedPhase, s, f, ht]
  · simp [selbergSqrtZetaSignedTruncatedPhase, s, f, ht]

/-- On an admissible start, the sliding integral of the truncated phase is
exactly the signed rational short model. -/
theorem
    integral_selbergSqrtZetaSignedTruncatedPhase_eq_rationalShortModel
    (T : ℝ) (X : ℕ) {H t : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H)
    (ht : t ∈ Icc T (2 * T - H)) :
    (∫ u in t..t + H,
      selbergSqrtZetaSignedTruncatedPhase T X u) =
      selbergSqrtZetaSignedRationalShortModel T X H t := by
  have htpos : 0 < t := hT.trans_le ht.1
  calc
    (∫ u in t..t + H,
        selbergSqrtZetaSignedTruncatedPhase T X u) =
        ∫ v in 0..H,
          selbergSqrtZetaSignedTruncatedPhase T X (v + t) := by
      have hshift := intervalIntegral.integral_comp_add_right
        (selbergSqrtZetaSignedTruncatedPhase T X) t
        (a := 0) (b := H)
      simpa only [zero_add, add_comm H t] using hshift.symm
    _ =
        ∫ v in 0..H,
          selbergSqrtZetaSignedTruncatedPhase T X (t + v) := by
      apply intervalIntegral.integral_congr
      intro v _hv
      simp only [add_comm v t]
    _ = ∫ v in 0..H,
        selbergSqrtZetaSignedPhasePolynomial
          (firstZetaApproximationCutoff T) X (t + v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hvIcc : v ∈ Icc (0 : ℝ) H := by
        simpa [uIcc_of_le hH] using hv
      have htv : t + v ∈ Icc T (2 * T) := by
        constructor
        · exact ht.1.trans (le_add_of_nonneg_right hvIcc.1)
        · linarith [ht.2, hvIcc.2]
      exact indicator_of_mem htv _
    _ = selbergSqrtZetaSignedRationalShortModel T X H t := by
      simpa only [selbergSqrtZetaSignedRationalShortModel] using
        integral_selbergSqrtZetaSignedPhasePolynomial_shift_eq_sum_thetaFrequencyShortIntegral
          (firstZetaApproximationCutoff T) X htpos hH

/-- Parseval transfer for the exact signed rational short model.  All
remaining work is now in the low- and high-frequency Fourier energies of the
compactly supported phase polynomial. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_fourier_low_high
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 < H) (hroom : H ≤ T) :
    (∫ t in T..2 * T - H,
      Complex.normSq
        (selbergSqrtZetaSignedRationalShortModel T X H t)) ≤
      H ^ 2 * (∫ y : ℝ in {y | |y| ≤ 1 / H},
        ‖(𝓕
          ((memLp_two_selbergSqrtZetaSignedTruncatedPhase T X hT).toLp
            (selbergSqrtZetaSignedTruncatedPhase T X)) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) +
      4 * (∫ y : ℝ in {y | 1 / H < |y|},
        ‖(𝓕
          ((memLp_two_selbergSqrtZetaSignedTruncatedPhase T X hT).toLp
            (selbergSqrtZetaSignedTruncatedPhase T X)) :
          Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) := by
  have hab : T ≤ 2 * T - H := by linarith
  let F : ℝ → ℂ := selbergSqrtZetaSignedTruncatedPhase T X
  let hF1 : Integrable F :=
    integrable_selbergSqrtZetaSignedTruncatedPhase T X hT
  let hF2 : MemLp F 2 :=
    memLp_two_selbergSqrtZetaSignedTruncatedPhase T X hT
  have hparseval :=
    MathlibAux.integral_normSq_slidingIntegral_le_fourier_low_high
      hF1 hF2 hH hab
  have hleft :
      (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) =
        ∫ t in T..2 * T - H,
          Complex.normSq (∫ u in t..t + H, F u) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Icc T (2 * T - H) := by
      simpa [uIcc_of_le hab] using ht
    change
      Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t) =
        Complex.normSq
          (∫ u in t..t + H,
            selbergSqrtZetaSignedTruncatedPhase T X u)
    rw [integral_selbergSqrtZetaSignedTruncatedPhase_eq_rationalShortModel
      T X hT hH.le htIcc]
  rw [hleft]
  simpa only [F, hF2] using hparseval

end HardyTheorem
