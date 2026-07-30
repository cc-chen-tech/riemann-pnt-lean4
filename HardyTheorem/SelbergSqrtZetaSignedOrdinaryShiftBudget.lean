import HardyTheorem.SelbergSqrtZetaSignedModelShiftDecomposition

/-!
# Complete budget for the ordinary signed-model correlation

The ordinary complex correlation is the sum of its unequal-frequency
remainder and same-frequency diagonal block. This module performs that
decomposition after all three integrations and combines the two existing
sharp budgets.
-/

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The full shift-averaged ordinary correlation is bounded by the collected
unequal-frequency gap budget plus the exact same-frequency collected energy. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedOrdinaryCorrelation_le_energy
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))‖ ≤
      (delta ^ 2 *
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
                ((2 + delta / 2) / |omega - nu|)) +
        delta ^ 2 * (T - delta) *
          ∑ omega ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            Complex.normSq
              (selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega) := by
  have hlong : T ≤ 2 * T - delta := by linarith
  let nuShift : Measure ℝ := volume.restrict (Ioc 0 delta)
  let muHeight : Measure ℝ := volume.restrict (Ioc T (2 * T - delta))
  let muBox : Measure ((ℝ × ℝ) × ℝ) :=
    (nuShift.prod nuShift).prod muHeight
  let Ford : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedOrdinaryShiftKernel kappa T X
  let Frem : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X
  let Fdiag : (ℝ × ℝ) × ℝ → ℂ :=
    selbergSqrtZetaSignedDiagonalShiftKernel T X
  have hord : Integrable Ford muBox := by
    simpa only [Ford, muBox, nuShift, muHeight] using
      integrable_selbergSqrtZetaSignedOrdinaryShiftKernel
        kappa T X hT hroom
  have hrem : Integrable Frem muBox := by
    simpa only [Frem, muBox, nuShift, muHeight] using
      integrable_selbergSqrtZetaSignedCollectedCorrelationShiftKernel
        kappa T X hT hroom
  have hdiag : Integrable Fdiag muBox := by
    simpa only [Fdiag, muBox, nuShift, muHeight] using
      integrable_selbergSqrtZetaSignedDiagonalShiftKernel
        T X hT hroom
  have houterOrd : Integrable
      (fun p : ℝ × ℝ => ∫ t, Ford (p, t) ∂muHeight)
      (nuShift.prod nuShift) :=
    hord.integral_prod_left
  have houterRem : Integrable
      (fun p : ℝ × ℝ => ∫ t, Frem (p, t) ∂muHeight)
      (nuShift.prod nuShift) :=
    hrem.integral_prod_left
  have houterDiag : Integrable
      (fun p : ℝ × ℝ => ∫ t, Fdiag (p, t) ∂muHeight)
      (nuShift.prod nuShift) :=
    hdiag.integral_prod_left
  have hboxSplit :
      (∫ p, Ford p ∂muBox) =
        (∫ p, Frem p ∂muBox) + ∫ p, Fdiag p ∂muBox := by
    calc
      (∫ p, Ford p ∂muBox) =
          ∫ p, Frem p + Fdiag p ∂muBox := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp only [Ford, Frem, Fdiag]
        unfold selbergSqrtZetaSignedOrdinaryShiftKernel
          selbergSqrtZetaSignedCollectedCorrelationShiftKernel
          selbergSqrtZetaSignedDiagonalShiftKernel
        ring
      _ = (∫ p, Frem p ∂muBox) + ∫ p, Fdiag p ∂muBox :=
        integral_add hrem hdiag
  have htripleOrd :
      (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
          selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedComplexModel kappa T X (t + w))) =
        ∫ p, Ford p ∂muBox := by
    calc
      _ = ∫ p, ∫ t, Ford (p, t) ∂muHeight
          ∂nuShift.prod nuShift := by
        rw [integral_prod _ houterOrd]
        simp only [nuShift, muHeight, Ford,
          intervalIntegral.integral_of_le hdelta,
          intervalIntegral.integral_of_le hlong,
          selbergSqrtZetaSignedOrdinaryShiftKernel]
      _ = ∫ p, Ford p ∂muBox := by
        simpa only [muBox] using (integral_prod Ford hord).symm
  have htripleRem :
      (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
          (selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
              (starRingEnd ℂ)
                (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) -
            hardyCorrelationAmplitude v w t *
              selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w)) =
        ∫ p, Frem p ∂muBox := by
    calc
      _ = ∫ p, ∫ t, Frem (p, t) ∂muHeight
          ∂nuShift.prod nuShift := by
        rw [integral_prod _ houterRem]
        simp only [nuShift, muHeight, Frem,
          intervalIntegral.integral_of_le hdelta,
          intervalIntegral.integral_of_le hlong,
          selbergSqrtZetaSignedCollectedCorrelationShiftKernel]
      _ = ∫ p, Frem p ∂muBox := by
        simpa only [muBox] using (integral_prod Frem hrem).symm
  have htripleDiag :
      (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
          hardyCorrelationAmplitude v w t *
            selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w) =
        ∫ p, Fdiag p ∂muBox := by
    calc
      _ = ∫ p, ∫ t, Fdiag (p, t) ∂muHeight
          ∂nuShift.prod nuShift := by
        rw [integral_prod _ houterDiag]
        simp only [nuShift, muHeight, Fdiag,
          intervalIntegral.integral_of_le hdelta,
          intervalIntegral.integral_of_le hlong,
          selbergSqrtZetaSignedDiagonalShiftKernel]
      _ = ∫ p, Fdiag p ∂muBox := by
        simpa only [muBox] using (integral_prod Fdiag hdiag).symm
  rw [htripleOrd, hboxSplit, ← htripleRem, ← htripleDiag]
  exact
    (norm_add_le _ _).trans
      (add_le_add
        (norm_integral_integral_integral_selbergSqrtZetaSignedComplexCorrelation_sub_diagonal_le_coeff
          kappa T X hT hdelta hroom)
        (norm_integral_integral_integral_selbergSqrtZetaSignedCollectedCorrelationDiagonal_le_energy
          T X hT hdelta hroom))

/-- The ordinary-correlation budget with its diagonal term expressed as the
exact square energy of the rationally collected coefficients. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedOrdinaryCorrelation_le_rational_energy
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))‖ ≤
      (delta ^ 2 *
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
                ((2 + delta / 2) / |omega - nu|)) +
        delta ^ 2 * (T - delta) *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport
              (firstZetaApproximationCutoff T) X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff
                (firstZetaApproximationCutoff T) X q) := by
  simpa only [
    sum_normSq_collectedCoeff_eq_rationalCoeff] using
    norm_integral_integral_integral_selbergSqrtZetaSignedOrdinaryCorrelation_le_energy
      kappa T X hT hdelta hroom

/-- Backwards-compatible ordinary-correlation budget obtained by replacing
the exact collected diagonal energy with its raw fiberwise upper bound. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedOrdinaryCorrelation_le
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))‖ ≤
      (delta ^ 2 *
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
                ((2 + delta / 2) / |omega - nu|)) +
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
  let gap : ℝ :=
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
            ((2 + delta / 2) / |omega - nu|)
  let factor : ℝ := delta ^ 2 * (T - delta)
  have hfactor : 0 ≤ factor := by
    dsimp only [factor]
    exact mul_nonneg (sq_nonneg delta) (sub_nonneg.mpr hroom)
  have hdiag :
      factor *
          (∑ omega ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            Complex.normSq
              (selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega)) ≤
        factor *
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
              Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) :=
    mul_le_mul_of_nonneg_left
      (sum_normSq_selbergSqrtZetaSignedCollectedCoeff_le_fiber_budget
        (firstZetaApproximationCutoff T) X)
      hfactor
  calc
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))‖ ≤
      gap + factor *
        ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          Complex.normSq
            (selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X omega) := by
      simpa only [gap, factor] using
        norm_integral_integral_integral_selbergSqrtZetaSignedOrdinaryCorrelation_le_energy
          kappa T X hT hdelta hroom
    _ ≤ gap + factor *
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
            Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) :=
      add_le_add_right hdiag gap
    _ = _ := by rfl

end HardyTheorem
