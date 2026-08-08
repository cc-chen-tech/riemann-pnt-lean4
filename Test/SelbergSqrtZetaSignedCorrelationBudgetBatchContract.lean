import HardyTheorem.OscillatoryIntegral
import HardyTheorem.SelbergSqrtZetaSignedCollectedGapBound
import HardyTheorem.SelbergSqrtZetaSignedPseudoPhase
import HardyTheorem.SelbergSqrtZetaSignedCollectedEnergy
import HardyTheorem.SelbergSqrtZetaSignedCollectedShiftBudget
import HardyTheorem.SelbergSqrtZetaSignedPseudoShiftBudget
import HardyTheorem.SelbergSqrtZetaSignedCollectedL1

open Complex MeasureTheory Set HardyTheorem
open scoped BigOperators

example {F : ℝ → ℝ} {a b r : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hsecond : (∀ x ∈ Icc a b, r ≤ iteratedDeriv 2 F x) ∨
      (∀ x ∈ Icc a b, iteratedDeriv 2 F x ≤ -r)) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 12 / Real.sqrt r :=
  OscillatoryIntegral.norm_integral_cexp_phase_le_of_second_deriv_on_Icc
    hab hr hF hsecond

noncomputable example (T : ℝ) (X : ℕ) (v w : ℝ) : ℂ :=
  selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w

noncomputable example (T : ℝ) (X : ℕ) (v w t : ℝ) : ℂ :=
  selbergSqrtZetaSignedCollectedCorrelationOffDiagonal T X v w t

example (kappa t v w : ℝ) :
    Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + v) : ℂ)) *
        (starRingEnd ℂ)
          (Complex.exp (I * kappa) *
            Complex.exp (I * (thetaModel (t + w) : ℂ))) =
      hardyCorrelationAmplitude v w t :=
  selbergSqrtZetaSignedCommonCorrelationPhase_eq kappa t v w

example (kappa T : ℝ) (X : ℕ) (t v w : ℝ) :
    selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
        (starRingEnd ℂ)
          (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) =
      hardyCorrelationAmplitude v w t *
        (selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w +
          selbergSqrtZetaSignedCollectedCorrelationOffDiagonal T X v w t) :=
  selbergSqrtZetaSignedComplexModel_mul_conj_shift_eq_diagonal_add_offDiagonal'
    kappa T X t v w

example (kappa T : ℝ) (X : ℕ) {delta v w : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T)
    (hv : v ∈ Icc 0 delta) (hw : w ∈ Icc 0 delta) :
    ‖∫ t in T..2 * T - delta,
        (selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) -
          hardyCorrelationAmplitude v w t *
            selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w)‖ ≤
      ∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        ∑ nu ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          if omega = nu then 0
          else
            ‖selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega *
              Complex.exp (I * ((omega * v : ℝ) : ℂ))‖ *
            ‖(starRingEnd ℂ)
                (selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X nu) *
              Complex.exp (-I * ((nu * w : ℝ) : ℂ))‖ *
            ((2 + delta / 2) / |omega - nu|) :=
  norm_integral_selbergSqrtZetaSignedComplexCorrelation_sub_diagonal_le
    kappa T X hT hdelta hroom hv hw

example (kappa T : ℝ) (X : ℕ) {delta v w : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T)
    (hv : v ∈ Icc 0 delta) (hw : w ∈ Icc 0 delta) :
    ‖∫ t in T..2 * T - delta,
        (selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) -
          hardyCorrelationAmplitude v w t *
            selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w)‖ ≤
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
            ((2 + delta / 2) / |omega - nu|) :=
  norm_integral_selbergSqrtZetaSignedComplexCorrelation_sub_diagonal_le_coeff
    kappa T X hT hdelta hroom hv hw

noncomputable example (omega nu v w t : ℝ) : ℝ :=
  selbergSqrtZetaSignedPseudoPhase omega nu v w t

example {omega nu v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    ContDiffAt ℝ 2
      (selbergSqrtZetaSignedPseudoPhase omega nu v w) t :=
  contDiffAt_selbergSqrtZetaSignedPseudoPhase_two htv htw

example {omega nu v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    iteratedDeriv 2
        (selbergSqrtZetaSignedPseudoPhase omega nu v w) t =
      1 / (2 * (t + v)) + 1 / (2 * (t + w)) :=
  iteratedDeriv_two_selbergSqrtZetaSignedPseudoPhase htv htw

example {T delta v w omega nu : ℝ}
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T)
    (hv : v ∈ Icc 0 delta) (hw : w ∈ Icc 0 delta) :
    ‖∫ t in T..2 * T - delta,
        Complex.exp
          (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t)‖ ≤
      12 * Real.sqrt (4 * T) :=
  norm_integral_cexp_selbergSqrtZetaSignedPseudoPhase_le
    hT hdelta hroom hv hw

noncomputable example
    (kappa T : ℝ) (X : ℕ) (v w omega nu : ℝ) : ℂ :=
  selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu

example (kappa T : ℝ) (X : ℕ) {t v w : ℝ}
    (htv : 0 < t + v) (htw : 0 < t + w) :
    selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
        selbergSqrtZetaSignedComplexModel kappa T X (t + w) =
      ∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        ∑ nu ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          selbergSqrtZetaSignedPseudoCoeff kappa T X v w omega nu *
            Complex.exp
              (I * selbergSqrtZetaSignedPseudoPhase omega nu v w t) :=
  selbergSqrtZetaSignedComplexModel_mul_shift_eq_sum_pseudoPhase
    kappa T X htv htw

example (kappa : ℝ) {T delta : ℝ} (X : ℕ)
    (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T)
    {v w : ℝ} (hv : v ∈ Icc 0 delta) (hw : w ∈ Icc 0 delta) :
    ‖∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)‖ ≤
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
                (firstZetaApproximationCutoff T) X nu‖) :=
  norm_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le
    kappa X hT hdelta hroom hv hw

example (N X : ℕ) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        Complex.normSq
          (selbergSqrtZetaSignedCollectedCoeff N X omega)) ≤
      ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        (((selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
        ∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
          Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) :=
  sum_normSq_selbergSqrtZetaSignedCollectedCoeff_le_fiber_budget N X

example (T : ℝ) (X : ℕ) (v w : ℝ) :
    ‖selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w‖ ≤
      ∑ omega ∈
          selbergSqrtZetaSignedCollectedFrequencySupport
            (firstZetaApproximationCutoff T) X,
        Complex.normSq
          (selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega) :=
  norm_selbergSqrtZetaSignedCollectedCorrelationDiagonal_le_energy T X v w

example (T : ℝ) (X : ℕ) (v w : ℝ) :
    ‖selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w‖ ≤
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
  norm_selbergSqrtZetaSignedCollectedCorrelationDiagonal_le_fiber_budget
    T X v w

noncomputable example
    (kappa T : ℝ) (X : ℕ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X p

example (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hroom : delta ≤ T) :
    Integrable
      (selbergSqrtZetaSignedCollectedCorrelationShiftKernel kappa T X)
      (((volume.restrict (Ioc 0 delta)).prod
          (volume.restrict (Ioc 0 delta))).prod
        (volume.restrict (Ioc T (2 * T - delta)))) :=
  integrable_selbergSqrtZetaSignedCollectedCorrelationShiftKernel
    kappa T X hT hroom

example (kappa T : ℝ) (X : ℕ) {delta : ℝ}
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
              ((2 + delta / 2) / |omega - nu|) :=
  norm_integral_integral_integral_selbergSqrtZetaSignedComplexCorrelation_sub_diagonal_le_coeff
    kappa T X hT hdelta hroom

noncomputable example
    (kappa T : ℝ) (X : ℕ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  selbergSqrtZetaSignedPseudoShiftKernel kappa T X p

example (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hroom : delta ≤ T) :
    Integrable
      (selbergSqrtZetaSignedPseudoShiftKernel kappa T X)
      (((volume.restrict (Ioc 0 delta)).prod
          (volume.restrict (Ioc 0 delta))).prod
        (volume.restrict (Ioc T (2 * T - delta)))) :=
  integrable_selbergSqrtZetaSignedPseudoShiftKernel kappa T X hT hroom

example (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)) =
      ∫ t in T..2 * T - delta, ∫ v in 0..delta, ∫ w in 0..delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w) :=
  selbergSqrtZetaSignedPseudoShiftKernel_fubini
    kappa T X hT hdelta hroom

example (kappa : ℝ) {T delta : ℝ} (X : ℕ)
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
                  (firstZetaApproximationCutoff T) X nu‖) :=
  norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le
    kappa X hT hdelta hroom

example (N X : ℕ) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        ‖selbergSqrtZetaSignedCollectedCoeff N X omega‖) ^ 2 ≤
      ((selbergSqrtZetaSignedCollectedFrequencySupport N X).card : ℝ) *
        ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedCollectedCoeff N X omega) :=
  sq_sum_norm_selbergSqrtZetaSignedCollectedCoeff_le_card_mul_energy N X

example (N X : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        ∑ nu ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          C * (‖selbergSqrtZetaSignedCollectedCoeff N X omega‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff N X nu‖)) ≤
      C * ((selbergSqrtZetaSignedCollectedFrequencySupport N X).card : ℝ) *
        ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedCollectedCoeff N X omega) :=
  sum_sum_mul_norm_selbergSqrtZetaSignedCollectedCoeff_le_card_mul_energy
    N X hC

example (N X : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        ∑ nu ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          C * (‖selbergSqrtZetaSignedCollectedCoeff N X omega‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff N X nu‖)) ≤
      C * ((selbergSqrtZetaSignedCollectedFrequencySupport N X).card : ℝ) *
        ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          (((selbergSqrtZetaSignedPhaseSupport N X).filter
            (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
          ∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
            (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
            Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) :=
  sum_sum_mul_norm_selbergSqrtZetaSignedCollectedCoeff_le_fiber_budget
    N X hC
