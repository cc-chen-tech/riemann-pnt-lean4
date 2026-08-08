import HardyTheorem.HardyPhaseHilbert
import HardyTheorem.SelbergSqrtZetaSignedCollectedCorrelation

/-!
# Frequency-gap bound for the collected signed model

After equal frequencies have been collected, the ordinary shifted
correlation has a same-frequency main block and a genuine off-diagonal
remainder.  This module identifies the common phase with the Hardy
correlation amplitude and applies the existing integration-by-parts gap
estimate to that remainder.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The same-frequency block of the collected ordinary correlation. -/
noncomputable def selbergSqrtZetaSignedCollectedCorrelationDiagonal
    (T : ℝ) (X : ℕ) (v w : ℝ) : ℂ :=
  ∑ omega ∈
      selbergSqrtZetaSignedCollectedFrequencySupport
        (firstZetaApproximationCutoff T) X,
    selbergSqrtZetaSignedCollectedCoeff
        (firstZetaApproximationCutoff T) X omega *
      (starRingEnd ℂ)
        (selbergSqrtZetaSignedCollectedCoeff
          (firstZetaApproximationCutoff T) X omega) *
      Complex.exp (I * ((omega * v - omega * w : ℝ) : ℂ))

/-- The genuine unequal-frequency part of the collected ordinary
correlation. -/
noncomputable def selbergSqrtZetaSignedCollectedCorrelationOffDiagonal
    (T : ℝ) (X : ℕ) (v w t : ℝ) : ℂ :=
  MathlibAux.exponentialOffDiagonalForm
    (selbergSqrtZetaSignedCollectedFrequencySupport
      (firstZetaApproximationCutoff T) X)
    (fun omega =>
      selbergSqrtZetaSignedCollectedCoeff
          (firstZetaApproximationCutoff T) X omega *
        Complex.exp (I * ((omega * v : ℝ) : ℂ)))
    (fun nu =>
      (starRingEnd ℂ)
          (selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X nu) *
        Complex.exp (-I * ((nu * w : ℝ) : ℂ)))
    (fun omega : ℝ => omega) t

/-- The constant `kappa` cancels from the ordinary correlation, leaving
exactly the common Hardy phase difference. -/
theorem selbergSqrtZetaSignedCommonCorrelationPhase_eq
    (kappa t v w : ℝ) :
    Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + v) : ℂ)) *
        (starRingEnd ℂ)
          (Complex.exp (I * kappa) *
            Complex.exp (I * (thetaModel (t + w) : ℂ))) =
      hardyCorrelationAmplitude v w t := by
  unfold hardyCorrelationAmplitude
  rw [map_mul, ← Complex.exp_conj, ← Complex.exp_conj]
  simp only [map_mul, conj_I, conj_ofReal]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Pointwise collected ordinary correlation as Hardy amplitude times its
same-frequency and unequal-frequency blocks. -/
theorem
    selbergSqrtZetaSignedComplexModel_mul_conj_shift_eq_diagonal_add_offDiagonal'
    (kappa T : ℝ) (X : ℕ) (t v w : ℝ) :
    selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
        (starRingEnd ℂ)
          (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) =
      hardyCorrelationAmplitude v w t *
        (selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w +
          selbergSqrtZetaSignedCollectedCorrelationOffDiagonal T X v w t) := by
  rw [
    selbergSqrtZetaSignedComplexModel_mul_conj_shift_eq_diagonal_add_offDiagonal,
    selbergSqrtZetaSignedCommonCorrelationPhase_eq]
  rfl

/-- Removing the same-frequency block leaves an integral controlled by the
explicit reciprocal-frequency gap sum. -/
theorem
    norm_integral_selbergSqrtZetaSignedComplexCorrelation_sub_diagonal_le
    (kappa T : ℝ) (X : ℕ) {delta v w : ℝ}
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
            ((2 + delta / 2) / |omega - nu|) := by
  have hpoint :
      (fun t : ℝ =>
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) -
          hardyCorrelationAmplitude v w t *
            selbergSqrtZetaSignedCollectedCorrelationDiagonal T X v w) =
        fun t : ℝ =>
          hardyCorrelationAmplitude v w t *
            selbergSqrtZetaSignedCollectedCorrelationOffDiagonal
              T X v w t := by
    funext t
    rw [
      selbergSqrtZetaSignedComplexModel_mul_conj_shift_eq_diagonal_add_offDiagonal']
    ring
  rw [hpoint]
  unfold selbergSqrtZetaSignedCollectedCorrelationOffDiagonal
  simpa only using
    (norm_integral_hardyCorrelationAmplitude_mul_exponentialOffDiagonal_le
      (selbergSqrtZetaSignedCollectedFrequencySupport
        (firstZetaApproximationCutoff T) X)
      (fun omega =>
        selbergSqrtZetaSignedCollectedCoeff
            (firstZetaApproximationCutoff T) X omega *
          Complex.exp (I * ((omega * v : ℝ) : ℂ)))
      (fun nu =>
        (starRingEnd ℂ)
            (selbergSqrtZetaSignedCollectedCoeff
              (firstZetaApproximationCutoff T) X nu) *
          Complex.exp (-I * ((nu * w : ℝ) : ℂ)))
      (fun omega : ℝ => omega)
      hT hdelta hroom hv hw)

/-- The shift phases have unit norm, so the off-diagonal integral is
controlled purely by the collected coefficients and reciprocal frequency
gaps. -/
theorem
    norm_integral_selbergSqrtZetaSignedComplexCorrelation_sub_diagonal_le_coeff
    (kappa T : ℝ) (X : ℕ) {delta v w : ℝ}
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
            ((2 + delta / 2) / |omega - nu|) := by
  have hpos (x : ℝ) :
      ‖Complex.exp (I * (x : ℂ))‖ = 1 :=
    Complex.norm_exp_I_mul_ofReal x
  have hneg (x : ℝ) :
      ‖Complex.exp (-I * (x : ℂ))‖ = 1 := by
    rw [show -I * (x : ℂ) = I * ((-x : ℝ) : ℂ) by
      push_cast
      ring]
    exact Complex.norm_exp_I_mul_ofReal (-x)
  simpa only [norm_mul, hpos, hneg, mul_one, Complex.norm_conj] using
    (norm_integral_selbergSqrtZetaSignedComplexCorrelation_sub_diagonal_le
      kappa T X hT hdelta hroom hv hw)

end HardyTheorem
