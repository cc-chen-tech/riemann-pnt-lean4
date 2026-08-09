import HardyTheorem.SelbergSqrtZetaSignedRationalWindow

/-!
# Exact rational model for signed Selberg short windows

The short integral of the finite complex Selberg model is a constant unitary
phase times a finite sum indexed by the positive rational frequencies
`l / (m*d)`.  This file packages that exact sum and identifies its pointwise
and integrated square energy with the original finite model.  No termwise
absolute values or frequency-separation estimates are used.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- The exact rational-frequency finite model for one signed short window. -/
noncomputable def selbergSqrtZetaSignedRationalShortModel
    (T : ℝ) (X : ℕ) (H t : ℝ) : ℂ :=
  ∑ q ∈ selbergSqrtZetaSignedRationalSupport
      (firstZetaApproximationCutoff T) X,
    selbergSqrtZetaSignedRationalCoeff
        (firstZetaApproximationCutoff T) X q *
      thetaFrequencyShortIntegral
        (selbergSqrtZetaSignedRationalFrequency q) H t

/-- The finite complex-model short integral is exactly a constant unitary
phase times the rational short model. -/
theorem integral_selbergSqrtZetaSignedComplexModel_shift_eq_rationalShortModel
    (kappa T : ℝ) (X : ℕ) {H t : ℝ}
    (ht : 0 < t) (hH : 0 ≤ H) :
    (∫ v in 0..H,
      selbergSqrtZetaSignedComplexModel kappa T X (t + v)) =
      Complex.exp (I * kappa) *
        selbergSqrtZetaSignedRationalShortModel T X H t := by
  simpa only [selbergSqrtZetaSignedRationalShortModel] using
    integral_selbergSqrtZetaSignedComplexModel_shift_eq_sum_thetaFrequencyShortIntegral
      kappa T X ht hH

/-- The constant phase disappears from the pointwise short-window energy. -/
theorem
    normSq_integral_selbergSqrtZetaSignedComplexModel_shift_eq_rationalShortModel
    (kappa T : ℝ) (X : ℕ) {H t : ℝ}
    (ht : 0 < t) (hH : 0 ≤ H) :
    Complex.normSq
        (∫ v in 0..H,
          selbergSqrtZetaSignedComplexModel kappa T X (t + v)) =
      Complex.normSq
        (selbergSqrtZetaSignedRationalShortModel T X H t) := by
  rw [
    integral_selbergSqrtZetaSignedComplexModel_shift_eq_rationalShortModel
      kappa T X ht hH,
    Complex.normSq_mul, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_I_mul_ofReal]
  norm_num

/-- On any positive height interval, the integrated finite-model short-window
energy is exactly the integrated rational short-model energy. -/
theorem
    integral_normSq_integral_selbergSqrtZetaSignedComplexModel_shift_eq_rationalShortModel
    (kappa T : ℝ) (X : ℕ) {H a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hH : 0 ≤ H) :
    (∫ t in a..b,
        Complex.normSq
          (∫ v in 0..H,
            selbergSqrtZetaSignedComplexModel kappa T X (t + v))) =
      ∫ t in a..b,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact
    normSq_integral_selbergSqrtZetaSignedComplexModel_shift_eq_rationalShortModel
      kappa T X (ha.trans_le ht.1) hH

end HardyTheorem
