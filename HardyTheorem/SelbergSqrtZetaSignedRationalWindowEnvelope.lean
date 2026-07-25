import HardyTheorem.SelbergSqrtZetaSignedRationalWindow

/-!
# Stationary-safe rational-frequency envelope for the Selberg model

The exact rational short-window expansion is bounded termwise.  A frequency
at exact stationary phase uses the window-length estimate; every other
frequency uses reciprocal-frequency decay plus the theta linearization error.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The explicit coefficient-weighted short-window envelope for the complex
signed Selberg model. -/
noncomputable def selbergSqrtZetaSignedRationalWindowEnvelopeSum
    (T : ℝ) (X : ℕ) (H t : ℝ) : ℝ :=
  ∑ q ∈ selbergSqrtZetaSignedRationalSupport
      (firstZetaApproximationCutoff T) X,
    ‖selbergSqrtZetaSignedRationalCoeff
        (firstZetaApproximationCutoff T) X q‖ *
      thetaFrequencyShortIntegralEnvelope
        (selbergSqrtZetaSignedRationalFrequency q) T H t

/-- The short-window integral of the full complex signed Selberg model is
bounded by the stationary-safe rational-frequency envelope sum. -/
theorem
    norm_integral_selbergSqrtZetaSignedComplexModel_shift_le_rationalWindowEnvelopeSum
    (kappa : ℝ) (X : ℕ) {T H t : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hH : 0 ≤ H) :
    ‖∫ v in 0..H,
      selbergSqrtZetaSignedComplexModel kappa T X (t + v)‖ ≤
      selbergSqrtZetaSignedRationalWindowEnvelopeSum T X H t := by
  rw [
    integral_selbergSqrtZetaSignedComplexModel_shift_eq_sum_thetaFrequencyShortIntegral
      kappa T X (hT.trans_le hTt) hH,
    norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  unfold selbergSqrtZetaSignedRationalWindowEnvelopeSum
  calc
    ‖∑ q ∈ selbergSqrtZetaSignedRationalSupport
          (firstZetaApproximationCutoff T) X,
        selbergSqrtZetaSignedRationalCoeff
            (firstZetaApproximationCutoff T) X q *
          thetaFrequencyShortIntegral
            (selbergSqrtZetaSignedRationalFrequency q) H t‖ ≤
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport
            (firstZetaApproximationCutoff T) X,
          ‖selbergSqrtZetaSignedRationalCoeff
              (firstZetaApproximationCutoff T) X q *
            thetaFrequencyShortIntegral
              (selbergSqrtZetaSignedRationalFrequency q) H t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ selbergSqrtZetaSignedRationalSupport
          (firstZetaApproximationCutoff T) X,
        ‖selbergSqrtZetaSignedRationalCoeff
            (firstZetaApproximationCutoff T) X q‖ *
          thetaFrequencyShortIntegralEnvelope
            (selbergSqrtZetaSignedRationalFrequency q) T H t := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_thetaFrequencyShortIntegral_le_envelope
          (selbergSqrtZetaSignedRationalFrequency q) hT hTt hH)
        (norm_nonneg _)

end HardyTheorem
