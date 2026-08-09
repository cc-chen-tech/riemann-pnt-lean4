import HardyTheorem.SelbergSqrtZetaSignedRationalWindowEnergy

open scoped BigOperators

open HardyTheorem

#check sq_sum_norm_mul_thetaFrequencyShortIntegralEnvelope_le
#check norm_sq_integral_selbergSqrtZetaSignedComplexModel_shift_le_rationalEnergy

example {N X : ℕ} (hN : 0 < N) (hX : 0 < X)
    {T H t : ℝ} (hT : 0 < T) (hH : 0 ≤ H) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        ‖selbergSqrtZetaSignedRationalCoeff N X q‖ *
          thetaFrequencyShortIntegralEnvelope
            (selbergSqrtZetaSignedRationalFrequency q) T H t) ^ 2 ≤
      2 *
          (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X q)) *
          (H ^ 2 + 12 * H * ((N * X ^ 2 : ℕ) : ℝ)) +
        2 *
          ((H ^ 3 / (2 * T)) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              ‖selbergSqrtZetaSignedRationalCoeff N X q‖) ^ 2 := by
  exact
    sq_sum_norm_mul_thetaFrequencyShortIntegralEnvelope_le
      hN hX hT hH

example (kappa : ℝ) {X : ℕ} (hX : 0 < X)
    {T H t : ℝ} (hT : 1 ≤ T) (hTt : T ≤ t) (hH : 0 ≤ H) :
    ‖∫ v in 0..H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v)‖ ^ 2 ≤
      2 *
          (∑ q ∈ selbergSqrtZetaSignedRationalSupport
              (firstZetaApproximationCutoff T) X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff
                (firstZetaApproximationCutoff T) X q)) *
          (H ^ 2 + 12 * H *
            (((firstZetaApproximationCutoff T) * X ^ 2 : ℕ) : ℝ)) +
        2 *
          ((H ^ 3 / (2 * T)) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport
                (firstZetaApproximationCutoff T) X,
              ‖selbergSqrtZetaSignedRationalCoeff
                (firstZetaApproximationCutoff T) X q‖) ^ 2 := by
  exact
    norm_sq_integral_selbergSqrtZetaSignedComplexModel_shift_le_rationalEnergy
      kappa hX hT hTt hH

#print axioms
  HardyTheorem.sq_sum_norm_mul_thetaFrequencyShortIntegralEnvelope_le
#print axioms
  HardyTheorem.norm_sq_integral_selbergSqrtZetaSignedComplexModel_shift_le_rationalEnergy
