import HardyTheorem.SelbergSqrtZetaSignedRationalWindow

open Complex
open HardyTheorem

#check selbergSqrtZetaSignedPhasePolynomial_eq_sum_rational_thetaFrequency
#check integral_selbergSqrtZetaSignedPhasePolynomial_shift_eq_sum_thetaFrequencyShortIntegral
#check integral_selbergSqrtZetaSignedComplexModel_shift_eq_sum_thetaFrequencyShortIntegral

example (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedPhasePolynomial N X t =
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        selbergSqrtZetaSignedRationalCoeff N X q *
          Complex.exp
            (I * ((thetaModel t +
              selbergSqrtZetaSignedRationalFrequency q * t : ℝ) : ℂ)) :=
  selbergSqrtZetaSignedPhasePolynomial_eq_sum_rational_thetaFrequency
    N X t

example (N X : ℕ) {H t : ℝ} (ht : 0 < t) (hH : 0 ≤ H) :
    (∫ v in 0..H,
      selbergSqrtZetaSignedPhasePolynomial N X (t + v)) =
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        selbergSqrtZetaSignedRationalCoeff N X q *
          thetaFrequencyShortIntegral
            (selbergSqrtZetaSignedRationalFrequency q) H t :=
  integral_selbergSqrtZetaSignedPhasePolynomial_shift_eq_sum_thetaFrequencyShortIntegral
    N X ht hH

example (kappa T : ℝ) (X : ℕ) {H t : ℝ}
    (ht : 0 < t) (hH : 0 ≤ H) :
    (∫ v in 0..H,
      selbergSqrtZetaSignedComplexModel kappa T X (t + v)) =
      Complex.exp (I * kappa) *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport
            (firstZetaApproximationCutoff T) X,
          selbergSqrtZetaSignedRationalCoeff
              (firstZetaApproximationCutoff T) X q *
            thetaFrequencyShortIntegral
              (selbergSqrtZetaSignedRationalFrequency q) H t :=
  integral_selbergSqrtZetaSignedComplexModel_shift_eq_sum_thetaFrequencyShortIntegral
    kappa T X ht hH

#print axioms
  integral_selbergSqrtZetaSignedPhasePolynomial_shift_eq_sum_thetaFrequencyShortIntegral
#print axioms
  integral_selbergSqrtZetaSignedComplexModel_shift_eq_sum_thetaFrequencyShortIntegral
