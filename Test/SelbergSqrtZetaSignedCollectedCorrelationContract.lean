import HardyTheorem.SelbergSqrtZetaSignedCollectedCorrelation

open Complex HardyTheorem
open scoped BigOperators

example (kappa T : ℝ) (X : ℕ) (t v w : ℝ) :
    selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
        (starRingEnd ℂ)
          (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) =
      (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + v) : ℂ)) *
        (starRingEnd ℂ)
          (Complex.exp (I * kappa) *
            Complex.exp (I * (thetaModel (t + w) : ℂ)))) *
        ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          ∑ nu ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega *
              (starRingEnd ℂ)
                (selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X nu) *
              Complex.exp
                (I * (((omega - nu) * t + omega * v - nu * w) : ℂ)) :=
  selbergSqrtZetaSignedComplexModel_mul_conj_shift_eq kappa T X t v w

example (kappa T : ℝ) (X : ℕ) (t v w : ℝ) :
    selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
        selbergSqrtZetaSignedComplexModel kappa T X (t + w) =
      (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + v) : ℂ)) *
        (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + w) : ℂ)))) *
        ∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
          ∑ nu ∈
              selbergSqrtZetaSignedCollectedFrequencySupport
                (firstZetaApproximationCutoff T) X,
            selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega *
              selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X nu *
              Complex.exp
                (I * (((omega + nu) * t + omega * v + nu * w) : ℂ)) :=
  selbergSqrtZetaSignedComplexModel_mul_shift_eq kappa T X t v w

example (kappa T : ℝ) (X : ℕ) (t v w : ℝ) :
    selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
        (starRingEnd ℂ)
          (selbergSqrtZetaSignedComplexModel kappa T X (t + w)) =
      (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + v) : ℂ)) *
        (starRingEnd ℂ)
          (Complex.exp (I * kappa) *
            Complex.exp (I * (thetaModel (t + w) : ℂ)))) *
        ((∑ omega ∈
            selbergSqrtZetaSignedCollectedFrequencySupport
              (firstZetaApproximationCutoff T) X,
            selbergSqrtZetaSignedCollectedCoeff
                (firstZetaApproximationCutoff T) X omega *
              (starRingEnd ℂ)
                (selbergSqrtZetaSignedCollectedCoeff
                  (firstZetaApproximationCutoff T) X omega) *
              Complex.exp
                (I * ((omega * v - omega * w : ℝ) : ℂ))) +
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
            (fun omega : ℝ => omega) t) :=
  selbergSqrtZetaSignedComplexModel_mul_conj_shift_eq_diagonal_add_offDiagonal
    kappa T X t v w
