import HardyTheorem.SelbergSqrtZetaSignedCollectedPhase
import MathlibAux.ExponentialPolynomialShiftedCorrelation

/-!
# Collected correlation expansions for the signed square-root-zeta model

The complex signed model is a Hardy phase times a finite exponential
polynomial indexed by distinct real frequencies.  These identities expose the
ordinary correlation and pseudo-correlation as explicit finite double sums.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The ordinary shifted correlation of the complex signed model, with the
common Hardy phase kept outside the collision-free frequency double sum. -/
theorem selbergSqrtZetaSignedComplexModel_mul_conj_shift_eq
    (kappa T : ℝ) (X : ℕ) (t v w : ℝ) :
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
                (I * (((omega - nu) * t + omega * v - nu * w) : ℂ)) := by
  rw [selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial,
    selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial,
    map_mul]
  rw [show
      (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + v) : ℂ)) *
          selbergSqrtZetaSignedCollectedTriplePolynomial
            (firstZetaApproximationCutoff T) X (t + v)) *
        ((starRingEnd ℂ)
            (Complex.exp (I * kappa) *
              Complex.exp (I * (thetaModel (t + w) : ℂ))) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedCollectedTriplePolynomial
              (firstZetaApproximationCutoff T) X (t + w))) =
        (Complex.exp (I * kappa) *
            Complex.exp (I * (thetaModel (t + v) : ℂ)) *
          (starRingEnd ℂ)
            (Complex.exp (I * kappa) *
              Complex.exp (I * (thetaModel (t + w) : ℂ)))) *
          (selbergSqrtZetaSignedCollectedTriplePolynomial
              (firstZetaApproximationCutoff T) X (t + v) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedCollectedTriplePolynomial
                (firstZetaApproximationCutoff T) X (t + w))) by
      ring]
  unfold selbergSqrtZetaSignedCollectedTriplePolynomial
    selbergSqrtZetaSignedCollectedFrequencySupport
    selbergSqrtZetaSignedCollectedCoeff
    MathlibAux.collectedExponentialPolynomial
  rw [MathlibAux.exponentialPolynomial_mul_conj_shift_eq_double_sum]

/-- The shifted pseudo-correlation of the complex signed model, with its two
Hardy phases kept outside the distinct-frequency double sum. -/
theorem selbergSqrtZetaSignedComplexModel_mul_shift_eq
    (kappa T : ℝ) (X : ℕ) (t v w : ℝ) :
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
                (I * (((omega + nu) * t + omega * v + nu * w) : ℂ)) := by
  rw [selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial,
    selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial]
  rw [show
      (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + v) : ℂ)) *
          selbergSqrtZetaSignedCollectedTriplePolynomial
            (firstZetaApproximationCutoff T) X (t + v)) *
        (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + w) : ℂ)) *
          selbergSqrtZetaSignedCollectedTriplePolynomial
            (firstZetaApproximationCutoff T) X (t + w)) =
        (Complex.exp (I * kappa) *
            Complex.exp (I * (thetaModel (t + v) : ℂ)) *
          (Complex.exp (I * kappa) *
            Complex.exp (I * (thetaModel (t + w) : ℂ)))) *
          (selbergSqrtZetaSignedCollectedTriplePolynomial
              (firstZetaApproximationCutoff T) X (t + v) *
            selbergSqrtZetaSignedCollectedTriplePolynomial
              (firstZetaApproximationCutoff T) X (t + w)) by
      ring]
  unfold selbergSqrtZetaSignedCollectedTriplePolynomial
    selbergSqrtZetaSignedCollectedFrequencySupport
    selbergSqrtZetaSignedCollectedCoeff
    MathlibAux.collectedExponentialPolynomial
  rw [MathlibAux.exponentialPolynomial_mul_shift_eq_double_sum]

/-- The ordinary collected correlation split into its same-frequency main
block and the genuine frequency-gap remainder.  The latter is now in exactly
the form accepted by the Hardy-phase off-diagonal estimate. -/
theorem
    selbergSqrtZetaSignedComplexModel_mul_conj_shift_eq_diagonal_add_offDiagonal
    (kappa T : ℝ) (X : ℕ) (t v w : ℝ) :
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
            (fun omega : ℝ => omega) t) := by
  rw [selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial,
    selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial,
    map_mul]
  rw [show
      (Complex.exp (I * kappa) *
          Complex.exp (I * (thetaModel (t + v) : ℂ)) *
          selbergSqrtZetaSignedCollectedTriplePolynomial
            (firstZetaApproximationCutoff T) X (t + v)) *
        ((starRingEnd ℂ)
            (Complex.exp (I * kappa) *
              Complex.exp (I * (thetaModel (t + w) : ℂ))) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedCollectedTriplePolynomial
              (firstZetaApproximationCutoff T) X (t + w))) =
        (Complex.exp (I * kappa) *
            Complex.exp (I * (thetaModel (t + v) : ℂ)) *
          (starRingEnd ℂ)
            (Complex.exp (I * kappa) *
              Complex.exp (I * (thetaModel (t + w) : ℂ)))) *
          (selbergSqrtZetaSignedCollectedTriplePolynomial
              (firstZetaApproximationCutoff T) X (t + v) *
            (starRingEnd ℂ)
              (selbergSqrtZetaSignedCollectedTriplePolynomial
                (firstZetaApproximationCutoff T) X (t + w))) by
      ring]
  unfold selbergSqrtZetaSignedCollectedTriplePolynomial
    selbergSqrtZetaSignedCollectedFrequencySupport
    selbergSqrtZetaSignedCollectedCoeff
    MathlibAux.collectedExponentialPolynomial
  rw [MathlibAux.exponentialPolynomial_mul_conj_shift_eq_diagonal_add_offDiagonal
    (hfreq := by
      intro omega homega nu hnu h
      exact h)]

end HardyTheorem
