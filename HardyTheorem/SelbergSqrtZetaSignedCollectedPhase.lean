import HardyTheorem.SelbergSqrtZetaSignedModelCorrelation
import MathlibAux.CollectedExponentialPolynomial

/-!
# Collected signed phase polynomial for the square-root-zeta mollifier

The raw signed triple support contains distinct triples with the same real
frequency.  This module collects their coefficients before any frequency-gap
estimate is applied.  The resulting support is a finite set of real
frequencies, so every off-diagonal denominator is genuinely nonzero.
-/

open Complex

namespace HardyTheorem

/-- The distinct real frequencies occurring in the signed triple model. -/
noncomputable def selbergSqrtZetaSignedCollectedFrequencySupport
    (N X : ℕ) : Finset ℝ :=
  MathlibAux.collectedFrequencySupport
    (selbergSqrtZetaSignedPhaseSupport N X)
    selbergSqrtZetaSignedPhaseFrequency

/-- The coefficient obtained by summing all signed triples at one frequency. -/
noncomputable def selbergSqrtZetaSignedCollectedCoeff
    (N X : ℕ) (omega : ℝ) : ℂ :=
  MathlibAux.collectedCoefficient
    (selbergSqrtZetaSignedPhaseSupport N X)
    (selbergSqrtZetaSignedPhaseCoeff X)
    selbergSqrtZetaSignedPhaseFrequency omega

/-- The signed triple polynomial reindexed by its distinct real frequencies. -/
noncomputable def selbergSqrtZetaSignedCollectedTriplePolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.collectedExponentialPolynomial
    (selbergSqrtZetaSignedPhaseSupport N X)
    (selbergSqrtZetaSignedPhaseCoeff X)
    selbergSqrtZetaSignedPhaseFrequency t

/-- Collecting equal-frequency triples preserves the signed triple polynomial
exactly. -/
theorem
    selbergSqrtZetaSignedCollectedTriplePolynomial_eq_signedTriplePolynomial
    (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedCollectedTriplePolynomial N X t =
      selbergSqrtZetaSignedTriplePolynomial N X t := by
  exact MathlibAux.collectedExponentialPolynomial_eq_exponentialPolynomial
    (selbergSqrtZetaSignedPhaseSupport N X)
    (selbergSqrtZetaSignedPhaseCoeff X)
    selbergSqrtZetaSignedPhaseFrequency t

/-- The signed phase polynomial is the common Hardy phase times the collected
distinct-frequency polynomial. -/
theorem
    selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_collectedTriplePolynomial
    (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedPhasePolynomial N X t =
      Complex.exp (I * (thetaModel t : ℂ)) *
        selbergSqrtZetaSignedCollectedTriplePolynomial N X t := by
  rw [selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_signedTriplePolynomial,
    selbergSqrtZetaSignedCollectedTriplePolynomial_eq_signedTriplePolynomial]

/-- The complex signed model has a common phase and a collision-free collected
finite exponential polynomial. -/
theorem
    selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial
    (kappa T : ℝ) (X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedComplexModel kappa T X t =
      Complex.exp (I * kappa) * Complex.exp (I * (thetaModel t : ℂ)) *
        selbergSqrtZetaSignedCollectedTriplePolynomial
          (firstZetaApproximationCutoff T) X t := by
  rw [selbergSqrtZetaSignedComplexModel,
    selbergSqrtZetaSignedPhasePolynomial_eq_exp_mul_collectedTriplePolynomial]
  ring

end HardyTheorem
