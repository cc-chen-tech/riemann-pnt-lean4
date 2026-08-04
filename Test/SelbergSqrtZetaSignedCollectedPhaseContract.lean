import HardyTheorem.SelbergSqrtZetaSignedCollectedPhase

open HardyTheorem

noncomputable example (N X : ℕ) : Finset ℝ :=
  selbergSqrtZetaSignedCollectedFrequencySupport N X

example (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedCollectedTriplePolynomial N X t =
      selbergSqrtZetaSignedTriplePolynomial N X t :=
  selbergSqrtZetaSignedCollectedTriplePolynomial_eq_signedTriplePolynomial N X t

example (kappa T : ℝ) (X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedComplexModel kappa T X t =
      Complex.exp (Complex.I * kappa) *
        Complex.exp (Complex.I * (thetaModel t : ℂ)) *
          selbergSqrtZetaSignedCollectedTriplePolynomial
            (firstZetaApproximationCutoff T) X t :=
  selbergSqrtZetaSignedComplexModel_eq_exp_mul_exp_mul_collectedTriplePolynomial
    kappa T X t
