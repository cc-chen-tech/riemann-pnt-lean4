import HardyTheorem.SelbergSqrtZetaSignedApproximation
import HardyTheorem.SelbergSqrtZetaSignedPhasePolynomial

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Signed square-root-zeta model polynomial

This module identifies the real signed theta model with the real part of the
exact signed phase polynomial.  It converts the scalar mollifier weight
`normSq M` into `M * conj M` and then applies the finite phase-polynomial
identity.
-/

/-- The signed theta model is exactly the real part of the common `kappa`
rotation of the signed square-root-zeta phase polynomial. -/
theorem selbergSqrtZetaSignedThetaModel_eq_re_exp_I_kappa_mul_signedPhasePolynomial
    (kappa T : ℝ) (X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedThetaModel kappa T X t =
      (Complex.exp (I * kappa) *
        selbergSqrtZetaSignedPhasePolynomial
          (firstZetaApproximationCutoff T) X t).re := by
  unfold selbergSqrtZetaSignedThetaModel
  rw [← exp_I_thetaModel_mul_criticalLinePolynomial_mul_sqrtZetaMollifier_mul_conj_eq_signedPhasePolynomial]
  congr 1
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- The two-point signed model correlation is the product of the corresponding
real parts of the rotated signed phase polynomials. -/
theorem selbergSqrtZetaSignedThetaModel_mul_eq_re_exp_I_kappa_mul_signedPhasePolynomial_mul
    (kappa T : ℝ) (X : ℕ) (t u : ℝ) :
    selbergSqrtZetaSignedThetaModel kappa T X t *
        selbergSqrtZetaSignedThetaModel kappa T X u =
      (Complex.exp (I * kappa) *
        selbergSqrtZetaSignedPhasePolynomial
          (firstZetaApproximationCutoff T) X t).re *
        (Complex.exp (I * kappa) *
          selbergSqrtZetaSignedPhasePolynomial
            (firstZetaApproximationCutoff T) X u).re := by
  rw [selbergSqrtZetaSignedThetaModel_eq_re_exp_I_kappa_mul_signedPhasePolynomial,
    selbergSqrtZetaSignedThetaModel_eq_re_exp_I_kappa_mul_signedPhasePolynomial]

end HardyTheorem
