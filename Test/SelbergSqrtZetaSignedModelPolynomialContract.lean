import HardyTheorem.SelbergSqrtZetaSignedModelPolynomial

open Complex

namespace HardyTheorem

example (kappa T : ℝ) (X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedThetaModel kappa T X t =
      (Complex.exp (I * kappa) *
        selbergSqrtZetaSignedPhasePolynomial
          (firstZetaApproximationCutoff T) X t).re :=
  selbergSqrtZetaSignedThetaModel_eq_re_exp_I_kappa_mul_signedPhasePolynomial
    kappa T X t

example (kappa T : ℝ) (X : ℕ) (t u : ℝ) :
    selbergSqrtZetaSignedThetaModel kappa T X t *
        selbergSqrtZetaSignedThetaModel kappa T X u =
      (Complex.exp (I * kappa) *
        selbergSqrtZetaSignedPhasePolynomial
          (firstZetaApproximationCutoff T) X t).re *
        (Complex.exp (I * kappa) *
          selbergSqrtZetaSignedPhasePolynomial
            (firstZetaApproximationCutoff T) X u).re :=
  selbergSqrtZetaSignedThetaModel_mul_eq_re_exp_I_kappa_mul_signedPhasePolynomial_mul
    kappa T X t u

end HardyTheorem
