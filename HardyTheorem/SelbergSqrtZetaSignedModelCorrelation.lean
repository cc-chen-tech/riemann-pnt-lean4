import HardyTheorem.SelbergSqrtZetaSignedModelPolynomial

/-!
# Correlation decomposition for the signed square-root-zeta model

The real signed model is the real part of a finite complex phase polynomial.
The product of two real parts splits into an ordinary complex correlation and
a pseudo-correlation.  These two pieces have different oscillatory phases and
must be estimated separately in the Selberg signed second moment.
-/

open Complex

namespace HardyTheorem

/-- The finite complex model whose real part is the signed theta model. -/
noncomputable def selbergSqrtZetaSignedComplexModel
    (kappa T : ℝ) (X : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (I * kappa) *
    selbergSqrtZetaSignedPhasePolynomial
      (firstZetaApproximationCutoff T) X t

/-- The signed theta model is the real part of the finite complex model. -/
theorem selbergSqrtZetaSignedThetaModel_eq_complexModel_re
    (kappa T : ℝ) (X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedThetaModel kappa T X t =
      (selbergSqrtZetaSignedComplexModel kappa T X t).re := by
  exact
    selbergSqrtZetaSignedThetaModel_eq_re_exp_I_kappa_mul_signedPhasePolynomial
      kappa T X t

/-- Pointwise real-part correlation decomposition.  The first term has the
Hardy phase difference, while the second has the rapidly oscillating Hardy
phase sum. -/
theorem
    selbergSqrtZetaSignedThetaModel_mul_eq_correlation_add_pseudocorrelation
    (kappa T : ℝ) (X : ℕ) (t u : ℝ) :
    selbergSqrtZetaSignedThetaModel kappa T X t *
        selbergSqrtZetaSignedThetaModel kappa T X u =
      ((selbergSqrtZetaSignedComplexModel kappa T X t *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X u)).re +
        (selbergSqrtZetaSignedComplexModel kappa T X t *
          selbergSqrtZetaSignedComplexModel kappa T X u).re) / 2 := by
  rw [selbergSqrtZetaSignedThetaModel_eq_complexModel_re,
    selbergSqrtZetaSignedThetaModel_eq_complexModel_re]
  simp only [mul_re, conj_re, conj_im]
  ring

end HardyTheorem
