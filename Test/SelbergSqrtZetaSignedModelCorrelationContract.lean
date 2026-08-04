import HardyTheorem.SelbergSqrtZetaSignedModelCorrelation

open Complex

namespace HardyTheorem

noncomputable example (kappa T : ℝ) (X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaSignedComplexModel kappa T X t

example (kappa T : ℝ) (X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedThetaModel kappa T X t =
      (selbergSqrtZetaSignedComplexModel kappa T X t).re :=
  selbergSqrtZetaSignedThetaModel_eq_complexModel_re kappa T X t

example (kappa T : ℝ) (X : ℕ) (t u : ℝ) :
    selbergSqrtZetaSignedThetaModel kappa T X t *
        selbergSqrtZetaSignedThetaModel kappa T X u =
      ((selbergSqrtZetaSignedComplexModel kappa T X t *
          (starRingEnd ℂ) (selbergSqrtZetaSignedComplexModel kappa T X u)).re +
        (selbergSqrtZetaSignedComplexModel kappa T X t *
          selbergSqrtZetaSignedComplexModel kappa T X u).re) / 2 :=
  selbergSqrtZetaSignedThetaModel_mul_eq_correlation_add_pseudocorrelation
    kappa T X t u

end HardyTheorem
