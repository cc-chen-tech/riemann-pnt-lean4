import HardyTheorem.SelbergSqrtZetaSignedApproximation

open Complex Set

namespace HardyTheorem

noncomputable example (kappa T : ℝ) (X : ℕ) (t : ℝ) : ℝ :=
  selbergSqrtZetaSignedThetaModel kappa T X t

example (X : ℕ) (t : ℝ) :
    selbergSqrtZetaMollifiedHardyZ X t =
      (Complex.exp (I * thetaPhase t) *
          riemannZeta ((1 / 2 : ℂ) + I * t) *
        (Complex.normSq
          (selbergSqrtZetaMollifier X
            ((1 / 2 : ℂ) + I * t)) : ℂ)).re :=
  selbergSqrtZetaMollifiedHardyZ_eq_rotatedZeta_re_mul_normSq X t

example :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, ∀ T t : ℝ,
        T0 ≤ T → t ∈ Icc T (2 * T) →
          |selbergSqrtZetaMollifiedHardyZ X t -
              selbergSqrtZetaSignedThetaModel kappa T X t| ≤
            C / Real.sqrt T *
              Complex.normSq
                (selbergSqrtZetaMollifier X
                  ((1 / 2 : ℂ) + I * t)) :=
  exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_normSq

example :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, ∀ T t : ℝ,
        T0 ≤ T → t ∈ Icc T (2 * T) →
          |selbergSqrtZetaMollifiedHardyZ X t -
              selbergSqrtZetaSignedThetaModel kappa T X t| ≤
            C / Real.sqrt T *
              selbergSqrtZetaMollifierMajorant X ^ 2 :=
  exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_majorant

example :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T t : ℝ,
        T0 ≤ T → t ∈ Icc T (2 * T) →
          |selbergSqrtZetaMollifiedHardyZ X t -
              selbergSqrtZetaSignedThetaModel kappa T X t| ≤
            4 * C * X / Real.sqrt T :=
  exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_four_mul

example :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T t u : ℝ,
        T0 ≤ T → t ∈ Icc T (2 * T) → u ∈ Icc T (2 * T) →
          |selbergSqrtZetaMollifiedHardyZ X t *
                selbergSqrtZetaMollifiedHardyZ X u -
              selbergSqrtZetaSignedThetaModel kappa T X t *
                selbergSqrtZetaSignedThetaModel kappa T X u| ≤
            (4 * C * X / Real.sqrt T) *
              (|selbergSqrtZetaSignedThetaModel kappa T X t| +
                |selbergSqrtZetaSignedThetaModel kappa T X u| +
                4 * C * X / Real.sqrt T) :=
  exists_abs_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le

end HardyTheorem
