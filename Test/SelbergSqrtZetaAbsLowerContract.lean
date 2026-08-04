import HardyTheorem.SelbergSqrtZetaAbsLower

open Complex Set

namespace HardyTheorem

noncomputable example (X : ℕ) (t : ℝ) : ℝ :=
  selbergSqrtZetaMollifiedHardyZ X t

noncomputable example (X : ℕ) (H t : ℝ) : ℝ :=
  selbergSqrtZetaAbsShortIntegral X H t

noncomputable example (H : ℝ) (N X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaShortDirichletPolynomialIntegral H N X t

example (H : ℝ) (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaShortDirichletPolynomialIntegral H N X t =
      selbergSqrtZetaMollifiedShortDirichletPolynomial H N X t :=
  selbergSqrtZetaShortDirichletPolynomialIntegral_eq H N X t

example (X : ℕ) (t : ℝ) :
    |selbergSqrtZetaMollifiedHardyZ X t| =
      ‖(riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)‖ :=
  abs_selbergSqrtZetaMollifiedHardyZ_eq_norm_zeta_mul_mollifier_sq X t

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H t : ℝ,
        T0 ≤ T → 0 ≤ H →
        t ∈ Icc T (2 * T - H) →
          H -
              ‖selbergSqrtZetaShortDirichletPolynomialIntegral H
                (firstZetaApproximationCutoff T) X t‖ -
              4 * C * H * X / Real.sqrt T ≤
            selbergSqrtZetaAbsShortIntegral X H t :=
  exists_selbergSqrtZetaAbsShortIntegral_ge_sub_shortDirichlet

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H t : ℝ,
        T0 ≤ T → 0 ≤ H →
        t ∈ Icc T (2 * T - H) →
          H -
              ‖selbergSqrtZetaMollifiedShortDirichletPolynomial H
                (firstZetaApproximationCutoff T) X t‖ -
              4 * C * H * X / Real.sqrt T ≤
            selbergSqrtZetaAbsShortIntegral X H t :=
  exists_selbergSqrtZetaAbsShortIntegral_ge_sub_mollifiedPolynomial

end HardyTheorem
