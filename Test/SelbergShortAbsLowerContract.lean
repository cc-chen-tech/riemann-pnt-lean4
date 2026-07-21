import HardyTheorem.SelbergShortAbsLower

open Complex MeasureTheory Set

namespace Test.SelbergShortAbsLowerContract

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H t : ℝ,
        T0 ≤ T → 0 ≤ H →
        t ∈ Icc T (2 * T - H) →
          H -
              ‖HardyTheorem.selbergMollifiedShortDirichletPolynomial H
                (HardyTheorem.firstZetaApproximationCutoff T) X t‖ -
              4 * C * H * X / Real.sqrt T ≤
            HardyTheorem.selbergMoebiusAbsShortIntegral X H t :=
  HardyTheorem.exists_selbergMoebiusAbsShortIntegral_ge_sub_shortDirichlet_coarse

#print axioms HardyTheorem.norm_selbergMoebiusMollifier_criticalLine_le_sum_inv_sqrt
#print axioms HardyTheorem.criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_sq_eq
#print axioms HardyTheorem.exists_selbergMoebiusMollifiedZetaFirstApprox
#print axioms HardyTheorem.exists_selbergMoebiusAbsShortIntegral_ge_sub_shortDirichlet
#print axioms HardyTheorem.exists_selbergMoebiusAbsShortIntegral_ge_sub_shortDirichlet_coarse

end Test.SelbergShortAbsLowerContract
