import HardyTheorem.SelbergMollifiedSecondMoment

open Complex MeasureTheory Set

namespace HardyTheorem

#check sq_selbergMoebiusMollifiedHardyZ_eq_normSq_zeta_mul_normSq_mollifier_sq
#check exists_integral_sq_selbergMoebiusMollifiedHardyZ_le

#print axioms sq_selbergMoebiusMollifiedHardyZ_eq_normSq_zeta_mul_normSq_mollifier_sq
#print axioms exists_integral_sq_selbergMoebiusMollifiedHardyZ_le

example :
    ∃ C T0 : ℝ, 0 < C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T : ℝ, T0 ≤ T →
        (∫ t in T..2 * T,
            selbergMoebiusMollifiedHardyZ X t ^ 2) ≤
          C * (X : ℝ) ^ 2 * T ^ 2 :=
  exists_integral_sq_selbergMoebiusMollifiedHardyZ_le

end HardyTheorem
