import HardyTheorem.OscillatoryDampedGammaTail

open Real Complex Set

namespace HardyTheorem.OscillatoryDampedGammaTail

#check norm_intervalIntegral_cpow_mul_exp_neg_mul_cexp_neg_linear_le
#print axioms norm_intervalIntegral_cpow_mul_exp_neg_mul_cexp_neg_linear_le

example {z : ℂ} {r c A B : ℝ}
    (hAB : A ≤ B) (hA : 0 < A) (hz1 : z.re < 1)
    (hr : 0 ≤ r) (hc : 0 < c) (him : 2 * |z.im| ≤ c * A) :
    ‖∫ u in A..B,
        (u : ℂ) ^ (z - 1) * Complex.exp (-(r * u)) *
          Complex.exp (-I * (c * u))‖ ≤
      8 * A ^ (z.re - 1) / c := by
  exact norm_intervalIntegral_cpow_mul_exp_neg_mul_cexp_neg_linear_le
    hAB hA hz1 hr hc him

end HardyTheorem.OscillatoryDampedGammaTail
