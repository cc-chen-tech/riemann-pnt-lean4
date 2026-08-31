import HardyTheorem.OscillatoryGammaTail

open Real Complex Set

namespace HardyTheorem.OscillatoryGammaTail

#check norm_intervalIntegral_cpow_mul_cexp_linear_le
#print axioms norm_intervalIntegral_cpow_mul_cexp_linear_le
#check exists_tendsto_oscillatoryGammaPartial_atTop
#print axioms exists_tendsto_oscillatoryGammaPartial_atTop
#check tendsto_oscillatoryGammaPartial_atTop
#check norm_oscillatoryGammaBoundary_sub_partial_le
#print axioms norm_oscillatoryGammaBoundary_sub_partial_le

example {z : ℂ} {c A B : ℝ}
    (hAB : A ≤ B) (hA : 0 < A) (hz1 : z.re < 1)
    (hc : 0 < c) (him : 2 * |z.im| ≤ c * A) :
    ‖∫ u in A..B,
        (u : ℂ) ^ (z - 1) * Complex.exp (I * (c * u))‖ ≤
      8 * A ^ (z.re - 1) / c := by
  exact norm_intervalIntegral_cpow_mul_cexp_linear_le
    hAB hA hz1 hc him

end HardyTheorem.OscillatoryGammaTail
