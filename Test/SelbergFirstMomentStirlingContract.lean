import HardyTheorem.SelbergFirstMomentStirling

open Complex

namespace HardyTheorem

example :
    ∃ c : ℝ, 0 < c ∧
      ∀ T delta t : ℝ,
        2 ≤ T → 0 ≤ delta → delta ≤ 1 / T →
        T / 2 ≤ t → t ≤ T →
        c * T ^ (-(1 / 4 : ℝ)) ≤
          ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ *
            Real.exp ((Real.pi / 4 - delta / 2) * t) :=
  exists_pos_rpow_neg_quarter_le_norm_GammaR_mul_selbergTilt

#print axioms exists_pos_rpow_neg_quarter_mul_exp_le_norm_GammaR
#print axioms exists_pos_rpow_neg_quarter_le_norm_GammaR_mul_selbergTilt

end HardyTheorem
