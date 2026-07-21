import HardyTheorem.ShortIntervalMeanValue

#check HardyTheorem.hardyShortIntegral
#check HardyTheorem.hardyShortAbsIntegral
#check HardyTheorem.continuous_hardyShortIntegral
#check HardyTheorem.continuous_hardyShortAbsIntegral
#check HardyTheorem.exists_hardyShortAbsIntegral_le_mul_sqrt
#check HardyTheorem.mul_integral_abs_hardyZ_interior_le_integral_hardyShortAbsIntegral
#check HardyTheorem.exists_integral_hardyShortAbsIntegral_ge_mul

example :
    ∃ c : ℝ, 0 < c ∧ ∀ delta : ℝ, 0 < delta → ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        c * delta * T ≤
          ∫ t in T..2 * T - delta,
            HardyTheorem.hardyShortAbsIntegral delta t :=
  HardyTheorem.exists_integral_hardyShortAbsIntegral_ge_mul
