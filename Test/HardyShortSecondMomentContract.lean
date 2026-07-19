import HardyTheorem.HardyShortSecondMoment

open MeasureTheory Set

#check HardyTheorem.exists_integral_hardyShortIntegral_sq_le_mul
#print axioms HardyTheorem.exists_integral_hardyShortIntegral_sq_le_mul

example (delta : ℝ) (hdelta : 1 ≤ delta) :
    ∃ C > 0, ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T ≥ T0,
      (∫ t in T..2 * T - delta,
        (HardyTheorem.hardyShortIntegral delta t) ^ 2) ≤ C * T :=
  HardyTheorem.exists_integral_hardyShortIntegral_sq_le_mul delta hdelta
