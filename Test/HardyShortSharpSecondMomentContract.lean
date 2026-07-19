import HardyTheorem.HardyShortSharpSecondMoment

open MeasureTheory

example :
    ∃ C : ℝ, 0 < C ∧
      ∀ delta : ℝ, 1 ≤ delta →
        ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T ≥ T0,
          (∫ t in T..2 * T - delta,
            (HardyTheorem.hardyShortIntegral delta t) ^ 2) ≤
              C * delta * T :=
  HardyTheorem.exists_integral_hardyShortIntegral_sq_le_mul_delta

#print axioms
  HardyTheorem.exists_integral_hardyShortIntegral_sq_le_mul_delta
