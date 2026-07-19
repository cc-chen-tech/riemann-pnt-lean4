import HardyTheorem.HardyPhaseSharpTwoBandSecondMoment

open Complex MeasureTheory Set

example :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ delta : ℝ, 1 ≤ delta →
        ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T ≥ T0,
          (∫ t in T..2 * T - delta,
            Complex.normSq
              (HardyTheorem.hardyPhaseLinearizedSum T delta t)) ≤
            A * delta * T +
              B * (delta ^ 4 + delta) * Real.sqrt T :=
  HardyTheorem.exists_integral_normSq_hardyPhaseLinearizedSum_le_twoBand

#print axioms
  HardyTheorem.exists_integral_normSq_hardyPhaseLinearizedSum_le_twoBand
