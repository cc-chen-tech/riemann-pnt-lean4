import HardyTheorem.VerticalGammaAsymptotic

open Complex MeasureTheory Set

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
    ‖∫ u in Set.Ioi t,
      HardyTheorem.verticalStirlingBernoulliKernel t u‖ ≤ C / t :=
  HardyTheorem.exists_norm_integral_Ioi_verticalStirlingBernoulliKernel_le_inv

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
    ‖∫ u in Set.Ioi (0 : ℝ),
      HardyTheorem.verticalStirlingBernoulliKernel t u‖ ≤ C / t :=
  HardyTheorem.exists_norm_integral_Ioi_zero_verticalStirlingBernoulliKernel_le_inv
