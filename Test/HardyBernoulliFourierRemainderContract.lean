import HardyTheorem.FirstZetaApproximation

open Complex MeasureTheory Set

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b t p : ℝ},
    a ≤ b → 0 < a → 0 < p → |t| ≤ a →
      ‖∫ x in a..b,
        ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
          (x ^ (-p) • Complex.exp (I * (-t * Real.log x)))‖ ≤
        C * a ^ (-p) :=
  HardyTheorem.exists_norm_intervalIntegral_periodizedBernoulli_two_mellin_le

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b sigma t : ℝ},
    a ≤ b → 0 < a → 0 < sigma + 2 → |t| ≤ a →
      ‖∫ x in a..b,
        ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
          (x : ℂ) ^ (-(((sigma : ℂ) + I * t) + 2))‖ ≤
        C * a ^ (-(sigma + 2)) :=
  HardyTheorem.exists_norm_intervalIntegral_periodizedBernoulli_two_cpow_le
