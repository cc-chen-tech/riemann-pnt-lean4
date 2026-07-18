import HardyTheorem.FirstZetaApproximation
import Mathlib.NumberTheory.ZetaValues

open Complex MeasureTheory Set

example {s : ℂ} (hs : 0 < s.re) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∫ x in (N : ℝ)..(M : ℝ),
      (((((⌊x⌋₊ : ℝ) - x) + 1 / 2 : ℝ) : ℂ) *
        (x : ℂ) ^ (-(s + 1)))) =
      ((N : ℂ) ^ (-(s + 1)) - (M : ℂ) ^ (-(s + 1))) / 12 -
        (s + 1) / 2 *
          ∫ x in (N : ℝ)..(M : ℝ),
            ((periodizedBernoulli 2 (x : AddCircle (1 : ℝ)) : ℝ) : ℂ) *
              (x : ℂ) ^ (-(s + 2)) :=
  HardyTheorem.intervalIntegral_centeredFloorError_cpow_eq_bernoulliTwo
    hs hN hNM
