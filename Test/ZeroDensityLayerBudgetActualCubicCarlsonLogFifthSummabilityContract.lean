import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonLogFifthSummability

namespace PrimeNumberTheorem

open Filter

example (sigma : ℝ) :
    actualCubicCarlsonDyadicRatio sigma =
      pntDyadicReciprocalDensityRatio
        (pntCarlsonClassicalDensityExponent sigma - 5) := rfl

example (sigma : ℝ) :
    0 < actualCubicCarlsonDyadicRatio sigma :=
  actualCubicCarlsonDyadicRatio_pos sigma

example (sigma : ℝ) :
    actualCubicCarlsonDyadicRatio sigma < 1 :=
  actualCubicCarlsonDyadicRatio_lt_one sigma

example (C sigma : ℝ) (n : ℕ) :
    actualCubicCarlsonDyadicLogFifthMajorant C sigma n =
      C * ((n + 1 : ℕ) : ℝ) ^ 5 *
        actualCubicCarlsonDyadicRatio sigma ^ (n + 1) := rfl

example (C sigma : ℝ) :
    Summable (actualCubicCarlsonDyadicLogFifthMajorant C sigma) :=
  summable_actualCubicCarlsonDyadicLogFifthMajorant C sigma

example {mass : ℕ → ℝ} {C sigma : ℝ}
    (hmassNonneg : ∀ n, 0 ≤ mass n)
    (hmass : ∀ᶠ n : ℕ in atTop,
      mass n ≤ actualCubicCarlsonDyadicLogFifthMajorant C sigma n) :
    Summable mass :=
  summable_of_eventually_le_actualCubicCarlsonDyadicLogFifthMajorant
    hmassNonneg hmass

end PrimeNumberTheorem
