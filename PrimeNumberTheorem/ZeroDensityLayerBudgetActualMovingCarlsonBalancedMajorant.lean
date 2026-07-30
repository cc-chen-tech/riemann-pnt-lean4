import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonBalancedExponent

namespace PrimeNumberTheorem

/-- Exact common coefficient of the low/high pointwise Carlson majorants at
the balanced cut. -/
noncomputable def actualMovingCarlsonBalancedPointwiseCoefficient
    (A alpha delta : ℝ) : ℝ :=
  125 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
      (carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha) ^ (4 : ℕ) /
        (1 - 2 * delta) +
    125 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
      alpha ^ (4 : ℕ)

/-- At the balanced intermediate height, the complete pointwise majorant is
exactly one coefficient times the common balanced power and fourth logarithm.
-/
theorem actualMovingCarlsonTwoHeightPointwiseMajorant_balanced_eq
    {A alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hdelta : 0 < delta m) (hquarter : delta m < 1 / 4) :
    actualMovingCarlsonTwoHeightPointwiseMajorant
        A alpha delta (carlsonMovingBalancedCut alpha delta) m =
      actualMovingCarlsonBalancedPointwiseCoefficient A alpha (delta m) *
        ((m : ℝ) ^
            carlsonTwoHeightBalancedExponent
              (1 - 2 * delta m) (1 - delta m) alpha *
          (Real.log (m : ℝ)) ^ (4 : ℕ)) := by
  have hmPos : (0 : ℝ) < (m : ℝ) := by positivity
  unfold actualMovingCarlsonTwoHeightPointwiseMajorant
    actualMovingCarlsonLowPointwiseMajorant
    actualMovingCarlsonHighPointwiseMajorant
    carlsonMovingBalancedCut
  rw [actualMovingCarlsonLowPointwiseMajorant_eq hmPos,
    actualMovingCarlsonHighPointwiseMajorant_eq hmPos,
    carlsonMovingLowExponent_eq_balanced hdelta hquarter,
    carlsonMovingHighExponent_eq_balanced hdelta hquarter]
  unfold actualMovingCarlsonBalancedPointwiseCoefficient
  ring

end PrimeNumberTheorem
