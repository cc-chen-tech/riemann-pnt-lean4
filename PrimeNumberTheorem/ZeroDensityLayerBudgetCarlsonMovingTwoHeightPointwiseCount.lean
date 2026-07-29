import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonUniformPointwiseCount

namespace PrimeNumberTheorem

open CarlsonZeroDensity

/-- The explicit height conditions under which the uniform Carlson contour
certificate gives a pointwise count estimate. -/
def CarlsonPointwiseHeightConditions
    (C₁ C₂ sigma T : ℝ) : Prop :=
  6 ≤ T ∧
    1 ≤ Real.log T ∧
    4 / Real.log T < sigma - 1 / 2 ∧
    1 ≤ T ^ (2 * sigma - 1) ∧
    C₁ ≤ T ∧ C₂ ≤ T

/-- The exact pointwise majorant returned by Carlson's contour argument. -/
noncomputable def carlsonPointwiseCountBudget
    (A sigma T : ℝ) : ℝ :=
  (125 * carlsonFinalCoefficient A sigma) *
    (T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4)

/-- One set of Carlson constants controls both heights pointwise.  This is the
quantifier order required by a moving two-height split. -/
theorem exists_carlson_moving_twoHeight_pointwise_count_certificate :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {delta U T : ℝ},
        0 < delta → delta < 1 / 4 →
        CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta) U →
        CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta) T →
        (ZeroDensity.zeroDensityCount (1 - 2 * delta) U : ℝ) ≤
            carlsonPointwiseCountBudget A (1 - 2 * delta) U ∧
          (ZeroDensity.zeroDensityCount (1 - 2 * delta) T : ℝ) ≤
            carlsonPointwiseCountBudget A (1 - 2 * delta) T := by
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hpointwise⟩ :=
    exists_carlson_uniform_pointwise_count_certificate
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro delta U T hdelta hdeltaQuarter hU hT
  have hsigma : 1 / 2 < 1 - 2 * delta := by linarith
  have hsigmaOne : 1 - 2 * delta < 1 := by linarith
  rcases hU with ⟨hU6, hUlog, hUwindow, hUpower, hC₁U, hC₂U⟩
  rcases hT with ⟨hT6, hTlog, hTwindow, hTpower, hC₁T, hC₂T⟩
  constructor
  · exact hpointwise hsigma hsigmaOne hU6 hUlog hUwindow hUpower hC₁U hC₂U
  · exact hpointwise hsigma hsigmaOne hT6 hTlog hTwindow hTpower hC₁T hC₂T

end PrimeNumberTheorem
