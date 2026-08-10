import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonContourAutomaticDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingHeightConditions

open Filter

namespace PrimeNumberTheorem

/--
The actual moving Carlson strip mass tends to zero with no remaining
pointwise-height side condition.  The logarithmic gap forces the balanced
height to infinity, while positivity of `alpha` handles the fixed height.
-/
theorem tendsto_actualMovingCarlsonStripMass_zero_fullyAutomatic
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * alpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    Tendsto (actualMovingCarlsonStripMass alpha delta) atTop (nhds 0) := by
  obtain ⟨A, C₁, C₂, _hA, _hC₁, _hC₂, htransfer⟩ :=
    exists_actualMovingCarlsonContourAutomaticDecay halpha hdelta hgap
  apply htransfer
  have hdeltaBasic : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 := by
    filter_upwards [hdelta] with m hm
    exact ⟨hm.1, hm.2.1⟩
  filter_upwards [
    eventually_balancedCarlsonPointwiseHeightConditions
      (C₁ := C₁) (C₂ := C₂) halpha hdeltaBasic hgap,
    eventually_fixedCarlsonPointwiseHeightConditions
      (C₁ := C₁) (C₂ := C₂) halpha hdeltaBasic
  ] with m hbalanced hfixed
  exact ⟨hbalanced, hfixed⟩

end PrimeNumberTheorem
