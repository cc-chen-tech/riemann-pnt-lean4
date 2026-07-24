import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonAdaptiveHeight

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for adaptive finite-grid Pintz-Carlson heights. -/

example
    (rates : Finset ℝ)
    (selectRate : ℝ → ℝ)
    (hselect : ∀ x, selectRate x ∈ rates)
    (hratesPos : ∀ k ∈ rates, 0 < k) :
    Tendsto
      (fun x : ℝ => pintzCarlsonHeight (selectRate x) x)
      atTop atTop :=
  tendsto_adaptive_pintzCarlsonHeight_atTop
    rates selectRate hselect hratesPos

example
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (C sigma : ι → ℝ)
    (hC : ∀ i ∈ layers, 0 ≤ C i)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonFiniteLayerBudget
            layers C sigma (selectRate x) x)
        atTop (𝓝 0) :=
  exists_pintzConstant_adaptiveFiniteHeightBudget_tendsto
    layers C sigma hC rates

example
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (C sigma : ι → ℝ)
    (hC : ∀ i ∈ layers, 0 ≤ C i)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀
      (selectRate : ℝ → ℝ)
      (actualBudget : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      (∀ x, 0 ≤ actualBudget x) →
      (∀ᶠ x : ℝ in atTop,
        actualBudget x ≤
          pintzCarlsonFiniteLayerBudget
            layers C sigma (selectRate x) x) →
      Tendsto actualBudget atTop (𝓝 0) :=
  exists_pintzConstant_dominatedAdaptiveLayerBudget_tendsto
    layers C sigma hC rates

end PrimeNumberTheorem
