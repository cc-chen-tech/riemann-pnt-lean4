import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonAdaptiveHeight

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for adaptive finite-grid Pintz-Carlson heights. -/

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

end PrimeNumberTheorem
