import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonDensityTransfer

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for adaptive Carlson density-count transfer. -/

example
    {sigma : ℝ}
    (hσ : 1 / 2 < sigma)
    (hσ1 : sigma < 1) :
    ∃ C ≥ 0, ∀ᶠ T : ℝ in atTop,
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        C * T ^ (4 * sigma * (1 - sigma)) *
          Real.log T ^ 4 :=
  exists_carlsonClassicalCoefficient_eventually_count_le hσ hσ1

example
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (count : ι → ℝ → ℝ)
    (hcount : ∀ i T, 0 ≤ count i T)
    (C sigma : ι → ℝ)
    (hC : ∀ i ∈ layers, 0 ≤ C i)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      (∀ i ∈ layers, ∀ᶠ x : ℝ in atTop,
        count i (pintzCarlsonHeight (selectRate x) x) ≤
          C i *
            pintzCarlsonHeight (selectRate x) x ^
              (4 * sigma i * (1 - sigma i)) *
            Real.log
                (pintzCarlsonHeight (selectRate x) x) ^ 4) →
      Tendsto
        (pintzCarlsonActualDensityBudget
          layers count selectRate)
        atTop (𝓝 0) :=
  exists_pintzConstant_adaptiveCarlsonDensityBudget_tendsto
    layers count hcount C sigma hC rates

end PrimeNumberTheorem
