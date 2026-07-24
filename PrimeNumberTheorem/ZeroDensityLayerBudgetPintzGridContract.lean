import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzGrid

namespace PrimeNumberTheorem

example
    {zeroFree : ℝ → ℝ → Prop}
    (input : PintzEnvelopeDynamicGridInput zeroFree)
    (cost : ℝ → ℝ → ℝ) :
    Filter.Tendsto
      (dynamicFiniteGridOptimalHeight
        cost input.toDynamicFiniteHeightGrid)
      Filter.atTop Filter.atTop :=
  input.optimalHeight_tendsto_atTop cost

example
    {zeroFree : ℝ → ℝ → Prop}
    (input : PintzEnvelopeDynamicGridInput zeroFree)
    (cost : ℝ → ℝ → ℝ) :
    ∀ᶠ x in Filter.atTop,
      zeroFree x
        (dynamicFiniteGridOptimalHeight
          cost input.toDynamicFiniteHeightGrid x) :=
  input.eventually_optimalHeight_zeroFree cost

end PrimeNumberTheorem
