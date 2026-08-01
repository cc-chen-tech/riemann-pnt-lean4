import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicOptimization

namespace PrimeNumberTheorem

private noncomputable def growingSingletonGrid : DynamicFiniteHeightGrid where
  grid := fun x =>
    { heights := {max 1 x}
      nonempty := by simp
      positive := by
        intro T hT
        simp only [Finset.mem_singleton] at hT
        subst T
        exact lt_of_lt_of_le zero_lt_one (le_max_left 1 x) }
  lowerEnvelope := fun x => x
  lowerEnvelope_tendsto_atTop := tendsto_id
  lowerEnvelope_le := by
    intro x T hT
    simp only [Finset.mem_singleton] at hT
    subst T
    exact le_max_right 1 x

example :
    Filter.Tendsto
      (dynamicFiniteGridOptimalHeight
        (fun x T : ℝ => (T - x) ^ 2) growingSingletonGrid)
      Filter.atTop Filter.atTop :=
  dynamicFiniteGridOptimalHeight_tendsto_atTop _ _

example (x : ℝ) :
    0 < dynamicFiniteGridOptimalHeight
      (fun x T : ℝ => (T - x) ^ 2) growingSingletonGrid x :=
  dynamicFiniteGridOptimalHeight_pos _ _ _

end PrimeNumberTheorem
