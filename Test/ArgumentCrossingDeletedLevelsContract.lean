import MathlibAux.ArgumentCrossing

open Set
open MathlibAux

-- Mutation caught: deleting arbitrary bad levels costs at most their full
-- cardinality, while the endpoint-rounding loss remains the single global
-- loss already present in `argumentCrossingIndices_card_lower_bound`.
example {alpha beta : ℝ} (bad : Finset ℤ) :
    (beta - alpha) / Real.pi - 1 - bad.card ≤
      ((argumentCrossingIndices alpha beta) \ bad).card := by
  exact argumentCrossingIndices_sdiff_card_lower_bound bad

#print axioms argumentCrossingIndices_sdiff_card_lower_bound

-- A half-open phase bridge of length `m * pi` contains exactly `m` global
-- crossing levels, including the endpoint-aligned cases.
example {alpha : ℝ} {m : ℕ} {k : ℤ} :
    k ∈ argumentCrossingBridgeIndices alpha m ↔
      argumentCrossingLevel k ∈ Set.Ico alpha (alpha + m * Real.pi) := by
  exact mem_argumentCrossingBridgeIndices_iff

example (alpha : ℝ) (m : ℕ) :
    (argumentCrossingBridgeIndices alpha m).card = m := by
  exact argumentCrossingBridgeIndices_card alpha m

#print axioms argumentCrossingBridgeIndices_card
