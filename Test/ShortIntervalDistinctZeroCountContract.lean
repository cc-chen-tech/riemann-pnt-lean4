import HardyTheorem.ShortIntervalDistinctZeroCount

open Complex

open HardyTheorem

#check card_le_criticalLineDistinctZeroCount_of_pairwiseDisjoint_hits

#print axioms card_le_criticalLineDistinctZeroCount_of_pairwiseDisjoint_hits

example (G : Finset ℕ) (J : ℕ → Set ℝ) (T : ℝ)
    (hdisj : (G : Set ℕ).PairwiseDisjoint J)
    (hhit : ∀ i ∈ G, ∃ t ∈ J i ∩ Set.Icc (0 : ℝ) T,
      riemannZeta ((1 / 2 : ℂ) + I * t) = 0) :
    G.card ≤ criticalLineDistinctZeroCount T := by
  exact card_le_criticalLineDistinctZeroCount_of_pairwiseDisjoint_hits
    G J T hdisj hhit
