import HardyTheorem.ShortIntervalSignChangeMeasure

open Complex Set

namespace HardyTheorem

#check HasNegToPosLocalSignChangeAt
#check HasNegToPosLocalSignChangeAt.eq_zero
#check card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_signChanges
#check card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_hardyZ_signChanges

example (G : Finset ℕ) (J : ℕ → Set ℝ) (T : ℝ)
    (hdisj : (G : Set ℕ).PairwiseDisjoint J)
    (hsign : ∀ i ∈ G, ∃ t ∈ J i, t ∈ Set.Icc (0 : ℝ) T ∧
      HasNegToPosLocalSignChangeAt hardyZ t) :
    G.card ≤ criticalLineOddZeroCount T := by
  exact card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_hardyZ_signChanges
    G J T hdisj hsign

end HardyTheorem
