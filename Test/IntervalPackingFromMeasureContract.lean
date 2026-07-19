import MathlibAux.IntervalPackingFromMeasure

open MeasureTheory Set

namespace MathlibAux

#check exists_many_pairwiseDisjoint_windows_of_measure_compl_le
#print axioms exists_many_pairwiseDisjoint_windows_of_measure_compl_le

example (good : Set ℝ) (a b H E : ℝ)
    (hH : 0 < H) (hab : a ≤ b)
    (hbad : volume.real (Set.Icc a b \ good) ≤ E) :
    ∃ (G : Finset ℕ) (start : ℕ → ℝ),
      ((Nat.floor ((b - a) / (3 * H)) : ℝ) - E / H ≤
          (G.card : ℝ)) ∧
        (∀ i ∈ G, start i ∈ good ∩ Set.Icc a (b - H)) ∧
        (G : Set ℕ).PairwiseDisjoint
          (fun i ↦ Set.Ioo (start i) (start i + H)) := by
  exact exists_many_pairwiseDisjoint_windows_of_measure_compl_le
    good a b H E hH hab hbad

end MathlibAux
