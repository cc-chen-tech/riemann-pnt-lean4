import HardyTheorem.CriticalLineMultiplicity

open Complex

namespace HardyTheorem

/-!
# Packing distinct critical-line zeros from disjoint height sets

This file supplies the finite packing step needed when short-interval
arguments detect a critical-line zero without controlling its multiplicity.
-/

/-- Pairwise-disjoint real sets containing critical-line zeta zeros at
heights in `[0, T]` inject into the distinct critical-line zero count. -/
theorem card_le_criticalLineDistinctZeroCount_of_pairwiseDisjoint_hits
    (G : Finset ℕ) (J : ℕ → Set ℝ) (T : ℝ)
    (hdisj : (G : Set ℕ).PairwiseDisjoint J)
    (hhit : ∀ i ∈ G, ∃ t ∈ J i ∩ Set.Icc (0 : ℝ) T,
      riemannZeta ((1 / 2 : ℂ) + I * t) = 0) :
    G.card ≤ criticalLineDistinctZeroCount T := by
  classical
  let τ : G → ℝ := fun i => Classical.choose (hhit i i.property)
  have hτmem (i : G) : τ i ∈ J i ∩ Set.Icc (0 : ℝ) T :=
    (Classical.choose_spec (hhit i i.property)).1
  have hτzero (i : G) :
      riemannZeta ((1 / 2 : ℂ) + I * τ i) = 0 :=
    (Classical.choose_spec (hhit i i.property)).2
  have hτfinset (i : G) :
      (1 / 2 : ℂ) + I * τ i ∈ criticalLineZerosFinset T := by
    rw [mem_criticalLineZerosFinset]
    refine ⟨⟨hτzero i, ?_, ?_⟩, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · simpa using (hτmem i).2.1
    · simpa using (hτmem i).2.2
  let F : G → criticalLineZerosFinset T := fun i =>
    ⟨(1 / 2 : ℂ) + I * τ i, hτfinset i⟩
  have hF : Function.Injective F := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hval :
        (1 / 2 : ℂ) + I * τ i = (1 / 2 : ℂ) + I * τ j :=
      congrArg Subtype.val hij
    have hτeq : τ i = τ j := by
      have him := congrArg Complex.im hval
      simpa using him
    have hd : Disjoint (J (i : ℕ)) (J (j : ℕ)) :=
      hdisj i.property j.property hne
    have hjmem : τ i ∈ J (j : ℕ) := by
      rw [hτeq]
      exact (hτmem j).1
    exact Set.disjoint_left.1 hd (hτmem i).1 hjmem
  have hcard := Fintype.card_le_of_injective F hF
  simpa [criticalLineDistinctZeroCount] using hcard

end HardyTheorem
