import Mathlib

open scoped BigOperators

namespace MathlibAux

/-- The part of `s` in the half-open dyadic interval `[2^k, 2^(k+1))`. -/
def dyadicBlock (s : Finset ℕ) (k : ℕ) : Finset ℕ :=
  s.filter fun n ↦ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1)

@[simp]
theorem mem_dyadicBlock {s : Finset ℕ} {k n : ℕ} :
    n ∈ dyadicBlock s k ↔ n ∈ s ∧ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  simp [dyadicBlock]

/-- A positive index belongs to the dyadic block selected by its binary logarithm. -/
theorem mem_dyadicBlock_log2 {s : Finset ℕ} {n : ℕ} (hn : n ∈ s) (hn0 : n ≠ 0) :
    n ∈ dyadicBlock s n.log2 := by
  exact mem_dyadicBlock.2 ⟨hn, Nat.log2_self_le hn0, Nat.lt_log2_self⟩

/-- Dyadic interval membership is equivalently a nonzero `Nat.log2` fiber. -/
theorem dyadicBlock_eq_filter_log2 (s : Finset ℕ) (k : ℕ) :
    dyadicBlock s k = s.filter fun n ↦ n ≠ 0 ∧ n.log2 = k := by
  ext n
  simp only [mem_dyadicBlock, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hlower, hupper⟩
    have hn0 : n ≠ 0 := by
      intro hnzero
      subst n
      have hpow : 0 < 2 ^ k := pow_pos (by omega) k
      omega
    have hk_le : k ≤ n.log2 := (Nat.le_log2 hn0).2 hlower
    have hlog_lt : n.log2 < k + 1 := (Nat.log2_lt hn0).2 hupper
    exact ⟨hn, hn0, Nat.le_antisymm (Nat.lt_succ_iff.mp hlog_lt) hk_le⟩
  · rintro ⟨hn, hn0, hlog⟩
    refine ⟨hn, ?_, ?_⟩
    · rw [← hlog]
      exact Nat.log2_self_le hn0
    · rw [← hlog]
      exact Nat.lt_log2_self

/-- Distinct dyadic blocks are disjoint. -/
theorem dyadicBlock_disjoint (s : Finset ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (dyadicBlock s i) (dyadicBlock s j) := by
  rw [Finset.disjoint_left]
  intro n hni hnj
  have hni' : n ∈ s.filter (fun m ↦ m ≠ 0 ∧ m.log2 = i) := by
    rwa [← dyadicBlock_eq_filter_log2]
  have hnj' : n ∈ s.filter (fun m ↦ m ≠ 0 ∧ m.log2 = j) := by
    rwa [← dyadicBlock_eq_filter_log2]
  have hi : n.log2 = i := (Finset.mem_filter.1 hni').2.2
  have hj : n.log2 = j := (Finset.mem_filter.1 hnj').2.2
  exact hij (hi.symm.trans hj)

/-- The bounded family of dyadic blocks is pairwise disjoint. -/
theorem pairwiseDisjoint_dyadicBlock (s : Finset ℕ) (K : ℕ) :
    (Finset.range K : Set ℕ).PairwiseDisjoint (dyadicBlock s) := by
  intro i _ j _ hij
  exact dyadicBlock_disjoint s hij

/-- Positive elements of `s` below `2^K` are covered by the first `K` dyadic blocks. -/
theorem biUnion_dyadicBlock_eq (s : Finset ℕ) (K : ℕ)
    (hpos : ∀ n ∈ s, n ≠ 0) (hbound : ∀ n ∈ s, n < 2 ^ K) :
    (Finset.range K).biUnion (dyadicBlock s) = s := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_biUnion.1 hn with ⟨k, _, hnk⟩
    exact (mem_dyadicBlock.1 hnk).1
  · intro hn
    have hn0 : n ≠ 0 := hpos n hn
    have hk : n.log2 < K := (Nat.log2_lt hn0).2 (hbound n hn)
    exact Finset.mem_biUnion.2 ⟨n.log2, Finset.mem_range.2 hk,
      mem_dyadicBlock_log2 hn hn0⟩

/-- Reindex a finite sum over positive bounded indices by its dyadic blocks. -/
theorem sum_dyadicBlocks {A : Type*} [AddCommMonoid A] (s : Finset ℕ) (K : ℕ)
    (f : ℕ → A) (hpos : ∀ n ∈ s, n ≠ 0) (hbound : ∀ n ∈ s, n < 2 ^ K) :
    ∑ k ∈ Finset.range K, ∑ n ∈ dyadicBlock s k, f n = ∑ n ∈ s, f n := by
  rw [← Finset.sum_biUnion (pairwiseDisjoint_dyadicBlock s K),
    biUnion_dyadicBlock_eq s K hpos hbound]

end MathlibAux
