import MathlibAux.FiberwiseNormSq

/-!
# Binary decomposition of a finite prefix

An initial interval inside a block of length `2^K` is a disjoint union of at
most `K+1` aligned dyadic blocks.  The resulting finite Cauchy--Schwarz bound
is the combinatorial core of a Rademacher--Menshov maximal mean-square
argument for moving Dirichlet-polynomial cutoffs.
-/

open Complex
open scoped BigOperators

namespace MathlibAux

/-- The aligned dyadic block with level `j` and block index `q`. -/
def dyadicPrefixBlock (j q : ℕ) : Finset ℕ :=
  Finset.Ico (q * 2 ^ j) ((q + 1) * 2 ^ j)

/-- Binary block identifiers for the first `m` points of the ambient aligned
block of length `2^K` and block index `q`.

The definition is total.  Its structural theorems assume `m ≤ 2^K`. -/
def dyadicPrefixIds : ℕ → ℕ → ℕ → Finset (ℕ × ℕ)
  | 0, m, q => if m = 0 then ∅ else {(0, q)}
  | K + 1, m, q =>
      if m ≤ 2 ^ K then
        dyadicPrefixIds K m (2 * q)
      else
        insert (K, 2 * q)
          (dyadicPrefixIds K (m - 2 ^ K) (2 * q + 1))

/-- Every aligned dyadic block inside the ambient block of length `2^K`.

The recursive description is tailored to the prefix decomposition: at the
next level it contains both half-blocks together with the two complete
subtrees. -/
def dyadicPrefixTree : ℕ → ℕ → Finset (ℕ × ℕ)
  | 0, q => {(0, q)}
  | K + 1, q =>
      insert (K, 2 * q) <|
        insert (K, 2 * q + 1) <|
          dyadicPrefixTree K (2 * q) ∪ dyadicPrefixTree K (2 * q + 1)

/-- Every block selected by a binary prefix decomposition belongs to the
complete aligned dyadic tree of the ambient block. -/
theorem dyadicPrefixIds_subset_tree (K m q : ℕ) :
    dyadicPrefixIds K m q ⊆ dyadicPrefixTree K q := by
  induction K generalizing m q with
  | zero =>
      by_cases hm : m = 0 <;> simp [dyadicPrefixIds, dyadicPrefixTree, hm]
  | succ K ih =>
      rw [dyadicPrefixIds, dyadicPrefixTree]
      split_ifs with hsmall
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inr (Or.inl (ih m (2 * q) hp)))
      · intro p hp
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · simp
        · simp only [Finset.mem_insert, Finset.mem_union]
          exact Or.inr (Or.inr (Or.inr
            (ih (m - 2 ^ K) (2 * q + 1) hp)))

/-- The binary prefix decomposition uses at most `K+1` blocks. -/
theorem card_dyadicPrefixIds_le (K m q : ℕ) :
    (dyadicPrefixIds K m q).card ≤ K + 1 := by
  induction K generalizing m q with
  | zero =>
      rw [dyadicPrefixIds]
      split_ifs <;> simp
  | succ K ih =>
      rw [dyadicPrefixIds]
      split_ifs with h
      · exact (ih m (2 * q)).trans (by omega)
      · exact (Finset.card_insert_le _ _).trans
          (Nat.add_le_add_right (ih (m - 2 ^ K) (2 * q + 1)) 1)

private theorem dyadicPrefixIds_fst_lt
    {K m q : ℕ} (hK : 0 < K) {p : ℕ × ℕ}
    (hp : p ∈ dyadicPrefixIds K m q) :
    p.1 < K := by
  induction K generalizing m q with
  | zero => omega
  | succ K ih =>
      rw [dyadicPrefixIds] at hp
      split_ifs at hp with h
      · by_cases hK0 : K = 0
        · subst K
          by_cases hm0 : m = 0
          · simp [dyadicPrefixIds, hm0] at hp
          · have hp' : p = (0, 2 * q) := by
              simpa [dyadicPrefixIds, hm0] using hp
            subst p
            simp
        · exact (ih (Nat.pos_of_ne_zero hK0) hp).trans (Nat.lt_succ_self K)
      · rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · simp
        · by_cases hK0 : K = 0
          · subst K
            by_cases hm0 : m - 1 = 0
            · simp [dyadicPrefixIds, hm0] at hp
            · have hp' : p = (0, 2 * q + 1) := by
                simpa [dyadicPrefixIds, hm0] using hp
              subst p
              simp
          · exact (ih (Nat.pos_of_ne_zero hK0) hp).trans (Nat.lt_succ_self K)

private theorem leftBlock_not_mem_rightPrefix (K r q : ℕ) :
    (K, 2 * q) ∉ dyadicPrefixIds K r (2 * q + 1) := by
  by_cases hK : K = 0
  · subst K
    by_cases hr : r = 0 <;> simp [dyadicPrefixIds, hr]
  · intro hmem
    have hlt := dyadicPrefixIds_fst_lt (Nat.pos_of_ne_zero hK) hmem
    simp at hlt

/-- Exact additive decomposition of an initial interval into its selected
aligned dyadic blocks. -/
theorem sum_dyadicPrefixBlocks
    {A : Type*} [AddCommMonoid A]
    (K m q : ℕ) (hm : m ≤ 2 ^ K) (f : ℕ → A) :
    (∑ n ∈ Finset.Ico (q * 2 ^ K) (q * 2 ^ K + m), f n) =
      ∑ p ∈ dyadicPrefixIds K m q,
        ∑ n ∈ dyadicPrefixBlock p.1 p.2, f n := by
  induction K generalizing m q with
  | zero =>
      have hm01 : m = 0 ∨ m = 1 := by omega
      rcases hm01 with rfl | rfl
      · simp [dyadicPrefixIds]
      · simp [dyadicPrefixIds, dyadicPrefixBlock]
  | succ K ih =>
      rw [dyadicPrefixIds]
      split_ifs with hsmall
      · have hrec := ih m (2 * q) hsmall
        rw [show q * 2 ^ (K + 1) = (2 * q) * 2 ^ K by
          rw [pow_succ]
          ring]
        exact hrec
      · have hpow : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by
          rw [pow_succ]
          ring
        have hlarge : 2 ^ K < m := Nat.lt_of_not_ge hsmall
        have hrem : m - 2 ^ K ≤ 2 ^ K := by
          rw [hpow] at hm
          omega
        have hrec := ih (m - 2 ^ K) (2 * q + 1) hrem
        rw [Finset.sum_insert (leftBlock_not_mem_rightPrefix K (m - 2 ^ K) q)]
        change
          (∑ n ∈ Finset.Ico (q * 2 ^ (K + 1))
              (q * 2 ^ (K + 1) + m), f n) =
            (∑ n ∈ Finset.Ico ((2 * q) * 2 ^ K)
              (((2 * q) + 1) * 2 ^ K), f n) +
              ∑ p ∈ dyadicPrefixIds K (m - 2 ^ K) (2 * q + 1),
                ∑ n ∈ dyadicPrefixBlock p.1 p.2, f n
        rw [← hrec]
        have hstart : (2 * q) * 2 ^ K = q * 2 ^ (K + 1) := by
          rw [pow_succ]
          ring
        have hmid : ((2 * q) + 1) * 2 ^ K =
            q * 2 ^ (K + 1) + 2 ^ K := by
          rw [pow_succ]
          ring
        rw [hstart, hmid]
        have htailend :
            q * 2 ^ (K + 1) + 2 ^ K + (m - 2 ^ K) =
              q * 2 ^ (K + 1) + m := by omega
        rw [htailend]
        exact (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm

/-- Finite Rademacher--Menshov pointwise skeleton: a prefix square is bounded
by `K+1` times the square sum of its selected aligned dyadic blocks. -/
theorem normSq_sum_Ico_le_dyadicPrefixBlocks
    (K m q : ℕ) (hm : m ≤ 2 ^ K) (f : ℕ → ℂ) :
    Complex.normSq
        (∑ n ∈ Finset.Ico (q * 2 ^ K) (q * 2 ^ K + m), f n) ≤
      (K + 1 : ℝ) *
        ∑ p ∈ dyadicPrefixIds K m q,
          Complex.normSq (∑ n ∈ dyadicPrefixBlock p.1 p.2, f n) := by
  rw [sum_dyadicPrefixBlocks K m q hm f]
  have hcs := normSq_finset_sum_le_card_mul_sum_normSq
    (dyadicPrefixIds K m q)
    (fun p => ∑ n ∈ dyadicPrefixBlock p.1 p.2, f n)
  exact hcs.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_dyadicPrefixIds_le K m q)
    (Finset.sum_nonneg fun p hp => Complex.normSq_nonneg _))

/-- Uniform pointwise Rademacher--Menshov envelope: every prefix square is
bounded by `K+1` times the block-square energy of the complete aligned
dyadic tree. -/
theorem normSq_sum_Ico_le_dyadicPrefixTree
    (K m q : ℕ) (hm : m ≤ 2 ^ K) (f : ℕ → ℂ) :
    Complex.normSq
        (∑ n ∈ Finset.Ico (q * 2 ^ K) (q * 2 ^ K + m), f n) ≤
      (K + 1 : ℝ) *
        ∑ p ∈ dyadicPrefixTree K q,
          Complex.normSq (∑ n ∈ dyadicPrefixBlock p.1 p.2, f n) := by
  refine (normSq_sum_Ico_le_dyadicPrefixBlocks K m q hm f).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (dyadicPrefixIds_subset_tree K m q) (by
        intro p hp hnot
        exact Complex.normSq_nonneg _)
  · positivity

end MathlibAux
