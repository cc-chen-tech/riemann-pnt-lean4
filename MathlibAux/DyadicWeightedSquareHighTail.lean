import MathlibAux.DyadicHarmonic
import MathlibAux.DyadicPartition

open scoped BigOperators

namespace MathlibAux

/-- A square weight decaying away from the first block of a finite high dyadic
tail has uniformly bounded reciprocal mass. -/
theorem sum_inv_mul_sq_le_of_high_dyadic_decay
    (s : Finset ℕ) (K L : ℕ) (f : ℕ → ℝ) {A : ℝ}
    (hA : 0 ≤ A)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hlower : ∀ n ∈ s, 2 ^ K ≤ n)
    (hupper : ∀ n ∈ s, n < 2 ^ L)
    (hdecay : ∀ k, K ≤ k → k < L → ∀ n ∈ dyadicBlock s k,
      (f n) ^ 2 ≤ A * (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹)) :
    (∑ n ∈ s, ((n : ℝ))⁻¹ * (f n) ^ 2) ≤ 2 * A := by
  have hcover : (Finset.Ico K L).biUnion (dyadicBlock s) = s := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_biUnion.1 hn with ⟨k, _hk, hnk⟩
      exact (mem_dyadicBlock.1 hnk).1
    · intro hn
      have hn0 : n ≠ 0 := hpos n hn
      have hk_lower : K ≤ n.log2 :=
        (Nat.le_log2 hn0).2 (hlower n hn)
      have hk_upper : n.log2 < L :=
        (Nat.log2_lt hn0).2 (hupper n hn)
      exact Finset.mem_biUnion.2 ⟨n.log2,
        Finset.mem_Ico.2 ⟨hk_lower, hk_upper⟩,
        mem_dyadicBlock_log2 hn hn0⟩
  have hsum_blocks :
      (∑ k ∈ Finset.Ico K L,
          ∑ n ∈ dyadicBlock s k, ((n : ℝ))⁻¹ * (f n) ^ 2) =
        ∑ n ∈ s, ((n : ℝ))⁻¹ * (f n) ^ 2 := by
    rw [← Finset.sum_biUnion]
    · rw [hcover]
    · intro i hi j hj hij
      exact dyadicBlock_disjoint s hij
  have hblock : ∀ k ∈ Finset.Ico K L,
      (∑ n ∈ dyadicBlock s k, ((n : ℝ))⁻¹ * (f n) ^ 2) ≤
        A * (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹) := by
    intro k hk
    have hk_bounds : K ≤ k ∧ k < L := Finset.mem_Ico.1 hk
    have hfactor :
        0 ≤ A * (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹) := by
      positivity
    calc
      (∑ n ∈ dyadicBlock s k, ((n : ℝ))⁻¹ * (f n) ^ 2) ≤
          ∑ n ∈ dyadicBlock s k,
            ((n : ℝ))⁻¹ *
              (A * (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left
          (hdecay k hk_bounds.1 hk_bounds.2 n hn) (by positivity)
      _ = (∑ n ∈ dyadicBlock s k, ((n : ℝ))⁻¹) *
            (A * (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹)) := by
        rw [Finset.sum_mul]
      _ ≤ 1 * (A * (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹)) := by
        apply mul_le_mul_of_nonneg_right _ hfactor
        apply sum_inv_le_one_of_subset_dyadic
        intro n hn
        exact Finset.mem_Ico.2 (mem_dyadicBlock.1 hn).2
      _ = A * (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹) := by ring
  have hinj : ∀ a ∈ Finset.Ico K L, ∀ b ∈ Finset.Ico K L,
      a - K + 1 = b - K + 1 → a = b := by
    intro a ha b hb hab
    have haK : K ≤ a := (Finset.mem_Ico.1 ha).1
    have hbK : K ≤ b := (Finset.mem_Ico.1 hb).1
    omega
  have himage : (Finset.Ico K L).image (fun k => k - K + 1) ⊆
      Finset.Icc 1 (L - K) := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    have hk_bounds : K ≤ k ∧ k < L := Finset.mem_Ico.1 hk
    simp only [Finset.mem_Icc]
    omega
  have hreciprocal :
      (∑ k ∈ Finset.Ico K L,
        (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹)) ≤ 2 := by
    let q : ℕ → ℝ := fun j => ((((j : ℝ) ^ 2))⁻¹)
    have hsum :
        (∑ k ∈ Finset.Ico K L,
          (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹)) =
          ∑ j ∈ (Finset.Ico K L).image (fun k => k - K + 1),
            ((((j : ℝ) ^ 2))⁻¹) := by
      have hsum' :
          (∑ k ∈ Finset.Ico K L, q (k - K + 1)) =
            ∑ j ∈ (Finset.Ico K L).image (fun k => k - K + 1), q j :=
        (Finset.sum_image hinj).symm
      simpa only [q] using hsum'
    rw [hsum]
    calc
      (∑ j ∈ (Finset.Ico K L).image (fun k => k - K + 1),
          ((((j : ℝ) ^ 2))⁻¹)) ≤
          ∑ j ∈ Finset.Icc 1 (L - K), ((((j : ℝ) ^ 2))⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg himage (by
          intro j _hj _himage
          positivity)
      _ ≤ 2 := sum_inv_sq_Icc_one_le_two (L - K)
  calc
    (∑ n ∈ s, ((n : ℝ))⁻¹ * (f n) ^ 2) =
        ∑ k ∈ Finset.Ico K L,
          ∑ n ∈ dyadicBlock s k, ((n : ℝ))⁻¹ * (f n) ^ 2 :=
      hsum_blocks.symm
    _ ≤ ∑ k ∈ Finset.Ico K L,
        A * (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹) :=
      Finset.sum_le_sum hblock
    _ = A * (∑ k ∈ Finset.Ico K L,
        (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹)) := by
      rw [Finset.mul_sum]
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left hreciprocal hA
    _ = 2 * A := by ring

end MathlibAux
