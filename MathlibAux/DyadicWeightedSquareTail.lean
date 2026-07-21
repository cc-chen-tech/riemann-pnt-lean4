import MathlibAux.DyadicHarmonic
import MathlibAux.DyadicPartition

open scoped BigOperators

namespace MathlibAux

/-- A dyadically decaying square weight has uniformly bounded reciprocal
mass.  The block nearest the cutoff is indexed by distance one. -/
theorem sum_inv_mul_sq_le_of_dyadic_decay
    (s : Finset ℕ) (K : ℕ) (f : ℕ → ℝ) {A : ℝ}
    (hA : 0 ≤ A)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hbound : ∀ n ∈ s, n < 2 ^ K)
    (hdecay : ∀ k < K, ∀ n ∈ dyadicBlock s k,
      (f n) ^ 2 ≤ A * ((((K - k : ℕ) : ℝ) ^ 2)⁻¹)) :
    (∑ n ∈ s, ((n : ℝ))⁻¹ * (f n) ^ 2) ≤ 2 * A := by
  have hblock : ∀ k ∈ Finset.range K,
      (∑ n ∈ dyadicBlock s k, ((n : ℝ))⁻¹ * (f n) ^ 2) ≤
        A * ((((K - k : ℕ) : ℝ) ^ 2)⁻¹) := by
    intro k hk
    have hklt : k < K := Finset.mem_range.1 hk
    have hdist : 0 < K - k := by omega
    have hfactor : 0 ≤ A * ((((K - k : ℕ) : ℝ) ^ 2)⁻¹) := by
      positivity
    calc
      (∑ n ∈ dyadicBlock s k, ((n : ℝ))⁻¹ * (f n) ^ 2) ≤
          ∑ n ∈ dyadicBlock s k,
            ((n : ℝ))⁻¹ *
              (A * ((((K - k : ℕ) : ℝ) ^ 2)⁻¹)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hdecay k hklt n hn) (by positivity)
      _ = (∑ n ∈ dyadicBlock s k, ((n : ℝ))⁻¹) *
            (A * ((((K - k : ℕ) : ℝ) ^ 2)⁻¹)) := by
        rw [Finset.sum_mul]
      _ ≤ 1 * (A * ((((K - k : ℕ) : ℝ) ^ 2)⁻¹)) := by
        apply mul_le_mul_of_nonneg_right _ hfactor
        apply sum_inv_le_one_of_subset_dyadic
        intro n hn
        exact Finset.mem_Ico.2 (mem_dyadicBlock.1 hn).2
      _ = A * ((((K - k : ℕ) : ℝ) ^ 2)⁻¹) := by ring
  have hinj : ∀ a ∈ Finset.range K, ∀ b ∈ Finset.range K,
      K - a = K - b → a = b := by
    intro a ha b hb hab
    have halt : a < K := Finset.mem_range.1 ha
    have hblt : b < K := Finset.mem_range.1 hb
    omega
  have himage : (Finset.range K).image (fun k => K - k) ⊆
      Finset.Icc 1 K := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    have hklt : k < K := Finset.mem_range.1 hk
    simp only [Finset.mem_Icc]
    omega
  have hreciprocal :
      (∑ k ∈ Finset.range K,
        (((((K - k : ℕ) : ℝ) ^ 2))⁻¹)) ≤ 2 := by
    let q : ℕ → ℝ := fun j => ((((j : ℝ) ^ 2))⁻¹)
    have hsum :
        (∑ k ∈ Finset.range K,
          (((((K - k : ℕ) : ℝ) ^ 2))⁻¹)) =
          ∑ j ∈ (Finset.range K).image (fun k => K - k),
            ((((j : ℝ) ^ 2))⁻¹) := by
      have hsum' :
          (∑ k ∈ Finset.range K, q (K - k)) =
            ∑ j ∈ (Finset.range K).image (fun k => K - k), q j :=
        (Finset.sum_image hinj).symm
      simpa only [q] using hsum'
    rw [hsum]
    calc
      (∑ j ∈ (Finset.range K).image (fun k => K - k),
          ((((j : ℝ) ^ 2))⁻¹)) ≤
          ∑ j ∈ Finset.Icc 1 K, ((((j : ℝ) ^ 2))⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg himage (by
          intro j _hj _himage
          positivity)
      _ ≤ 2 := sum_inv_sq_Icc_one_le_two K
  calc
    (∑ n ∈ s, ((n : ℝ))⁻¹ * (f n) ^ 2) =
        ∑ k ∈ Finset.range K,
          ∑ n ∈ dyadicBlock s k, ((n : ℝ))⁻¹ * (f n) ^ 2 :=
      (sum_dyadicBlocks s K
        (fun n => ((n : ℝ))⁻¹ * (f n) ^ 2) hpos hbound).symm
    _ ≤ ∑ k ∈ Finset.range K,
        A * ((((K - k : ℕ) : ℝ) ^ 2)⁻¹) :=
      Finset.sum_le_sum hblock
    _ = A * (∑ k ∈ Finset.range K,
        ((((K - k : ℕ) : ℝ) ^ 2)⁻¹)) := by
      rw [Finset.mul_sum]
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left hreciprocal hA
    _ = 2 * A := by ring

end MathlibAux
