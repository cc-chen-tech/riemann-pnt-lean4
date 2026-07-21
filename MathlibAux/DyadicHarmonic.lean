import Mathlib.Analysis.PSeries

open scoped BigOperators

namespace MathlibAux

private theorem sum_inv_Ico_self_two_mul_le_one
    {M : ℕ} (hM : 0 < M) :
    (∑ n ∈ (Finset.Ico M (2 * M) : Finset ℕ), ((n : ℝ))⁻¹) ≤ 1 := by
  have hpoint : ∀ n ∈ (Finset.Ico M (2 * M) : Finset ℕ),
      ((n : ℝ))⁻¹ ≤ ((M : ℝ))⁻¹ := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact inv_anti₀ (by exact_mod_cast hM) (by exact_mod_cast hn.1)
  have hcard : (Finset.Ico M (2 * M) : Finset ℕ).card = M := by
    rw [Nat.card_Ico]
    omega
  calc
    (∑ n ∈ (Finset.Ico M (2 * M) : Finset ℕ), ((n : ℝ))⁻¹) ≤
        ∑ _n ∈ (Finset.Ico M (2 * M) : Finset ℕ), ((M : ℝ))⁻¹ :=
      Finset.sum_le_sum hpoint
    _ = (M : ℝ) * ((M : ℝ))⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = 1 := by field_simp

/-- The reciprocal mass of every half-open dyadic block is at most one. -/
theorem sum_inv_dyadic_interval_le_one (k : ℕ) :
    (∑ n ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1)) : Finset ℕ),
      ((n : ℝ))⁻¹) ≤ 1 := by
  simpa only [pow_succ, mul_comm] using
    (sum_inv_Ico_self_two_mul_le_one (M := 2 ^ k) (by positivity))

/-- Every subset of a dyadic block has reciprocal mass at most one. -/
theorem sum_inv_le_one_of_subset_dyadic
    {s : Finset ℕ} {k : ℕ}
    (hs : s ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1))) :
    (∑ n ∈ s, ((n : ℝ))⁻¹) ≤ 1 := by
  calc
    (∑ n ∈ s, ((n : ℝ))⁻¹) ≤
        ∑ n ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1)) : Finset ℕ),
          ((n : ℝ))⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (by
        intro n _hn _hns
        positivity)
    _ ≤ 1 := sum_inv_dyadic_interval_le_one k

/-- Every finite initial segment of the reciprocal-square series beginning
at one is bounded by two. -/
theorem sum_inv_sq_Icc_one_le_two (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, (((j : ℝ) ^ 2))⁻¹) ≤ 2 := by
  by_cases hK : K = 0
  · simp [hK]
  have hset : Finset.Icc 1 K = insert 1 (Finset.Ioo 1 (K + 1)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  have hone : 1 ∉ Finset.Ioo 1 (K + 1) := by simp
  have htail :
      (∑ j ∈ Finset.Ioo 1 (K + 1), (((j : ℝ) ^ 2))⁻¹) ≤ 1 := by
    have h := sum_Ioo_inv_sq_le (α := ℝ) 1 (K + 1)
    norm_num at h ⊢
    exact h
  rw [hset, Finset.sum_insert hone]
  norm_num
  linarith

end MathlibAux
