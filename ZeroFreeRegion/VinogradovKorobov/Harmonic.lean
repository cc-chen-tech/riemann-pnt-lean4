import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The weighted reciprocal sum produced by one van der Corput differencing
step is bounded by a harmonic factor. -/
theorem weighted_reciprocal_sum_le (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * (ell : ℝ)⁻¹) ≤
      (L : ℝ) * (1 + Real.log L) := by
  have hpointwise :
      (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * (ell : ℝ)⁻¹) ≤
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          (L : ℝ) * (ell : ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro ell hell
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg ell))
    exact sub_le_self (L : ℝ) (Nat.cast_nonneg ell)
  have hsubset : Finset.Icc 1 (L - 1) ⊆ Finset.Icc 1 L := by
    intro ell hell
    simp only [Finset.mem_Icc] at hell ⊢
    exact ⟨hell.1, hell.2.trans (Nat.sub_le L 1)⟩
  have hextend :
      (∑ ell ∈ Finset.Icc 1 (L - 1),
          (L : ℝ) * (ell : ℝ)⁻¹) ≤
        ∑ ell ∈ Finset.Icc 1 L,
          (L : ℝ) * (ell : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro ell hell hnot
    positivity
  have hharmonic :
      (∑ ell ∈ Finset.Icc 1 L, (ell : ℝ)⁻¹) = (harmonic L : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * (ell : ℝ)⁻¹) ≤
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          (L : ℝ) * (ell : ℝ)⁻¹ := hpointwise
    _ ≤ ∑ ell ∈ Finset.Icc 1 L,
          (L : ℝ) * (ell : ℝ)⁻¹ := hextend
    _ = (L : ℝ) * (harmonic L : ℝ) := by
      rw [← Finset.mul_sum, hharmonic]
    _ ≤ (L : ℝ) * (1 + Real.log L) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (Nat.cast_nonneg L)

end ZeroFreeRegion.VinogradovKorobov
