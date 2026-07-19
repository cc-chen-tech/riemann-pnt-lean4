import ZeroFreeRegion.VinogradovKorobov.AProcessBounds

namespace ZeroFreeRegion.VinogradovKorobov

/-- Squared child bounds with reciprocal shift decay propagate through one
A-process step with the harmonic `(1 + log L) / L` gain. -/
theorem aProcessSquaredBound_le_of_sq_reciprocal
    (Q : ℕ → ℝ) (C : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hC : 0 ≤ C)
    (hQ : ∀ ell ∈ Finset.Icc 1 (L - 1),
      Q ell ≤ (C * (ell : ℝ)⁻¹) ^ 2) :
    aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) * C * (1 + Real.log L) / L := by
  apply aProcessSquaredBound_le_reciprocal
    (fun ell ↦ Real.sqrt (Q ell)) C N L hL hLN hC
  · intro ell hell
    exact Real.sqrt_nonneg _
  · intro ell hell
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg hC (inv_nonneg.mpr (Nat.cast_nonneg ell)), ?_⟩
    exact hQ ell hell

end ZeroFreeRegion.VinogradovKorobov
