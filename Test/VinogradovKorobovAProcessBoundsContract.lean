import ZeroFreeRegion.VinogradovKorobov.AProcessBounds

namespace ZeroFreeRegion.VinogradovKorobov

example (B : ℕ → ℝ) (C : ℝ) (L : ℕ)
    (hC : 0 ≤ C)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1), B ell ≤ C) :
    ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell ≤ (L : ℝ) ^ 2 * C :=
  sum_aProcess_weights_le_sq_mul B C L hC hB

example (B : ℕ → ℝ) (C : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hC : 0 ≤ C)
    (hB0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ B ell)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1), B ell ≤ C) :
    aProcessSquaredBound B N L ≤
      2 * (N : ℝ) ^ 2 / L + 4 * (N : ℝ) * C :=
  aProcessSquaredBound_le B C N L hL hLN hC hB0 hB

example (B C : ℕ → ℝ) (N M L : ℕ)
    (hL : 1 ≤ L) (hNM : N ≤ M)
    (hB0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ B ell)
    (hC0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ C ell)
    (hBC : ∀ ell ∈ Finset.Icc 1 (L - 1), B ell ≤ C ell) :
    aProcessSquaredBound B N L ≤ aProcessSquaredBound C M L :=
  aProcessSquaredBound_mono B C N M L hL hNM hB0 hC0 hBC

example (B : ℕ → ℝ) (C : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hC : 0 ≤ C)
    (hB0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ B ell)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1),
      B ell ≤ C * (ell : ℝ)⁻¹) :
    aProcessSquaredBound B N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) * C * (1 + Real.log L) / L :=
  aProcessSquaredBound_le_reciprocal
    B C N L hL hLN hC hB0 hB

example (Q : ℕ → ℝ) (A D α : ℝ) (N L : ℕ)
    (hL : 2 ≤ L) (hLN : L ≤ N)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hα0 : 0 ≤ α) (hα2 : α < 2)
    (hQ : ∀ ell ∈ Finset.Icc 1 (L - 1),
      Q ell ≤ A + D * (ell : ℝ) ^ (-α)) :
    aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) *
          (Real.sqrt A * (L : ℝ) ^ 2 +
            Real.sqrt D * (L : ℝ) * finiteRpowSumEnvelope L (α / 2)) /
          (L : ℝ) ^ 2 :=
  aProcessSquaredBound_le_sqrt_add_rpow
    Q A D α N L hL hLN hA hD hα0 hα2 hQ

example (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * (Real.sqrt ell)⁻¹) ≤
      Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L)) :=
  weighted_inv_sqrt_sum_le L

example (B : ℕ → ℝ) (A D : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hB0 : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ B ell)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1),
      B ell ≤ Real.sqrt (A + D * (ell : ℝ)⁻¹)) :
    aProcessSquaredBound B N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) *
          (Real.sqrt A * (L : ℝ) ^ 2 +
            Real.sqrt D *
              Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L))) /
          (L : ℝ) ^ 2 :=
  aProcessSquaredBound_le_sqrt_reciprocal
    B A D N L hL hLN hA hD hB0 hB

end ZeroFreeRegion.VinogradovKorobov
