import ZeroFreeRegion.VinogradovKorobov.RecursiveReciprocalEnvelope

namespace ZeroFreeRegion.VinogradovKorobov

example (Q : ℕ → ℝ) (C : ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hC : 0 ≤ C)
    (hQ : ∀ ell ∈ Finset.Icc 1 (L - 1),
      Q ell ≤ (C * (ell : ℝ)⁻¹) ^ 2) :
    aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) * C * (1 + Real.log L) / L :=
  aProcessSquaredBound_le_of_sq_reciprocal
    Q C N L hL hLN hC hQ

end ZeroFreeRegion.VinogradovKorobov
