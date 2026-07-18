import ZeroFreeRegion.VinogradovKorobov.Harmonic

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * (ell : ℝ)⁻¹) ≤
      (L : ℝ) * (1 + Real.log L) :=
  weighted_reciprocal_sum_le L

end ZeroFreeRegion.VinogradovKorobov
