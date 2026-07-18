import ZeroFreeRegion.VinogradovKorobov.WeightedSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (a : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (a k : ℂ) * z k) =
      (a N : ℂ) * (∑ k ∈ Finset.range (N + 1), z k) +
        ∑ k ∈ Finset.range N,
          ((a k - a (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (k + 1), z j) :=
  weighted_sum_eq_endpoint_add_partial_sums a z N

example (a : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (ha : ∀ k ≤ N, 0 ≤ a k)
    (hanti : ∀ k < N, a (k + 1) ≤ a k)
    (hpartial : ∀ k ≤ N,
      ‖∑ j ∈ Finset.range (k + 1), z j‖ ≤ B) :
    ‖∑ k ∈ Finset.range (N + 1), (a k : ℂ) * z k‖ ≤ a 0 * B :=
  norm_weighted_sum_le_first_mul a z N B ha hanti hpartial

end ZeroFreeRegion.VinogradovKorobov
