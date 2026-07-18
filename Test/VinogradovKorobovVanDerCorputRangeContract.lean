import ZeroFreeRegion.VinogradovKorobov.VanDerCorputRange

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n =
      ∑ k ∈ Finset.range N, f (k + 1) :=
  sum_Icc_one_eq_sum_range f N

example (u : ℕ → ℂ) (N L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N) :
    (L : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, u n‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ n ∈ Finset.range N, ‖u n‖ ^ 2
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ell : ℝ)) *
          (∑ n ∈ Finset.range (N - ell),
            u n * (starRingEnd ℂ) (u (n + ell))).re :=
  vanDerCorputRangeInequality u N L hL hLN

example (u : ℕ → ℂ) (B : ℕ → ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hcor : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.range (N - ell),
        u n * (starRingEnd ℂ) (u (n + ell))‖ ≤ B ell) :
    (L : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, u n‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ n ∈ Finset.range N, ‖u n‖ ^ 2
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * B ell :=
  vanDerCorputRangeOfCorrelationBounds u B N L hL hLN hcor

end ZeroFreeRegion.VinogradovKorobov
