import ZeroFreeRegion.VinogradovKorobov.VanDerCorput

open Finset

namespace ZeroFreeRegion.VinogradovKorobov

example (a N : ℕ) (ha : 0 < a) (u : ℕ → ℂ) (L : ℕ)
    (hL : 1 ≤ a * L) (hLN : a * L ≤ N) :
    (L : ℝ) ^ 2 * ‖∑ n ∈ Finset.Icc 1 N, u n‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + (a : ℝ) * ((L : ℝ) - 1)) *
          ∑ n ∈ Finset.Icc 1 N, ‖u n‖ ^ 2
      + 2 * ((N : ℝ) + (a : ℝ) * ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ell : ℝ)) *
          (∑ n ∈ Finset.Icc 1 (N - a * ell),
            u n * (starRingEnd ℂ) (u (n + a * ell))).re :=
  vanDerCorputFundamentalInequality a N ha u L hL hLN

end ZeroFreeRegion.VinogradovKorobov
