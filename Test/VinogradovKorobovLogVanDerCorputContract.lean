import ZeroFreeRegion.VinogradovKorobov.LogVanDerCorput

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (t : ℝ) (m : ℕ) (B : ℕ → ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hcor : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.range (N - ell),
        zetaOscillation t (m + n) *
          (starRingEnd ℂ) (zetaOscillation t (m + n + ell))‖ ≤ B ell) :
    (L : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * B ell :=
  vanDerCorputZetaOscillationOfCorrelationBounds t m B N L hL hLN hcor

example (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hturn : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ∀ k ≤ N - ell - 1,
        logarithmicCorrelationPhase t ell (m + (k + 1)) -
          logarithmicCorrelationPhase t ell (m + k) < 2 * Real.pi) :
    (L : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) *
            logarithmicCorrelationEndpointBound t ell m (N - ell - 1) :=
  vanDerCorputZetaOscillationWithKusminLandau t m N L ht hm hL hLN hturn

example (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hstart : ∀ ell ∈ Finset.Icc 1 (L - 1),
      logarithmicCorrelationPhase t ell (m + 1) -
        logarithmicCorrelationPhase t ell m < 2 * Real.pi) :
    (L : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) *
            logarithmicCorrelationEndpointBound t ell m (N - ell - 1) :=
  vanDerCorputZetaOscillationWithKusminLandauOfStartTurn t m N L ht hm hL hLN hstart

example (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hfrac : ∀ ell ∈ Finset.Icc 1 (L - 1),
      t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) < 2 * Real.pi) :
    (L : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) *
            logarithmicCorrelationEndpointBound t ell m (N - ell - 1) :=
  vanDerCorputZetaOscillationWithKusminLandauOfFractionTurn t m N L ht hm hL hLN hfrac

example (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hmargin : ∀ ell ∈ Finset.Icc 1 (L - 1),
      t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
        t * (ell : ℝ) /
          (((m + (N - ell - 1) : ℕ) : ℝ) *
              (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
        2 * Real.pi) :
    (L : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) *
            (2 * Real.pi *
                (((m + (N - ell - 1) : ℕ) : ℝ) *
                    (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) /
              (t * (ell : ℝ))) :=
  vanDerCorputZetaOscillationExplicit t m N L ht hm hL hLN hmargin

example (t : ℝ) (m N L : ℕ) (ht : 0 < t) :
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) *
          (2 * Real.pi *
              (((m + (N - ell - 1) : ℕ) : ℝ) *
                  (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) /
            (t * (ell : ℝ)))) ≤
      (2 * Real.pi *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) / t) *
        ((L : ℝ) * (1 + Real.log L)) :=
  weightedExplicitCorrelationSum_le t m N L ht

example (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hmargin : ∀ ell ∈ Finset.Icc 1 (L - 1),
      t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
        t * (ell : ℝ) /
          (((m + (N - ell - 1) : ℕ) : ℝ) *
              (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
        2 * Real.pi) :
    (L : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N +
        4 * Real.pi * ((N : ℝ) + ((L : ℝ) - 1)) * L *
          (1 + Real.log L) *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) / t :=
  vanDerCorputZetaOscillationHarmonic t m N L ht hm hL hLN hmargin

example (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hmargin : ∀ ell ∈ Finset.Icc 1 (L - 1),
      t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
        t * (ell : ℝ) /
          (((m + (N - ell - 1) : ℕ) : ℝ) *
              (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
        2 * Real.pi) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      (((N : ℝ) + ((L : ℝ) - 1)) * N) / L +
        4 * Real.pi * ((N : ℝ) + ((L : ℝ) - 1)) *
          (1 + Real.log L) *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) /
          (t * L) :=
  norm_zetaOscillation_sum_sq_le_harmonic t m N L ht hm hL hLN hmargin

example (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hmargin : ∀ ell ∈ Finset.Icc 1 (L - 1),
      t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
        t * (ell : ℝ) /
          (((m + (N - ell - 1) : ℕ) : ℝ) *
              (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
        2 * Real.pi)
    (hsaving :
      (((N : ℝ) + ((L : ℝ) - 1)) * N) / L +
        4 * Real.pi * ((N : ℝ) + ((L : ℝ) - 1)) *
          (1 + Real.log L) *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) /
          (t * L) < (N : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ < N :=
  norm_zetaOscillation_sum_lt_trivial_of_harmonic
    t m N L ht hm hL hLN hmargin hsaving

example (m : ℕ) (hm : 2000 ≤ m) :
    ‖∑ n ∈ Finset.range m,
        zetaOscillation ((m : ℝ) ^ 2) (m + n)‖ < m :=
  norm_zetaOscillation_square_height_block_lt_trivial m hm

end ZeroFreeRegion.VinogradovKorobov
