import ZeroFreeRegion.VinogradovKorobov.DirichletPrefix

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t : ℝ) (m N L : ℕ) : ℝ :=
  zetaOscillationHarmonicBound t m N L

example (t : ℝ) (m L : ℕ) {K N : ℕ}
    (ht : 0 < t) (hL : 1 ≤ L) (hKN : K ≤ N) :
    zetaOscillationHarmonicBound t m K L ≤
      zetaOscillationHarmonicBound t m N L :=
  zetaOscillationHarmonicBound_mono_length t m L ht hL hKN

example (t : ℝ) (m K L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hLK : L ≤ K)
    (hscale : t * ((L - 1 : ℕ) : ℝ) ≤
      (m : ℝ) * ((m : ℝ) + 2)) :
    ∀ ell ∈ Finset.Icc 1 (L - 1),
      t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
        t * (ell : ℝ) /
          (((m + (K - ell - 1) : ℕ) : ℝ) *
              (((m + (K - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
        2 * Real.pi :=
  logarithmic_prefix_margin_of_scale t m K L ht hm hLK hscale

example (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hL : 1 ≤ L) (Q : ℝ)
    (hmargin : ∀ K, L ≤ K → K ≤ N →
      ∀ ell ∈ Finset.Icc 1 (L - 1),
        t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
          t * (ell : ℝ) /
            (((m + (K - ell - 1) : ℕ) : ℝ) *
                (((m + (K - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
          2 * Real.pi)
    (henvelope : ∀ K, L ≤ K → K ≤ N →
      zetaOscillationHarmonicBound t m K L ≤ Q) :
    ∀ K ≤ N,
      ‖∑ n ∈ Finset.range K, zetaOscillation t (m + n)‖ ≤
        max (L : ℝ) (Real.sqrt Q) :=
  norm_zetaOscillation_prefix_le_max_sqrt_harmonic
    t m N L ht hm hL Q hmargin henvelope

example (sigma t : ℝ) (m N L : ℕ) (Q : ℝ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hmargin : ∀ K, L ≤ K → K ≤ N + 1 →
      ∀ ell ∈ Finset.Icc 1 (L - 1),
        t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
          t * (ell : ℝ) /
            (((m + (K - ell - 1) : ℕ) : ℝ) *
                (((m + (K - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
          2 * Real.pi)
    (henvelope : ∀ K, L ≤ K → K ≤ N + 1 →
      zetaOscillationHarmonicBound t m K L ≤ Q) :
    ‖∑ k ∈ Finset.range (N + 1),
        1 / ((m + k : ℕ) : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ≤
      dirichletWeight sigma m * max (L : ℝ) (Real.sqrt Q) :=
  norm_dirichletBlock_le_weight_mul_max_sqrt_harmonic
    sigma t m N L Q hsigma ht hm hL hmargin henvelope

example (sigma t : ℝ) (m N L : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hmargin : ∀ K, L ≤ K → K ≤ N + 1 →
      ∀ ell ∈ Finset.Icc 1 (L - 1),
        t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
          t * (ell : ℝ) /
            (((m + (K - ell - 1) : ℕ) : ℝ) *
                (((m + (K - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
          2 * Real.pi) :
    ‖∑ k ∈ Finset.range (N + 1),
        1 / ((m + k : ℕ) : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ≤
      dirichletWeight sigma m *
        max (L : ℝ)
          (Real.sqrt (zetaOscillationHarmonicBound t m (N + 1) L)) :=
  norm_dirichletBlock_le_weight_mul_harmonic_end
    sigma t m N L hsigma ht hm hL hmargin

example (sigma t : ℝ) (m N L : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hscale : t * ((L - 1 : ℕ) : ℝ) ≤
      (m : ℝ) * ((m : ℝ) + 2)) :
    ‖∑ k ∈ Finset.range (N + 1),
        1 / ((m + k : ℕ) : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ≤
      dirichletWeight sigma m *
        max (L : ℝ)
          (Real.sqrt (zetaOscillationHarmonicBound t m (N + 1) L)) :=
  norm_dirichletBlock_le_weight_mul_harmonic_end_of_scale
    sigma t m N L hsigma ht hm hL hscale

end ZeroFreeRegion.VinogradovKorobov
