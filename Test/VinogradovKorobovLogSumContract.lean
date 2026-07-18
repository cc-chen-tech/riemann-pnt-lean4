import ZeroFreeRegion.VinogradovKorobov.LogSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (t : ℝ) (n : ℕ) : ‖zetaOscillation t n‖ = 1 :=
  norm_zetaOscillation t n

example (t : ℝ) (n h : ℕ) :
    zetaOscillation t n * (starRingEnd ℂ) (zetaOscillation t (n + h)) =
      (starRingEnd ℂ) (phaseTerm (logarithmicCorrelationPhase t h) n) :=
  zetaOscillation_mul_conj_shift t n h

example (t : ℝ) (h m N : ℕ) :
    ‖∑ k ∈ Finset.range N,
        zetaOscillation t (m + k) *
          (starRingEnd ℂ) (zetaOscillation t (m + k + h))‖ =
      ‖∑ k ∈ Finset.range N,
        phaseTerm (fun j ↦ logarithmicCorrelationPhase t h (m + j)) k‖ :=
  norm_zetaOscillation_correlationSum_eq t h m N

example (t : ℝ) (h m N : ℕ) (ht : 0 < t) (hh : 0 < h) (hm : 0 < m)
    (hlt : ∀ k ≤ N,
      logarithmicCorrelationPhase t h (m + (k + 1)) -
        logarithmicCorrelationPhase t h (m + k) < 2 * Real.pi) :
    ‖∑ k ∈ Finset.range (N + 1),
        zetaOscillation t (m + k) *
          (starRingEnd ℂ) (zetaOscillation t (m + k + h))‖ ≤
      ‖(Complex.exp (Complex.I *
        ((logarithmicCorrelationPhase t h (m + 1) -
          logarithmicCorrelationPhase t h m : ℝ) : ℂ)) - 1)⁻¹‖ +
      ‖(Complex.exp (Complex.I *
        ((logarithmicCorrelationPhase t h (m + (N + 1)) -
          logarithmicCorrelationPhase t h (m + N) : ℝ) : ℂ)) - 1)⁻¹‖ +
      (Real.cot ((logarithmicCorrelationPhase t h (m + (N + 1)) -
          logarithmicCorrelationPhase t h (m + N)) / 2) -
        Real.cot ((logarithmicCorrelationPhase t h (m + 1) -
          logarithmicCorrelationPhase t h m) / 2)) / 2 :=
  norm_zetaOscillation_correlationSum_le_endpoint t h m N ht hh hm hlt

example (t : ℝ) (h m N : ℕ) (ht : 0 < t) (hh : 0 < h) (hm : 0 < m)
    (hmargin :
      t * (h : ℝ) / ((m : ℝ) * ((m : ℝ) + h + 1)) +
        t * (h : ℝ) /
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + h + 1) + h) ≤
        2 * Real.pi) :
    ‖∑ k ∈ Finset.range (N + 1),
        zetaOscillation t (m + k) *
          (starRingEnd ℂ) (zetaOscillation t (m + k + h))‖ ≤
      2 * Real.pi *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + h + 1) + h) /
        (t * (h : ℝ)) :=
  norm_zetaOscillation_correlationSum_le_explicit t h m N ht hh hm hmargin

end ZeroFreeRegion.VinogradovKorobov
