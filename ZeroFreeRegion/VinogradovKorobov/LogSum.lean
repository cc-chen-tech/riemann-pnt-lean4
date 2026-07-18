import ZeroFreeRegion.VinogradovKorobov.LogPhase

open scoped BigOperators
open ComplexConjugate

namespace ZeroFreeRegion.VinogradovKorobov

/-- The unit oscillation `n ↦ exp (-i t log n)` occurring in the Dirichlet
polynomial for `ζ(σ + i t)`. -/
noncomputable def zetaOscillation (t : ℝ) (n : ℕ) : ℂ :=
  phaseTerm (fun j ↦ -t * Real.log j) n

lemma norm_zetaOscillation (t : ℝ) (n : ℕ) :
    ‖zetaOscillation t n‖ = 1 :=
  norm_phaseTerm _ _

/-- A shifted autocorrelation of zeta oscillations is the conjugate of the
positive-increment logarithmic correlation phase. -/
lemma zetaOscillation_mul_conj_shift (t : ℝ) (n h : ℕ) :
    zetaOscillation t n * (starRingEnd ℂ) (zetaOscillation t (n + h)) =
      (starRingEnd ℂ) (phaseTerm (logarithmicCorrelationPhase t h) n) := by
  rw [zetaOscillation, zetaOscillation, phaseTerm_mul_conj_shift, phaseTerm]
  rw [← Complex.exp_conj]
  congr 1
  rw [logarithmicCorrelationPhase]
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  simp only [Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_mul]
  rw [Nat.cast_add]
  ring

/-- The norm of a zeta autocorrelation sum is exactly the norm of the
Kusmin--Landau logarithmic phase sum. -/
lemma norm_zetaOscillation_correlationSum_eq (t : ℝ) (h m N : ℕ) :
    ‖∑ k ∈ Finset.range N,
        zetaOscillation t (m + k) *
          (starRingEnd ℂ) (zetaOscillation t (m + k + h))‖ =
      ‖∑ k ∈ Finset.range N,
        phaseTerm (fun j ↦ logarithmicCorrelationPhase t h (m + j)) k‖ := by
  calc
    ‖∑ k ∈ Finset.range N,
        zetaOscillation t (m + k) *
          (starRingEnd ℂ) (zetaOscillation t (m + k + h))‖ =
      ‖∑ k ∈ Finset.range N,
        (starRingEnd ℂ)
          (phaseTerm (fun j ↦ logarithmicCorrelationPhase t h (m + j)) k)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [Nat.add_assoc] using zetaOscillation_mul_conj_shift t (m + k) h
    _ = ‖(starRingEnd ℂ) (∑ k ∈ Finset.range N,
        phaseTerm (fun j ↦ logarithmicCorrelationPhase t h (m + j)) k)‖ := by
      rw [map_sum]
    _ = ‖∑ k ∈ Finset.range N,
        phaseTerm (fun j ↦ logarithmicCorrelationPhase t h (m + j)) k‖ := by
      simpa only using norm_star (∑ k ∈ Finset.range N,
        phaseTerm (fun j ↦ logarithmicCorrelationPhase t h (m + j)) k)

/-- Quantitative bound for the zeta autocorrelation sum supplied to van der
Corput differencing. -/
theorem norm_zetaOscillation_correlationSum_le_endpoint
    (t : ℝ) (h m N : ℕ) (ht : 0 < t) (hh : 0 < h) (hm : 0 < m)
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
          logarithmicCorrelationPhase t h m) / 2)) / 2 := by
  rw [norm_zetaOscillation_correlationSum_eq]
  exact logarithmicCorrelation_kusminLandau_endpoint_bound t h m N ht hh hm hlt

end ZeroFreeRegion.VinogradovKorobov
