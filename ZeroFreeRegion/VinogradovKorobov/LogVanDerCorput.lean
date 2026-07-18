import ZeroFreeRegion.VinogradovKorobov.LogSum
import ZeroFreeRegion.VinogradovKorobov.VanDerCorputRange

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Van der Corput specialized to a shifted block of zeta oscillations.  The
diagonal term is exactly the block length because every oscillation has norm
one. -/
theorem vanDerCorputZetaOscillationOfCorrelationBounds
    (t : ℝ) (m : ℕ) (B : ℕ → ℝ) (N L : ℕ)
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
          ((L : ℝ) - (ell : ℝ)) * B ell := by
  have h := vanDerCorputRangeOfCorrelationBounds
    (fun n ↦ zetaOscillation t (m + n)) B N L hL hLN (by
      intro ell hell
      simpa only [Nat.add_assoc] using hcor ell hell)
  have hdiag :
      (∑ n ∈ Finset.range N, ‖zetaOscillation t (m + n)‖ ^ 2) = (N : ℝ) := by
    simp only [norm_zetaOscillation, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  rw [hdiag] at h
  exact h

/-- The explicit Kusmin--Landau endpoint expression for a logarithmic
autocorrelation block of length `K + 1`. -/
noncomputable def logarithmicCorrelationEndpointBound
    (t : ℝ) (h m K : ℕ) : ℝ :=
  ‖(Complex.exp (Complex.I *
      ((logarithmicCorrelationPhase t h (m + 1) -
        logarithmicCorrelationPhase t h m : ℝ) : ℂ)) - 1)⁻¹‖ +
  ‖(Complex.exp (Complex.I *
      ((logarithmicCorrelationPhase t h (m + (K + 1)) -
        logarithmicCorrelationPhase t h (m + K) : ℝ) : ℂ)) - 1)⁻¹‖ +
  (Real.cot ((logarithmicCorrelationPhase t h (m + (K + 1)) -
      logarithmicCorrelationPhase t h (m + K)) / 2) -
    Real.cot ((logarithmicCorrelationPhase t h (m + 1) -
      logarithmicCorrelationPhase t h m) / 2)) / 2

/-- The first complete differencing step for a logarithmic zeta block: van der
Corput consumes the Kusmin--Landau bounds for every shifted autocorrelation. -/
theorem vanDerCorputZetaOscillationWithKusminLandau
    (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
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
            logarithmicCorrelationEndpointBound t ell m (N - ell - 1) := by
  apply vanDerCorputZetaOscillationOfCorrelationBounds t m
    (fun ell ↦ logarithmicCorrelationEndpointBound t ell m (N - ell - 1)) N L hL hLN
  intro ell hell
  rw [Finset.mem_Icc] at hell
  have hNell : 0 < N - ell := by omega
  have hlength : N - ell = (N - ell - 1) + 1 := by omega
  rw [hlength]
  exact norm_zetaOscillation_correlationSum_le_endpoint
    t ell m (N - ell - 1) ht hell.1 hm (fun k hk ↦ hturn ell (by simpa using hell) k hk)

/-- The same complete differencing step, with nonresonance checked only at the
start of each autocorrelation block. -/
theorem vanDerCorputZetaOscillationWithKusminLandauOfStartTurn
    (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
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
            logarithmicCorrelationEndpointBound t ell m (N - ell - 1) := by
  apply vanDerCorputZetaOscillationWithKusminLandau t m N L ht hm hL hLN
  intro ell hell k hk
  exact (logarithmicCorrelationPhase_forwardDifference_le_start k ht.le
    (by rw [Finset.mem_Icc] at hell; exact hell.1) hm).trans_lt (hstart ell hell)

/-- Nonresonance in the complete differencing step can be checked using the
elementary rational upper bound for the first logarithmic increment. -/
theorem vanDerCorputZetaOscillationWithKusminLandauOfFractionTurn
    (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hfrac : ∀ ell ∈ Finset.Icc 1 (L - 1),
      t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) < 2 * Real.pi) :
    (L : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N
      + 2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) *
            logarithmicCorrelationEndpointBound t ell m (N - ell - 1) := by
  apply vanDerCorputZetaOscillationWithKusminLandauOfStartTurn
    t m N L ht hm hL hLN
  intro ell hell
  rw [Finset.mem_Icc] at hell
  exact (logarithmicCorrelationPhase_forwardDifference_le_fraction
    ht.le hell.1 hm).trans_lt (hfrac ell (by simpa using hell))

end ZeroFreeRegion.VinogradovKorobov
