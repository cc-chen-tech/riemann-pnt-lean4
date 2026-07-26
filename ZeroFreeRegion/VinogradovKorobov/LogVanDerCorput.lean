import ZeroFreeRegion.VinogradovKorobov.Harmonic
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

/-- Van der Corput with every logarithmic autocorrelation replaced by the
explicit `1 / ell` Kusmin--Landau estimate. -/
theorem vanDerCorputZetaOscillationExplicit
    (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
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
              (t * (ell : ℝ))) := by
  apply vanDerCorputZetaOscillationOfCorrelationBounds t m
    (fun ell ↦ 2 * Real.pi *
      (((m + (N - ell - 1) : ℕ) : ℝ) *
          (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) /
        (t * (ell : ℝ))) N L hL hLN
  intro ell hell
  rw [Finset.mem_Icc] at hell
  have hNell : 0 < N - ell := by omega
  have hlength : N - ell = (N - ell - 1) + 1 := by omega
  rw [hlength]
  exact norm_zetaOscillation_correlationSum_le_explicit
    t ell m (N - ell - 1) ht hell.1 hm (hmargin ell (by simpa using hell))

/-- The explicit autocorrelation contribution is bounded by one harmonic
factor and a denominator uniform in the shift. -/
theorem weightedExplicitCorrelationSum_le
    (t : ℝ) (m N L : ℕ) (ht : 0 < t) :
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) *
          (2 * Real.pi *
              (((m + (N - ell - 1) : ℕ) : ℝ) *
                  (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) /
            (t * (ell : ℝ)))) ≤
      (2 * Real.pi *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) / t) *
        ((L : ℝ) * (1 + Real.log L)) := by
  let D : ℝ :=
    ((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L
  let C : ℝ := 2 * Real.pi * D / t
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hterm : ∀ ell ∈ Finset.Icc 1 (L - 1),
      2 * Real.pi *
          (((m + (N - ell - 1) : ℕ) : ℝ) *
              (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) /
        (t * (ell : ℝ)) ≤ C * (ell : ℝ)⁻¹ := by
    intro ell hell
    rw [Finset.mem_Icc] at hell
    have haNat : m + (N - ell - 1) ≤ m + N := by omega
    have ha : ((m + (N - ell - 1) : ℕ) : ℝ) ≤ ((m + N : ℕ) : ℝ) := by
      exact_mod_cast haNat
    have hellLNat : ell ≤ L := hell.2.trans (Nat.sub_le L 1)
    have hellL : (ell : ℝ) ≤ (L : ℝ) := by exact_mod_cast hellLNat
    have hsecond :
        ((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1 ≤
          ((m + N : ℕ) : ℝ) + L + 1 := by
      linarith
    have hsmallD :
        ((m + (N - ell - 1) : ℕ) : ℝ) *
              (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell ≤ D := by
      dsimp only [D]
      exact add_le_add (mul_le_mul ha hsecond (by positivity) (by positivity)) hellL
    have hnum :
        2 * Real.pi *
            (((m + (N - ell - 1) : ℕ) : ℝ) *
                (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
          2 * Real.pi * D :=
      mul_le_mul_of_nonneg_left hsmallD (by positivity)
    have hellpos : 0 < (ell : ℝ) := Nat.cast_pos.mpr hell.1
    have hdenpos : 0 < t * (ell : ℝ) := mul_pos ht hellpos
    calc
      2 * Real.pi *
            (((m + (N - ell - 1) : ℕ) : ℝ) *
                (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) /
          (t * (ell : ℝ)) ≤
          2 * Real.pi * D / (t * (ell : ℝ)) :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      _ = C * (ell : ℝ)⁻¹ := by
        dsimp only [C]
        field_simp
  have hsum :
      (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) *
            (2 * Real.pi *
                (((m + (N - ell - 1) : ℕ) : ℝ) *
                    (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) /
              (t * (ell : ℝ)))) ≤
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * (C * (ell : ℝ)⁻¹) := by
    apply Finset.sum_le_sum
    intro ell hell
    apply mul_le_mul_of_nonneg_left (hterm ell hell)
    rw [Finset.mem_Icc] at hell
    exact sub_nonneg.mpr (by
      exact_mod_cast hell.2.trans (Nat.sub_le L 1))
  calc
    (∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) *
          (2 * Real.pi *
              (((m + (N - ell - 1) : ℕ) : ℝ) *
                  (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) /
            (t * (ell : ℝ)))) ≤
        ∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * (C * (ell : ℝ)⁻¹) := hsum
    _ = C * (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) * (ell : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      ring
    _ ≤ C * ((L : ℝ) * (1 + Real.log L)) :=
      mul_le_mul_of_nonneg_left (weighted_reciprocal_sum_le L) hC
    _ = (2 * Real.pi *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) / t) *
        ((L : ℝ) * (1 + Real.log L)) := by rfl

/-- Closed one-step van der Corput estimate: the autocorrelation finite sum is
replaced by a single harmonic factor. -/
theorem vanDerCorputZetaOscillationHarmonic
    (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
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
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) / t := by
  have hbase := vanDerCorputZetaOscillationExplicit
    t m N L ht hm hL hLN hmargin
  refine hbase.trans ?_
  apply add_le_add le_rfl
  have hsum := weightedExplicitCorrelationSum_le t m N L ht
  have hfactor : 0 ≤ 2 * ((N : ℝ) + ((L : ℝ) - 1)) := by
    apply mul_nonneg (by norm_num)
    exact add_nonneg (Nat.cast_nonneg N)
      (sub_nonneg.mpr (by exact_mod_cast hL))
  calc
    2 * ((N : ℝ) + ((L : ℝ) - 1)) *
        (∑ ell ∈ Finset.Icc 1 (L - 1),
          ((L : ℝ) - (ell : ℝ)) *
            (2 * Real.pi *
                (((m + (N - ell - 1) : ℕ) : ℝ) *
                    (((m + (N - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) /
              (t * (ell : ℝ)))) ≤
        2 * ((N : ℝ) + ((L : ℝ) - 1)) *
          ((2 * Real.pi *
              (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) / t) *
            ((L : ℝ) * (1 + Real.log L))) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = 4 * Real.pi * ((N : ℝ) + ((L : ℝ) - 1)) * L *
          (1 + Real.log L) *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) / t := by
      ring

/-- Normalized closed estimate after dividing the van der Corput inequality by
the square of the differencing length. -/
theorem norm_zetaOscillation_sum_sq_le_harmonic
    (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
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
          (t * L) := by
  have hbase := vanDerCorputZetaOscillationHarmonic
    t m N L ht hm hL hLN hmargin
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  calc
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 =
        ((L : ℝ) ^ 2 *
          ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2) /
            (L : ℝ) ^ 2 := by field_simp
    _ ≤ ((L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N +
        4 * Real.pi * ((N : ℝ) + ((L : ℝ) - 1)) * L *
          (1 + Real.log L) *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) / t) /
        (L : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hbase (sq_nonneg (L : ℝ))
    _ = (((N : ℝ) + ((L : ℝ) - 1)) * N) / L +
        4 * Real.pi * ((N : ℝ) + ((L : ℝ) - 1)) *
          (1 + Real.log L) *
          (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) /
          (t * L) := by
      field_simp

/-- A concrete formal nontriviality gate: whenever the closed harmonic bound
is strictly below the square of the trivial length bound, the logarithmic
exponential sum is strictly smaller than `N`. -/
theorem norm_zetaOscillation_sum_lt_trivial_of_harmonic
    (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
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
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ < N := by
  have hsq := norm_zetaOscillation_sum_sq_le_harmonic
    t m N L ht hm hL hLN hmargin
  have hlt := hsq.trans_lt hsaving
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [norm_nonneg (∑ n ∈ Finset.range N, zetaOscillation t (m + n))]

/-- A genuine nontrivial logarithmic exponential-sum family.  At square
height, a block of length `m` starting at `m` has norm strictly below its
trivial bound once `m` is at least `2000`. -/
theorem norm_zetaOscillation_square_height_block_lt_trivial
    (m : ℕ) (hm : 2000 ≤ m) :
    ‖∑ n ∈ Finset.range m,
        zetaOscillation ((m : ℝ) ^ 2) (m + n)‖ < m := by
  have hmpos : 0 < m := by omega
  have hxpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
  have ht : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hxpos
  apply norm_zetaOscillation_sum_lt_trivial_of_harmonic
    ((m : ℝ) ^ 2) m m 2 ht hmpos (by norm_num) (by omega)
  · intro ell hell
    rw [Finset.mem_Icc] at hell
    have hell1 : ell = 1 := by omega
    subst ell
    let a : ℕ := m + (m - 1 - 1)
    have hma : m ≤ a := by
      dsimp only [a]
      omega
    have hmaReal : (m : ℝ) ≤ (a : ℝ) := by exact_mod_cast hma
    have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    have hfirstDen : 0 < (m : ℝ) * ((m : ℝ) + 1 + 1) := by positivity
    have hfirst :
        (m : ℝ) ^ 2 / ((m : ℝ) * ((m : ℝ) + 1 + 1)) ≤ 1 := by
      apply (div_le_iff₀ hfirstDen).2
      nlinarith
    have hsecondDen : 0 < (a : ℝ) * ((a : ℝ) + 1 + 1) + 1 := by positivity
    have hmaSq : (m : ℝ) * (m : ℝ) ≤ (a : ℝ) * (a : ℝ) :=
      mul_self_le_mul_self hxpos.le hmaReal
    have hsecond :
        (m : ℝ) ^ 2 / ((a : ℝ) * ((a : ℝ) + 1 + 1) + 1) ≤ 1 := by
      apply (div_le_iff₀ hsecondDen).2
      nlinarith
    have htwo :
        (m : ℝ) ^ 2 / ((m : ℝ) * ((m : ℝ) + 1 + 1)) +
          (m : ℝ) ^ 2 /
            (((m + (m - 1 - 1) : ℕ) : ℝ) *
                (((m + (m - 1 - 1) : ℕ) : ℝ) + 1 + 1) + 1) ≤ 2 := by
      dsimp only [a] at hsecond
      nlinarith [add_le_add hfirst hsecond]
    norm_num only [Nat.cast_one, mul_one]
    exact htwo.trans (by nlinarith [Real.two_le_pi])
  · let x : ℝ := m
    have hx : 2000 ≤ x := by
      dsimp only [x]
      exact_mod_cast hm
    have hx0 : 0 ≤ x := by positivity
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hlog : 1 + Real.log (2 : ℝ) ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
      norm_num at h ⊢
      linarith
    have hlog0 : 0 ≤ 1 + Real.log (2 : ℝ) := by
      have : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      linarith
    have hA : x + 1 ≤ 2 * x := by linarith
    have hD0 : 0 ≤ (2 * x) * (2 * x + 3) + 2 := by positivity
    have hD : (2 * x) * (2 * x + 3) + 2 ≤ 12 * x ^ 2 := by
      have hx1 : 0 ≤ x - 1 := by linarith
      have hfactor : 0 ≤ 2 * (4 * x + 1) * (x - 1) :=
        mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hx1
      nlinarith
    have hnum :
        4 * Real.pi * (x + 1) * (1 + Real.log (2 : ℝ)) *
            ((2 * x) * (2 * x + 3) + 2) ≤
          768 * x ^ 3 := by
      calc
        4 * Real.pi * (x + 1) * (1 + Real.log (2 : ℝ)) *
              ((2 * x) * (2 * x + 3) + 2) ≤
            4 * 4 * (2 * x) * 2 * (12 * x ^ 2) := by
          gcongr
        _ = 768 * x ^ 3 := by ring
    have hdenpos : 0 < x ^ 2 * 2 := by positivity
    have hsecond :
        4 * Real.pi * (x + 1) * (1 + Real.log (2 : ℝ)) *
              ((2 * x) * (2 * x + 3) + 2) / (x ^ 2 * 2) ≤
          384 * x := by
      calc
        4 * Real.pi * (x + 1) * (1 + Real.log (2 : ℝ)) *
              ((2 * x) * (2 * x + 3) + 2) / (x ^ 2 * 2) ≤
            (768 * x ^ 3) / (x ^ 2 * 2) :=
          div_le_div_of_nonneg_right hnum hdenpos.le
        _ = 384 * x := by field_simp; ring
    have hfirst : (x + 1) * x / 2 ≤ 3 * x ^ 2 / 4 := by
      nlinarith [sq_nonneg x]
    have htotal :
        (x + 1) * x / 2 +
            4 * Real.pi * (x + 1) * (1 + Real.log (2 : ℝ)) *
              ((2 * x) * (2 * x + 3) + 2) / (x ^ 2 * 2) < x ^ 2 := by
      calc
        (x + 1) * x / 2 +
            4 * Real.pi * (x + 1) * (1 + Real.log (2 : ℝ)) *
              ((2 * x) * (2 * x + 3) + 2) / (x ^ 2 * 2) ≤
            3 * x ^ 2 / 4 + 384 * x := add_le_add hfirst hsecond
        _ < x ^ 2 := by nlinarith [sq_nonneg x]
    dsimp only [x] at htotal
    (convert htotal using 1; norm_num [Nat.cast_add]; ring)

end ZeroFreeRegion.VinogradovKorobov
