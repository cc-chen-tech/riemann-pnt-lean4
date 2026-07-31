import ZeroFreeRegion.VinogradovKorobov.DirichletBlock

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The closed harmonic upper bound produced by one logarithmic van der
Corput step. -/
noncomputable def zetaOscillationHarmonicBound
    (t : ℝ) (m N L : ℕ) : ℝ :=
  (((N : ℝ) + ((L : ℝ) - 1)) * N) / L +
    4 * Real.pi * ((N : ℝ) + ((L : ℝ) - 1)) *
      (1 + Real.log L) *
      (((m + N : ℕ) : ℝ) * (((m + N : ℕ) : ℝ) + L + 1) + L) /
      (t * L)

/-- For fixed height, starting point, and differencing length, the closed
harmonic bound increases with the length of the logarithmic block. -/
lemma zetaOscillationHarmonicBound_mono_length
    (t : ℝ) (m L : ℕ) {K N : ℕ}
    (ht : 0 < t) (hL : 1 ≤ L) (hKN : K ≤ N) :
    zetaOscillationHarmonicBound t m K L ≤
      zetaOscillationHarmonicBound t m N L := by
  have hKNR : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hLone : 1 ≤ (L : ℝ) := by exact_mod_cast hL
  have hlog : 0 ≤ 1 + Real.log (L : ℝ) := by
    have : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hLone
    linarith
  have hshiftK : 0 ≤ (K : ℝ) + ((L : ℝ) - 1) := by
    have hK0 : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith
  have hshiftN : 0 ≤ (N : ℝ) + ((L : ℝ) - 1) := by
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith
  have hcoefN :
      0 ≤ 4 * Real.pi * ((N : ℝ) + ((L : ℝ) - 1)) *
        (1 + Real.log (L : ℝ)) := by positivity
  have hmK : ((m + K : ℕ) : ℝ) ≤ ((m + N : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_left hKN m
  unfold zetaOscillationHarmonicBound
  apply add_le_add
  · gcongr
  · gcongr

/-- A single scale condition guarantees the nonresonance margin for every
shift in a logarithmic prefix. -/
lemma logarithmic_prefix_margin_of_scale
    (t : ℝ) (m K L : ℕ) (ht : 0 < t) (hm : 0 < m)
    (_hLK : L ≤ K)
    (hscale : t * ((L - 1 : ℕ) : ℝ) ≤
      (m : ℝ) * ((m : ℝ) + 2)) :
    ∀ ell ∈ Finset.Icc 1 (L - 1),
      t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
        t * (ell : ℝ) /
          (((m + (K - ell - 1) : ℕ) : ℝ) *
              (((m + (K - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤
        2 * Real.pi := by
  intro ell hell
  rw [Finset.mem_Icc] at hell
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell.1
  have hellL : (ell : ℝ) ≤ (L - 1 : ℕ) := by exact_mod_cast hell.2
  have hnum : t * (ell : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 2) :=
    (mul_le_mul_of_nonneg_left hellL ht.le).trans hscale
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hdenOne : 0 < (m : ℝ) * ((m : ℝ) + ell + 1) := by positivity
  have hnumOne :
      t * (ell : ℝ) ≤ (m : ℝ) * ((m : ℝ) + ell + 1) := by
    calc
      t * (ell : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 2) := hnum
      _ ≤ (m : ℝ) * ((m : ℝ) + ell + 1) := by
        apply mul_le_mul_of_nonneg_left _ hmR.le
        linarith
  have hfirst :
      t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) ≤ 1 :=
    (div_le_one hdenOne).2 hnumOne
  let a : ℕ := m + (K - ell - 1)
  have hmaNat : m ≤ a := by
    dsimp only [a]
    omega
  have hma : (m : ℝ) ≤ a := by exact_mod_cast hmaNat
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hell0 : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hprod :
      (m : ℝ) * ((m : ℝ) + ell + 1) ≤
        (a : ℝ) * ((a : ℝ) + ell + 1) := by
    apply mul_le_mul hma
    · linarith
    · positivity
    · exact ha0
  have hdenTwo :
      0 < (a : ℝ) * ((a : ℝ) + ell + 1) + ell := by positivity
  have hnumTwo :
      t * (ell : ℝ) ≤
        (a : ℝ) * ((a : ℝ) + ell + 1) + ell :=
    hnumOne.trans (hprod.trans (le_add_of_nonneg_right hell0))
  have hsecond :
      t * (ell : ℝ) /
          ((a : ℝ) * ((a : ℝ) + ell + 1) + ell) ≤ 1 :=
    (div_le_one hdenTwo).2 hnumTwo
  dsimp only [a] at hsecond
  calc
    t * (ell : ℝ) / ((m : ℝ) * ((m : ℝ) + ell + 1)) +
        t * (ell : ℝ) /
          (((m + (K - ell - 1) : ℕ) : ℝ) *
              (((m + (K - ell - 1) : ℕ) : ℝ) + ell + 1) + ell) ≤ 2 := by
      linarith
    _ ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]


/-- A common prefix envelope obtained by combining the trivial estimate for
prefixes shorter than `L` with the harmonic van der Corput estimate for all
longer prefixes. -/
theorem norm_zetaOscillation_prefix_le_max_sqrt_harmonic
    (t : ℝ) (m N L : ℕ) (ht : 0 < t) (hm : 0 < m)
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
        max (L : ℝ) (Real.sqrt Q) := by
  intro K hKN
  by_cases hKL : L ≤ K
  · have hsq := norm_zetaOscillation_sum_sq_le_harmonic
      t m K L ht hm hL hKL (hmargin K hKL hKN)
    have hsqQ :
        ‖∑ n ∈ Finset.range K, zetaOscillation t (m + n)‖ ^ 2 ≤ Q := by
      exact hsq.trans (by
        simpa only [zetaOscillationHarmonicBound] using
          henvelope K hKL hKN)
    exact (Real.le_sqrt_of_sq_le hsqQ).trans (le_max_right _ _)
  · have hKleL : K ≤ L := Nat.le_of_lt (Nat.lt_of_not_ge hKL)
    calc
      ‖∑ n ∈ Finset.range K, zetaOscillation t (m + n)‖ ≤
          ∑ n ∈ Finset.range K, ‖zetaOscillation t (m + n)‖ :=
        norm_sum_le _ _
      _ = K := by
        simp only [norm_zetaOscillation, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
      _ ≤ L := by exact_mod_cast hKleL
      _ ≤ max (L : ℝ) (Real.sqrt Q) := le_max_left _ _

/-- A harmonic envelope for all logarithmic prefixes transfers directly to a
weighted finite Dirichlet block. -/
theorem norm_dirichletBlock_le_weight_mul_max_sqrt_harmonic
    (sigma t : ℝ) (m N L : ℕ) (Q : ℝ)
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
      dirichletWeight sigma m * max (L : ℝ) (Real.sqrt Q) := by
  apply norm_dirichletBlock_le_weight_mul sigma t m N
    (max (L : ℝ) (Real.sqrt Q)) hsigma hm
  have hprefix := norm_zetaOscillation_prefix_le_max_sqrt_harmonic
    t m (N + 1) L ht hm hL Q hmargin henvelope
  intro k hk
  exact hprefix (k + 1) (by omega)

/-- The preceding transfer with the longest-prefix harmonic expression used
as the common envelope. -/
theorem norm_dirichletBlock_le_weight_mul_harmonic_end
    (sigma t : ℝ) (m N L : ℕ)
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
          (Real.sqrt (zetaOscillationHarmonicBound t m (N + 1) L)) := by
  apply norm_dirichletBlock_le_weight_mul_max_sqrt_harmonic
    sigma t m N L (zetaOscillationHarmonicBound t m (N + 1) L)
    hsigma ht hm hL hmargin
  intro K hLK hKN
  exact zetaOscillationHarmonicBound_mono_length t m L ht hL hKN

/-- A finite Dirichlet block estimate under the single practical scale
condition `t (L - 1) ≤ m (m + 2)`. -/
theorem norm_dirichletBlock_le_weight_mul_harmonic_end_of_scale
    (sigma t : ℝ) (m N L : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hscale : t * ((L - 1 : ℕ) : ℝ) ≤
      (m : ℝ) * ((m : ℝ) + 2)) :
    ‖∑ k ∈ Finset.range (N + 1),
        1 / ((m + k : ℕ) : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ≤
      dirichletWeight sigma m *
        max (L : ℝ)
          (Real.sqrt (zetaOscillationHarmonicBound t m (N + 1) L)) := by
  apply norm_dirichletBlock_le_weight_mul_harmonic_end
    sigma t m N L hsigma ht hm hL
  intro K hLK hKN
  exact logarithmic_prefix_margin_of_scale t m K L ht hm hLK hscale

end ZeroFreeRegion.VinogradovKorobov
