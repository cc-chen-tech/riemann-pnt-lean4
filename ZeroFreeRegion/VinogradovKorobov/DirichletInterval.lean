import ZeroFreeRegion.VinogradovKorobov.DirichletPrefix

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- A finite Dirichlet polynomial on the half-open integer interval
`[m, m + N)`. -/
noncomputable def dirichletInterval
    (sigma t : ℝ) (m N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico m (m + N),
    1 / (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)

/-- Consecutive Dirichlet intervals concatenate exactly. -/
lemma dirichletInterval_add_length
    (sigma t : ℝ) (m N₁ N₂ : ℕ) :
    dirichletInterval sigma t m (N₁ + N₂) =
      dirichletInterval sigma t m N₁ +
        dirichletInterval sigma t (m + N₁) N₂ := by
  unfold dirichletInterval
  rw [show m + (N₁ + N₂) = (m + N₁) + N₂ by omega]
  exact (Finset.sum_Ico_consecutive
    (fun n ↦ 1 / (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t))
    (m := m) (n := m + N₁) (k := (m + N₁) + N₂)
    (by omega) (by omega)).symm

/-- A long interval of length `q * B` is the sum of `q` consecutive blocks
of length `B`. -/
lemma dirichletInterval_mul_length
    (sigma t : ℝ) (m q B : ℕ) :
    dirichletInterval sigma t m (q * B) =
      ∑ j ∈ Finset.range q,
        dirichletInterval sigma t (m + j * B) B := by
  induction q with
  | zero => simp [dirichletInterval]
  | succ q ih =>
      rw [Nat.succ_mul, dirichletInterval_add_length, ih,
        Finset.sum_range_succ]

/-- The scale-form logarithmic estimate on an interval of exactly `N`
integer terms. -/
theorem norm_dirichletInterval_le_weight_mul_harmonic_of_scale
    (sigma t : ℝ) (m N L : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hscale : t * ((L - 1 : ℕ) : ℝ) ≤
      (m : ℝ) * ((m : ℝ) + 2)) :
    ‖dirichletInterval sigma t m N‖ ≤
      dirichletWeight sigma m *
        max (L : ℝ)
          (Real.sqrt (zetaOscillationHarmonicBound t m N L)) := by
  cases N with
  | zero =>
      simp only [dirichletInterval, Nat.add_zero, Finset.Ico_self,
        Finset.sum_empty, norm_zero]
      exact mul_nonneg (dirichletWeight_nonneg sigma m)
        ((Real.sqrt_nonneg _).trans (le_max_right _ _))
  | succ N =>
      have hbound :=
        norm_dirichletBlock_le_weight_mul_harmonic_end_of_scale
          sigma t m N L hsigma ht hm hL hscale
      simpa only [dirichletInterval, Finset.sum_Ico_eq_sum_range,
        Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hbound

/-- Summed harmonic control for a long interval split into equal consecutive
blocks. -/
theorem norm_dirichletInterval_mul_le_sum_harmonic_of_scale
    (sigma t : ℝ) (m q B L : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hscale : ∀ j < q,
      t * ((L - 1 : ℕ) : ℝ) ≤
        ((m + j * B : ℕ) : ℝ) * (((m + j * B : ℕ) : ℝ) + 2)) :
    ‖dirichletInterval sigma t m (q * B)‖ ≤
      ∑ j ∈ Finset.range q,
        dirichletWeight sigma (m + j * B) *
          max (L : ℝ)
            (Real.sqrt
              (zetaOscillationHarmonicBound t (m + j * B) B L)) := by
  rw [dirichletInterval_mul_length]
  calc
    ‖∑ j ∈ Finset.range q,
        dirichletInterval sigma t (m + j * B) B‖ ≤
        ∑ j ∈ Finset.range q,
          ‖dirichletInterval sigma t (m + j * B) B‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range q,
        dirichletWeight sigma (m + j * B) *
          max (L : ℝ)
            (Real.sqrt
              (zetaOscillationHarmonicBound t (m + j * B) B L)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply norm_dirichletInterval_le_weight_mul_harmonic_of_scale
        sigma t (m + j * B) B L hsigma ht
      · omega
      · exact hL
      · exact hscale j (Finset.mem_range.mp hj)

end ZeroFreeRegion.VinogradovKorobov
