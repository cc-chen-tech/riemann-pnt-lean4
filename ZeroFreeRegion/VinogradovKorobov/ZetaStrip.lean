import ZeroFreeRegion.VinogradovKorobov.ZetaApproximation

open Complex Set

namespace ZeroFreeRegion.VinogradovKorobov

/-- The general first zeta approximation on the positive-height strip, with
the real cutoff fixed to `2t`. -/
theorem stripZetaFirstApprox_dirichletInterval :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ sigma t : ℝ,
      (1 / 4 : ℝ) ≤ sigma → sigma ≤ 2 → 1 ≤ t →
        ∃ R : ℂ,
          riemannZeta ((sigma : ℂ) + I * t) =
            dirichletInterval sigma t 1 (Nat.floor (2 * t)) +
              (2 * t : ℂ) ^ (1 - ((sigma : ℂ) + I * t)) /
                (((sigma : ℂ) + I * t) - 1) + R ∧
          ‖R‖ ≤ C * (2 * t) ^ (-sigma) := by
  obtain ⟨C, hC, happ⟩ := HardyTheorem.exists_riemannZeta_first_approximation
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma hsigmatwo ht
  let s : ℂ := (sigma : ℂ) + I * t
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hsne : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [s, add_im, ofReal_im, mul_im, I_re, ofReal_im, I_im,
      ofReal_re, zero_mul, one_mul, zero_add, one_im] at him
    linarith
  have hx : (1 : ℝ) ≤ 2 * t := by linarith
  have him : |s.im| ≤ (2 * t) / 2 := by
    simp only [s, add_im, ofReal_im, mul_im, I_re, ofReal_im, I_im,
      ofReal_re, zero_mul, one_mul, zero_add, abs_of_pos htpos]
    linarith
  obtain ⟨R, hzeta, hR⟩ := happ s (2 * t)
    (by simpa [s] using hsigma)
    (by simpa [s] using hsigmatwo)
    hsne hx him
  dsimp only [s] at hzeta hR
  have hcast : (((2 * t : ℝ) : ℂ)) = 2 * (t : ℂ) := by norm_num
  rw [hcast] at hzeta
  refine ⟨R, ?_, ?_⟩
  · rw [dirichletInterval_one_eq_sum_Icc]
    exact hzeta
  · simpa using hR

/-- A parameterized zeta growth estimate valid throughout the strip
`1/4 ≤ σ ≤ 2`.  It isolates the elementary pole term and applies the
logarithmic harmonic estimate to the long Dirichlet tail. -/
theorem norm_riemannZeta_strip_le_harmonic_of_scale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ sigma t : ℝ,
      (1 / 4 : ℝ) ≤ sigma → sigma ≤ 2 → 1 ≤ t →
        ∀ m L : ℕ,
          1 ≤ m → m ≤ Nat.floor (2 * t) + 1 → 1 ≤ L →
          t * ((L - 1 : ℕ) : ℝ) ≤
            (m : ℝ) * ((m : ℝ) + 2) →
          ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
            (m - 1 : ℕ) +
              dirichletWeight sigma m *
                max (L : ℝ)
                  (Real.sqrt (zetaOscillationHarmonicBound t m
                    (Nat.floor (2 * t) + 1 - m) L)) +
              ‖(2 * t : ℂ) ^ (1 - ((sigma : ℂ) + I * t)) /
                (((sigma : ℂ) + I * t) - 1)‖ +
              C * (2 * t) ^ (-sigma) := by
  obtain ⟨C, hC, happ⟩ := stripZetaFirstApprox_dirichletInterval
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma hsigmatwo ht m L hm hcut hL hscale
  obtain ⟨R, hzeta, hR⟩ := happ sigma t hsigma hsigmatwo ht
  let M := Nat.floor (2 * t)
  let P : ℂ := (2 * t : ℂ) ^ (1 - ((sigma : ℂ) + I * t)) /
    (((sigma : ℂ) + I * t) - 1)
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hsigma0 : 0 ≤ sigma := by linarith
  have hsplit :
      dirichletInterval sigma t 1 M =
        dirichletInterval sigma t 1 (m - 1) +
          dirichletInterval sigma t m (M + 1 - m) := by
    have hs := dirichletInterval_add_length
      sigma t 1 (m - 1) (M + 1 - m)
    have hlength : (m - 1) + (M + 1 - m) = M := by
      dsimp only [M] at hcut ⊢
      omega
    have hstart : 1 + (m - 1) = m := by omega
    rw [hlength, hstart] at hs
    exact hs
  have hinit :
      ‖dirichletInterval sigma t 1 (m - 1)‖ ≤ (m - 1 : ℕ) :=
    norm_dirichletInterval_le_length sigma t 1 (m - 1)
      hsigma0 (by norm_num)
  have htail :
      ‖dirichletInterval sigma t m (M + 1 - m)‖ ≤
        dirichletWeight sigma m *
          max (L : ℝ)
            (Real.sqrt
              (zetaOscillationHarmonicBound t m (M + 1 - m) L)) :=
    norm_dirichletInterval_le_weight_mul_harmonic_of_scale
      sigma t m (M + 1 - m) L hsigma0 htpos (by omega) hL hscale
  change riemannZeta ((sigma : ℂ) + I * t) =
      dirichletInterval sigma t 1 M + P + R at hzeta
  rw [hsplit] at hzeta
  rw [hzeta]
  calc
    ‖(dirichletInterval sigma t 1 (m - 1) +
          dirichletInterval sigma t m (M + 1 - m) + P) + R‖ ≤
        ‖dirichletInterval sigma t 1 (m - 1) +
          dirichletInterval sigma t m (M + 1 - m) + P‖ + ‖R‖ :=
      norm_add_le _ _
    _ ≤ (‖dirichletInterval sigma t 1 (m - 1) +
          dirichletInterval sigma t m (M + 1 - m)‖ + ‖P‖) + ‖R‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖dirichletInterval sigma t 1 (m - 1)‖ +
          ‖dirichletInterval sigma t m (M + 1 - m)‖) + ‖P‖) + ‖R‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ (m - 1 : ℕ) +
          dirichletWeight sigma m *
            max (L : ℝ)
              (Real.sqrt
                (zetaOscillationHarmonicBound t m (M + 1 - m) L)) +
          ‖P‖ + C * (2 * t) ^ (-sigma) := by
      exact add_le_add (add_le_add (add_le_add hinit htail) le_rfl) hR

end ZeroFreeRegion.VinogradovKorobov
