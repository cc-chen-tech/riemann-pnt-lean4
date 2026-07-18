import HardyTheorem.FirstZetaApproximation
import HardyTheorem.HardyIntegralUpperBound
import ZeroFreeRegion.VinogradovKorobov.DirichletInterval

open Complex Set
open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The first critical-line Dirichlet polynomial is exactly the interval
starting at one with length equal to its upper cutoff. -/
lemma dirichletInterval_one_eq_sum_Icc
    (sigma t : ℝ) (N : ℕ) :
    dirichletInterval sigma t 1 N =
      ∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((sigma : ℂ) + I * t) := by
  unfold dirichletInterval
  rw [show 1 + N = N + 1 by omega, Finset.Ico_add_one_right_eq_Icc]

/-- Hardy's first zeta approximation, rewritten in the interval language used
by the logarithmic exponential-sum estimates. -/
theorem criticalLineZetaFirstApprox_dirichletInterval :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Set.Icc T (2 * T) →
        ∃ R : ℂ,
          riemannZeta ((1 / 2 : ℂ) + I * t) =
            dirichletInterval (1 / 2) t 1
              (HardyTheorem.firstZetaApproximationCutoff T) + R ∧
          ‖R‖ ≤ C / Real.sqrt T := by
  obtain ⟨C, T0, hC, hT0, happ⟩ := HardyTheorem.criticalLineZetaFirstApprox
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T t hT ht
  obtain ⟨R, hzeta, hR⟩ := happ T t hT ht
  refine ⟨R, ?_, hR⟩
  rw [dirichletInterval_one_eq_sum_Icc]
  simpa only [show (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) by norm_num] using hzeta

/-- The critical-line initial Dirichlet segment has the sharp elementary
square-root bound. -/
theorem norm_criticalLine_dirichletInterval_one_le_two_sqrt
    (t : ℝ) (N : ℕ) :
    ‖dirichletInterval (1 / 2) t 1 N‖ ≤ 2 * Real.sqrt N := by
  rw [dirichletInterval_one_eq_sum_Icc]
  calc
    ‖∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((((1 / 2 : ℝ) : ℂ)) + I * t)‖ ≤
        ∑ n ∈ Finset.Icc 1 N,
          ‖1 / (n : ℂ) ^ ((((1 / 2 : ℝ) : ℂ)) + I * t)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn0 : n ≠ 0 := by omega
      rw [inv_nat_cpow_eq_dirichletWeight_mul_zetaOscillation
        hn0 (1 / 2) t]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (dirichletWeight_nonneg (1 / 2) n),
        norm_zetaOscillation, mul_one]
      unfold dirichletWeight
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
    _ ≤ 2 * Real.sqrt N :=
      HardyTheorem.sum_inv_sqrt_Icc_one_le_two_sqrt N

/-- A parameterized critical-line zeta growth estimate.  The initial segment
uses the trivial length bound, while the tail uses the harmonic logarithmic
block estimate. -/
theorem norm_riemannZeta_criticalLine_le_harmonic_of_scale :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Set.Icc T (2 * T) →
        ∀ m L : ℕ,
          1 ≤ m →
          m ≤ HardyTheorem.firstZetaApproximationCutoff T + 1 →
          1 ≤ L →
          t * ((L - 1 : ℕ) : ℝ) ≤
            (m : ℝ) * ((m : ℝ) + 2) →
          ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ≤
            (m - 1 : ℕ) +
              dirichletWeight (1 / 2) m *
                max (L : ℝ)
                  (Real.sqrt (zetaOscillationHarmonicBound t m
                    (HardyTheorem.firstZetaApproximationCutoff T + 1 - m) L)) +
              C / Real.sqrt T := by
  obtain ⟨C, T0, hC, hT0, happ⟩ :=
    criticalLineZetaFirstApprox_dirichletInterval
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T t hT ht m L hm hcut hL hscale
  obtain ⟨R, hzeta, hR⟩ := happ T t hT ht
  let M := HardyTheorem.firstZetaApproximationCutoff T
  have htpos : 0 < t := by linarith [hT0, hT, ht.1]
  have hsplit :
      dirichletInterval (1 / 2) t 1 M =
        dirichletInterval (1 / 2) t 1 (m - 1) +
          dirichletInterval (1 / 2) t m (M + 1 - m) := by
    have hs := dirichletInterval_add_length
      (1 / 2) t 1 (m - 1) (M + 1 - m)
    have hlength : (m - 1) + (M + 1 - m) = M := by
      dsimp only [M] at hcut ⊢
      omega
    have hstart : 1 + (m - 1) = m := by omega
    rw [hlength, hstart] at hs
    exact hs
  have hinit :
      ‖dirichletInterval (1 / 2) t 1 (m - 1)‖ ≤ (m - 1 : ℕ) :=
    norm_dirichletInterval_le_length (1 / 2) t 1 (m - 1)
      (by norm_num) (by norm_num)
  have htail :
      ‖dirichletInterval (1 / 2) t m (M + 1 - m)‖ ≤
        dirichletWeight (1 / 2) m *
          max (L : ℝ)
            (Real.sqrt
              (zetaOscillationHarmonicBound t m (M + 1 - m) L)) :=
    norm_dirichletInterval_le_weight_mul_harmonic_of_scale
      (1 / 2) t m (M + 1 - m) L (by norm_num) htpos (by omega) hL hscale
  change riemannZeta ((1 / 2 : ℂ) + I * t) =
      dirichletInterval (1 / 2) t 1 M + R at hzeta
  rw [hsplit] at hzeta
  rw [hzeta]
  calc
    ‖(dirichletInterval (1 / 2) t 1 (m - 1) +
          dirichletInterval (1 / 2) t m (M + 1 - m)) + R‖ ≤
        ‖dirichletInterval (1 / 2) t 1 (m - 1) +
          dirichletInterval (1 / 2) t m (M + 1 - m)‖ + ‖R‖ :=
      norm_add_le _ _
    _ ≤ (‖dirichletInterval (1 / 2) t 1 (m - 1)‖ +
          ‖dirichletInterval (1 / 2) t m (M + 1 - m)‖) + ‖R‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (m - 1 : ℕ) +
          dirichletWeight (1 / 2) m *
            max (L : ℝ)
              (Real.sqrt
                (zetaOscillationHarmonicBound t m (M + 1 - m) L)) +
          C / Real.sqrt T := by
      exact add_le_add (add_le_add hinit htail) hR

/-- The same parameterized growth estimate with the square-root bound for the
initial critical-line segment. -/
theorem norm_riemannZeta_criticalLine_le_harmonic_sqrt_initial_of_scale :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Set.Icc T (2 * T) →
        ∀ m L : ℕ,
          1 ≤ m →
          m ≤ HardyTheorem.firstZetaApproximationCutoff T + 1 →
          1 ≤ L →
          t * ((L - 1 : ℕ) : ℝ) ≤
            (m : ℝ) * ((m : ℝ) + 2) →
          ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ≤
            2 * Real.sqrt (m - 1 : ℕ) +
              dirichletWeight (1 / 2) m *
                max (L : ℝ)
                  (Real.sqrt (zetaOscillationHarmonicBound t m
                    (HardyTheorem.firstZetaApproximationCutoff T + 1 - m) L)) +
              C / Real.sqrt T := by
  obtain ⟨C, T0, hC, hT0, happ⟩ :=
    criticalLineZetaFirstApprox_dirichletInterval
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T t hT ht m L hm hcut hL hscale
  obtain ⟨R, hzeta, hR⟩ := happ T t hT ht
  let M := HardyTheorem.firstZetaApproximationCutoff T
  have htpos : 0 < t := by linarith [hT0, hT, ht.1]
  have hsplit :
      dirichletInterval (1 / 2) t 1 M =
        dirichletInterval (1 / 2) t 1 (m - 1) +
          dirichletInterval (1 / 2) t m (M + 1 - m) := by
    have hs := dirichletInterval_add_length
      (1 / 2) t 1 (m - 1) (M + 1 - m)
    have hlength : (m - 1) + (M + 1 - m) = M := by
      dsimp only [M] at hcut ⊢
      omega
    have hstart : 1 + (m - 1) = m := by omega
    rw [hlength, hstart] at hs
    exact hs
  have hinit :
      ‖dirichletInterval (1 / 2) t 1 (m - 1)‖ ≤
        2 * Real.sqrt (m - 1 : ℕ) :=
    norm_criticalLine_dirichletInterval_one_le_two_sqrt t (m - 1)
  have htail :
      ‖dirichletInterval (1 / 2) t m (M + 1 - m)‖ ≤
        dirichletWeight (1 / 2) m *
          max (L : ℝ)
            (Real.sqrt
              (zetaOscillationHarmonicBound t m (M + 1 - m) L)) :=
    norm_dirichletInterval_le_weight_mul_harmonic_of_scale
      (1 / 2) t m (M + 1 - m) L (by norm_num) htpos (by omega) hL hscale
  change riemannZeta ((1 / 2 : ℂ) + I * t) =
      dirichletInterval (1 / 2) t 1 M + R at hzeta
  rw [hsplit] at hzeta
  rw [hzeta]
  calc
    ‖(dirichletInterval (1 / 2) t 1 (m - 1) +
          dirichletInterval (1 / 2) t m (M + 1 - m)) + R‖ ≤
        ‖dirichletInterval (1 / 2) t 1 (m - 1) +
          dirichletInterval (1 / 2) t m (M + 1 - m)‖ + ‖R‖ :=
      norm_add_le _ _
    _ ≤ (‖dirichletInterval (1 / 2) t 1 (m - 1)‖ +
          ‖dirichletInterval (1 / 2) t m (M + 1 - m)‖) + ‖R‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 2 * Real.sqrt (m - 1 : ℕ) +
          dirichletWeight (1 / 2) m *
            max (L : ℝ)
              (Real.sqrt
                (zetaOscillationHarmonicBound t m (M + 1 - m) L)) +
          C / Real.sqrt T := by
      exact add_le_add (add_le_add hinit htail) hR

end ZeroFreeRegion.VinogradovKorobov
