import ZeroFreeRegion.VinogradovKorobov.ZetaStrip

open Complex
open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The cubic-log decay in Ford's short logarithmic exponential-sum bound.

Writing `lambda = log t / log m`, this is the exponential form of
`C * m ^ (1 - 1 / (D * lambda ^ 2))`.  The exponential form is the one
consumed by the later dyadic optimization. -/
noncomputable def fordShortSumScale
    (C D t : ℝ) (m : ℕ) : ℝ :=
  C * (m : ℝ) *
    Real.exp (-(Real.log (m : ℝ)) ^ 3 /
      (D * (Real.log t) ^ 2))

/-- A pointwise Ford-type estimate for every prefix of one logarithmic
oscillation block.

This is deliberately a local interface.  The hard Vinogradov step must
produce such a bound uniformly over the relevant starts and block lengths. -/
def FordShortSumPrefixBound
    (C D t : ℝ) (m N : ℕ) : Prop :=
  ∀ K ≤ N,
    ‖∑ n ∈ Finset.range K, zetaOscillation t (m + n)‖ ≤
      fordShortSumScale C D t m

/-- Abel transfer from an arbitrary uniform prefix bound to a finite
Dirichlet interval. -/
theorem norm_dirichletInterval_le_weight_mul_of_prefix_bound
    (sigma t : ℝ) (m N : ℕ) (B : ℝ)
    (hsigma : 0 ≤ sigma) (hm : 0 < m)
    (hprefix : ∀ K ≤ N,
      ‖∑ n ∈ Finset.range K, zetaOscillation t (m + n)‖ ≤ B) :
    ‖dirichletInterval sigma t m N‖ ≤
      dirichletWeight sigma m * B := by
  cases N with
  | zero =>
      have hB : 0 ≤ B := by
        simpa using hprefix 0 (by omega)
      simp only [dirichletInterval, Nat.add_zero, Finset.Ico_self,
        Finset.sum_empty, norm_zero]
      exact mul_nonneg (dirichletWeight_nonneg sigma m) hB
  | succ N =>
      rw [dirichletInterval, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
      apply norm_dirichletBlock_le_weight_mul sigma t m N B hsigma hm
      intro k hk
      exact hprefix (k + 1) (by omega)

/-- A Ford-type logarithmic short-sum estimate controls the corresponding
weighted Dirichlet interval with no additional loss. -/
theorem norm_dirichletInterval_le_fordShortSumScale
    (C D sigma t : ℝ) (m N : ℕ)
    (hsigma : 0 ≤ sigma) (hm : 0 < m)
    (hshort : FordShortSumPrefixBound C D t m N) :
    ‖dirichletInterval sigma t m N‖ ≤
      dirichletWeight sigma m * fordShortSumScale C D t m :=
  norm_dirichletInterval_le_weight_mul_of_prefix_bound
    sigma t m N (fordShortSumScale C D t m) hsigma hm hshort

/-- Blockwise Ford short-sum estimates control an arbitrary long Dirichlet
interval.  Only the final Euclidean remainder is bounded trivially. -/
theorem norm_dirichletInterval_le_sum_fordShortSumScale
    (C D sigma t : ℝ) (m N B : ℕ)
    (hsigma : 0 ≤ sigma) (hm : 0 < m) (hB : 0 < B)
    (hshort : ∀ j < N / B,
      FordShortSumPrefixBound C D t (m + j * B) B) :
    ‖dirichletInterval sigma t m N‖ ≤
      ∑ j ∈ Finset.range (N / B),
          dirichletWeight sigma (m + j * B) *
            fordShortSumScale C D t (m + j * B) +
        (N % B : ℕ) := by
  rw [dirichletInterval_division_blocks sigma t m N B hB]
  calc
    ‖(∑ j ∈ Finset.range (N / B),
          dirichletInterval sigma t (m + j * B) B) +
        dirichletInterval sigma t (m + (N / B) * B) (N % B)‖ ≤
        ‖∑ j ∈ Finset.range (N / B),
          dirichletInterval sigma t (m + j * B) B‖ +
        ‖dirichletInterval sigma t (m + (N / B) * B) (N % B)‖ :=
      norm_add_le _ _
    _ ≤ (∑ j ∈ Finset.range (N / B),
          ‖dirichletInterval sigma t (m + j * B) B‖) +
        ‖dirichletInterval sigma t (m + (N / B) * B) (N % B)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (∑ j ∈ Finset.range (N / B),
          dirichletWeight sigma (m + j * B) *
            fordShortSumScale C D t (m + j * B)) +
        (N % B : ℕ) := by
      gcongr with j hj
      · apply norm_dirichletInterval_le_fordShortSumScale
          C D sigma t (m + j * B) B hsigma
        · omega
        · exact hshort j (Finset.mem_range.mp hj)
      · exact norm_dirichletInterval_le_length sigma t
          (m + (N / B) * B) (N % B) hsigma (by omega)

/-- Ford short-sum inputs plugged into the existing first zeta
approximation.  This theorem performs only the deterministic block and Abel
transfers; proving the short-sum hypotheses is the remaining Vinogradov
mean-value problem. -/
theorem norm_riemannZeta_strip_le_sum_fordShortSumScale :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ C D sigma t : ℝ,
      (1 / 4 : ℝ) ≤ sigma → sigma ≤ 2 → 1 ≤ t →
        ∀ m B : ℕ,
          1 ≤ m → m ≤ Nat.floor (2 * t) + 1 → 0 < B →
          (∀ j < (Nat.floor (2 * t) + 1 - m) / B,
            FordShortSumPrefixBound C D t (m + j * B) B) →
          ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
            (m - 1 : ℕ) +
              ∑ j ∈ Finset.range
                  ((Nat.floor (2 * t) + 1 - m) / B),
                dirichletWeight sigma (m + j * B) *
                  fordShortSumScale C D t (m + j * B) +
              ((Nat.floor (2 * t) + 1 - m) % B : ℕ) +
              ‖(2 * t : ℂ) ^ (1 - ((sigma : ℂ) + I * t)) /
                (((sigma : ℂ) + I * t) - 1)‖ +
              A * (2 * t) ^ (-sigma) := by
  obtain ⟨A, hA, happ⟩ := stripZetaFirstApprox_dirichletInterval
  refine ⟨A, hA, ?_⟩
  intro C D sigma t hsigma hsigmatwo ht m B hm hcut hB hshort
  let M := Nat.floor (2 * t)
  let P : ℂ := (2 * t : ℂ) ^
      (1 - ((sigma : ℂ) + I * t)) /
    (((sigma : ℂ) + I * t) - 1)
  obtain ⟨R, hzeta, hR⟩ := happ sigma t hsigma hsigmatwo ht
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
  have htail :=
    norm_dirichletInterval_le_sum_fordShortSumScale
      C D sigma t m (M + 1 - m) B hsigma0 (by omega) hB
      (by simpa only [M] using hshort)
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
    _ ≤ ((m - 1 : ℕ) +
          (∑ j ∈ Finset.range ((M + 1 - m) / B),
              dirichletWeight sigma (m + j * B) *
                fordShortSumScale C D t (m + j * B)) +
          ((M + 1 - m) % B : ℕ) + ‖P‖) +
          A * (2 * t) ^ (-sigma) := by
      simpa only [add_assoc] using
        add_le_add
          (add_le_add (add_le_add hinit htail) le_rfl)
          hR
    _ = (m - 1 : ℕ) +
          (∑ j ∈ Finset.range
              ((Nat.floor (2 * t) + 1 - m) / B),
            dirichletWeight sigma (m + j * B) *
              fordShortSumScale C D t (m + j * B)) +
          ((Nat.floor (2 * t) + 1 - m) % B : ℕ) +
          ‖(2 * t : ℂ) ^ (1 - ((sigma : ℂ) + I * t)) /
            (((sigma : ℂ) + I * t) - 1)‖ +
          A * (2 * t) ^ (-sigma) := by
      rfl

end ZeroFreeRegion.VinogradovKorobov
