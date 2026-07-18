import HardyTheorem.FirstZetaApproximation

open Complex
open Filter Asymptotics

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (x : ℝ),
    (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → s ≠ 1 → 1 ≤ x →
      |s.im| ≤ x / 2 →
        ∃ R : ℂ,
          riemannZeta s =
            (∑ n ∈ Finset.Icc 1 (Nat.floor x), 1 / (n : ℂ) ^ s) +
              (x : ℂ) ^ (1 - s) / (s - 1) + R ∧
          ‖R‖ ≤ C * x ^ (-s.re) :=
  HardyTheorem.exists_riemannZeta_first_approximation

example : ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
    T0 ≤ T → t ∈ Set.Icc T (2 * T) →
      ∃ R : ℂ,
        riemannZeta ((1 / 2 : ℂ) + I * t) =
          (∑ n ∈ Finset.Icc 1 (HardyTheorem.firstZetaApproximationCutoff T),
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) + R ∧
        ‖R‖ ≤ C / Real.sqrt T :=
  HardyTheorem.criticalLineZetaFirstApprox

example : ∃ c T0 : ℝ, 0 < c ∧ 1 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
    c * T ≤ ∫ t in T..(2 * T),
      ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ :=
  HardyTheorem.exists_integral_norm_riemannZeta_critical_line_ge_mul

example {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} :
    ‖∫ t in a..b, 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
      2 / (Real.sqrt n * Real.log n) :=
  HardyTheorem.norm_integral_inv_nat_cpow_criticalLine_le hn

example {N : ℕ} {a b : ℝ} :
    ‖∫ t in a..b, ∑ n ∈ Finset.Icc 2 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
      (2 / Real.log 2) *
        (Real.sqrt N * Real.sqrt (harmonic N : ℝ)) :=
  HardyTheorem.norm_integral_criticalLineDirichletTail_le

example {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ t in T..2 * T, ∑ n ∈ Finset.Icc 2 (HardyTheorem.firstZetaApproximationCutoff T),
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
      (2 / Real.log 2) *
        (Real.sqrt (4 * T) * Real.sqrt (1 + Real.log (4 * T))) :=
  HardyTheorem.norm_integral_criticalLineDirichletTail_cutoff_le hT

example :
    (fun T : ℝ =>
      ‖∫ t in T..2 * T,
        ∑ n ∈ Finset.Icc 2 (HardyTheorem.firstZetaApproximationCutoff T),
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖) =o[atTop]
      (fun T : ℝ => T) :=
  HardyTheorem.norm_integral_criticalLineDirichletTail_cutoff_isLittleO
