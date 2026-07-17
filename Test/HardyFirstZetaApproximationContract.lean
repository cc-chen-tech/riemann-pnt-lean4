import HardyTheorem.FirstZetaApproximation

open Complex

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
