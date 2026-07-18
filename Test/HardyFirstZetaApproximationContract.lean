import HardyTheorem.FirstZetaApproximation

open Complex
open Filter Asymptotics

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
