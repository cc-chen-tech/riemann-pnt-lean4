import HardyTheorem.AFEExplicitPoissonCriticalEndpoints

open HardyTheorem AFE Complex

example (t : ℝ) {K : ℕ} (hK : 6 ≤ K) :
    (∑ m ∈ Finset.Icc (K - 1) K, ‖poissonGammaTerm (1 / 2) t m‖) ≤
      4 * (K : ℝ) ^ (-(1 / 2) : ℝ) :=
  sum_norm_poissonGammaTerm_two_endpoints_le t hK

example {N t : ℝ} {K : ℕ} (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    ‖explicitPoissonMode (1 / 2) ((K : ℝ) + 1) N t 0 -
        (N : ℂ) ^ (1 - s) / (1 - s)‖ ≤
      2 * (K : ℝ) ^ (-(1 / 2) : ℝ) + N ^ (-(1 / 2) : ℝ) :=
  norm_explicitPoissonZeroMode_critical_sqrt_sub_main_le hK hN htL

#print axioms sum_norm_poissonGammaTerm_two_endpoints_le
#print axioms norm_explicitPoissonZeroMode_critical_sqrt_sub_main_le
