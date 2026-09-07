import HardyTheorem.AFEExplicitPoissonSqrtBands

open HardyTheorem AFE

example {C₁ sigma N t : ℝ} {K : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    let M := Nat.ceil (t / (Real.pi * K))
    (∑ m ∈ Finset.Icc (K + 4) M,
      ‖explicitPoissonMode sigma ((K : ℝ) + 1) N t (-(m : ℤ))‖) ≤
      (8 * C₁ * (K : ℝ) ^ (-sigma) / Real.pi) * (1 + Real.log M) :=
  sum_norm_explicitPoissonMode_sqrt_above_le_log hs hK hN htL htU hC₁0 hC₁

example {C₁ sigma N t : ℝ} {K : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ m ∈ Finset.Icc (K - 1) (K + 3),
      ‖explicitPoissonMode sigma ((K : ℝ) + 1) N t (-(m : ℤ))‖) ≤
      5 * (12 * (4 * C₁ + 2) / Real.sqrt (Real.pi / 2) +
        4 * (1 + 4 * C₁) / Real.pi) * (K : ℝ) ^ (-sigma) :=
  sum_norm_explicitPoissonMode_five_sqrt_endpoints_le hs hK hN htL htU hC₁0 hC₁

#print axioms sum_norm_explicitPoissonMode_sqrt_above_le_log
#print axioms sum_norm_explicitPoissonMode_five_sqrt_endpoints_le
