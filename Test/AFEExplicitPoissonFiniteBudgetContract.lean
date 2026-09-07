import HardyTheorem.AFEExplicitPoissonFiniteBudget

open HardyTheorem AFE Complex

-- Full finite-cutoff estimate, with no component norm estimates supplied as gates.
example {C₁ C₂ t : ℝ} {K N : ℕ}
    (hK : 6 ≤ K) (hN : 2 * K ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hfar : 2 * t ≤ 2 * Real.pi * (N : ℝ))
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    let M := Nat.ceil (t / (Real.pi * K))
    ‖((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (1 - s)) -
        (∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s)) -
        (∑ m ∈ Finset.Icc 1 K, poissonGammaTerm (1 / 2) t m)‖ ≤
      explicitPoissonCriticalFiniteConstant C₁ C₂ * (K : ℝ) ^ (-(1 / 2) : ℝ) *
          (1 + Real.log M) +
        ((K : ℝ) - 1 + (4 / Real.pi) * (harmonic (K - 2) : ℝ)) *
          (N : ℝ) ^ (-(1 / 2) : ℝ) :=
  norm_dirichlet_sum_sub_pole_sub_dualGamma_le
    hK hN htL htU hfar hC₁0 hC₂0 hC₁ hC₂

#print axioms norm_dirichlet_sum_sub_pole_sub_dualGamma_le
