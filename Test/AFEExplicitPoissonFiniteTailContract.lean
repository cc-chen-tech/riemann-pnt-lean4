import HardyTheorem.AFEExplicitPoissonFiniteTail

open HardyTheorem AFE

-- The actual finite signed mode sum has the proven uniform far-tail error.
-- In particular no caller-supplied convergence or tail estimate is required.
example {C₁ C₂ sigma N t : ℝ} {K : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    let M := Nat.ceil (t / (Real.pi * K))
    let f := explicitPoissonMode sigma ((K : ℝ) + 1) N t
    ‖(∑' k : ℤ, f k) - f 0 -
        (∑ m ∈ Finset.Icc 1 M, f (m : ℤ)) -
        (∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ)))‖ ≤
      4 * explicitPoissonFarConstant C₁ C₂ sigma * (K : ℝ) ^ (-sigma) / Real.pi ^ 2 :=
  norm_explicitPoisson_tsum_sub_finite_modes_le
    hs hK hN htL htU hC₁0 hC₂0 hC₁ hC₂

#print axioms norm_explicitPoisson_tsum_sub_finite_modes_le
