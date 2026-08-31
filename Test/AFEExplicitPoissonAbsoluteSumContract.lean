import HardyTheorem.AFEExplicitPoissonAbsoluteSum

open HardyTheorem AFE

-- Absolute convergence and the exact signed-index reassembly are conclusions.
example {C₁ C₂ sigma N t : ℝ} {K : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * (K : ℝ) ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    let f := explicitPoissonMode sigma ((K : ℝ) + 1) N t
    Summable (fun m : ℕ => ‖f ((m + 1 : ℕ) : ℤ)‖ + ‖f (-((m + 1 : ℕ) : ℤ))‖) ∧
      Summable f ∧
      (∑' k : ℤ, f k) = f 0 +
        ∑' m : ℕ, (f ((m + 1 : ℕ) : ℤ) + f (-((m + 1 : ℕ) : ℤ))) :=
  explicitPoissonMode_summable_and_tsum_pairs
    hs hK hN htL htU hC₁0 hC₂0 hC₁ hC₂

#print axioms explicitPoissonMode_summable_and_tsum_pairs
