import HardyTheorem.AFEExplicitPoissonCutoffLimit

open HardyTheorem AFE Complex

-- The upper cutoff has disappeared from the actual zeta estimate.
example {C₁ C₂ t : ℝ} {K : ℕ} (hK : 6 ≤ K)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    let M := Nat.ceil (t / (Real.pi * K))
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s)) -
        (∑ m ∈ Finset.Icc 1 K, poissonGammaTerm (1 / 2) t m)‖ ≤
      explicitPoissonCriticalFiniteConstant C₁ C₂ * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        (1 + Real.log M) :=
  norm_riemannZeta_sub_primal_sub_dualGamma_le hK htL htU hC₁0 hC₂0 hC₁ hC₂

#print axioms norm_riemannZeta_sub_primal_sub_dualGamma_le
