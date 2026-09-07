import HardyTheorem.AFEExplicitPoissonUniformIntegral

open HardyTheorem AFE Set MeasureTheory

-- No upper-cutoff dependence and no integrability or derivative gate on the RHS.
example {C₁ C₂ sigma x N t g : ℝ} {k : ℤ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (ht : 0 ≤ t) (hg : 0 < g)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (hgap : ∀ u ∈ Icc (x - 1) (N + 1), g ≤ |weightedPoissonVelocity t k u|) :
    ‖∫ u in (x - 1)..(N + 1), explicitComplexMellinAmplitude sigma x N u *
        Complex.exp (Complex.I * weightedPoissonPhase t k u)‖ ≤
      (1 / g ^ 2) *
        (2 * (2 * C₂ + 2 * C₁ ^ 2) * (x - 1) ^ (-sigma) +
          (8 * sigma * C₁ + sigma) * (x - 1) ^ (-sigma - 1)) +
      (6 * C₁ * t / g ^ 3) * ((x - 1) ^ (-sigma - 1) / (sigma + 1)) +
      ((3 * sigma + 2) * t / g ^ 3) * ((x - 1) ^ (-sigma - 2) / (sigma + 2)) +
      (3 * t ^ 2 / g ^ 4) * ((x - 1) ^ (-sigma - 3) / (sigma + 3)) :=
  norm_explicitPoissonIntegral_le_uniform hs hx hxN ht hg hC₁0 hC₂0 hC₁ hC₂ hgap

#print axioms norm_explicitPoissonSecondQuotientDerivative_le_supportedGap
#print axioms norm_explicitPoissonIntegral_le_uniform
