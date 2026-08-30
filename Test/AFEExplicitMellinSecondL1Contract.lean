import HardyTheorem.AFEExplicitMellinSecondL1

open HardyTheorem AFE MeasureTheory

example {sigma x N u : ℝ} (hs : 0 ≤ sigma) (hu : 0 < u) :
    ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖ ≤
      |explicitIntervalPlateauSecondDeriv x N u| * u ^ (-sigma) +
      2 * sigma * (|explicitIntervalPlateauDeriv x N u| * u ^ (-sigma - 1)) +
      sigma * (sigma + 1) * u ^ (-sigma - 2) :=
  norm_explicitMellinSecondDeriv_le_supported hs hu

-- The RHS must not depend on N; dropping transition support would fail this contract.
example {C₁ C₂ sigma x N : ℝ} (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    (∫ u in (x - 1)..(N + 1), ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖) ≤
      2 * (2 * C₂ + 2 * C₁ ^ 2) * (x - 1) ^ (-sigma) +
      (8 * sigma * C₁ + sigma) * (x - 1) ^ (-sigma - 1) :=
  intervalIntegral_norm_explicitMellinSecondDeriv_le hs hx hxN hC₁0 hC₂0 hC₁ hC₂

#print axioms norm_explicitMellinSecondDeriv_le_supported
#print axioms intervalIntegral_norm_explicitMellinSecondDeriv_le
