import HardyTheorem.AFEExplicitPoissonSecondDerivative

open HardyTheorem AFE Complex Set MeasureTheory

-- The amplitude variation is proved, not an analytic input; no length factor appears.
example {F : ℝ → ℝ} {C₁ sigma x N a b r : ℝ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N)
    (hxa : x - 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N + 1) (hr : 0 < r)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hF : ∀ u : ℝ, 0 < u → ContDiffAt ℝ 2 F u)
    (hsecond : (∀ u ∈ Icc a b, r ≤ iteratedDeriv 2 F u) ∨
      (∀ u ∈ Icc a b, iteratedDeriv 2 F u ≤ -r)) :
    ‖∫ u in a..b, explicitComplexMellinAmplitude sigma x N u *
      Complex.exp (I * F u)‖ ≤ 12 * (4 * C₁ + 2) * a ^ (-sigma) / Real.sqrt r :=
  norm_explicitMellin_restricted_phaseIntegral_le_secondDerivative
    hs hx hxN hxa hab hbN hr hC₁0 hC₁ hF hsecond

#print axioms intervalIntegral_abs_explicitMellinDeriv_restricted_le
#print axioms norm_explicitMellin_restricted_integral_le_primitive
#print axioms norm_explicitMellin_restricted_phaseIntegral_le_secondDerivative
