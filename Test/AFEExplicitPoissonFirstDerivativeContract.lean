import HardyTheorem.AFEExplicitPoissonFirstDerivative

open HardyTheorem AFE Complex Set MeasureTheory

-- A true 1/g estimate, independent of N, with no assumed primitive bound.
example {F : ℝ → ℝ} {C₁ sigma x N g : ℝ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (hg : 0 < g)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hF : ∀ u : ℝ, 0 < u → ContDiffAt ℝ 2 F u)
    (hmono : MonotoneOn (deriv F) (Icc (x - 1) (N + 1)) ∨
      AntitoneOn (deriv F) (Icc (x - 1) (N + 1)))
    (hgap : ∀ u ∈ Icc (x - 1) (N + 1), g ≤ |deriv F u|) :
    ‖∫ u in (x - 1)..(N + 1), explicitComplexMellinAmplitude sigma x N u *
      Complex.exp (I * F u)‖ ≤ 16 * C₁ * (x - 1) ^ (-sigma) / g :=
  norm_explicitMellin_phaseIntegral_le_firstDerivative hs hx hxN hg hC₁0 hC₁ hF hmono hgap

#print axioms norm_explicitMellin_phaseIntegral_le_firstDerivative
