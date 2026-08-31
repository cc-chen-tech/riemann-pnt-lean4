import HardyTheorem.AFEExplicitPoissonRestrictedCutoff

open HardyTheorem AFE Complex Set MeasureTheory

-- The interval may end inside the plateau: no false zero-boundary premise.
example {F : ℝ → ℝ} {C₁ sigma x N a b g : ℝ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N)
    (hxa : x - 1 ≤ a) (hab : a ≤ b) (hbN : b ≤ N + 1) (hg : 0 < g)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hF : ∀ u : ℝ, 0 < u → ContDiffAt ℝ 2 F u)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨ AntitoneOn (deriv F) (Icc a b))
    (hgap : ∀ u ∈ Icc a b, g ≤ |deriv F u|) :
    ‖∫ u in a..b, explicitComplexMellinAmplitude sigma x N u *
      Complex.exp (I * F u)‖ ≤ 4 * (1 + 4 * C₁) * a ^ (-sigma) / g :=
  norm_explicitMellin_restricted_phaseIntegral_le_firstDerivative
    hs hx hxN hxa hab hbN hg hC₁0 hC₁ hF hmono hgap

-- The transfer theorem keeps the right boundary and the exact derivative mass.
example {A A' : ℝ → ℝ} {E : ℝ → ℂ} {a b B : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hA : ∀ u ∈ Icc a b, HasDerivAt A (A' u) u)
    (hAd : ContinuousOn A' (Icc a b)) (hE : ContinuousOn E (Ioi 0))
    (hprim : ∀ v ∈ Icc a b, ‖∫ u in a..v, E u‖ ≤ B) :
    ‖∫ u in a..b, A u • E u‖ ≤ (|A b| + ∫ u in a..b, |A' u|) * B :=
  norm_intervalIntegral_real_smul_le_primitive ha hab hA hAd hE hprim

#print axioms norm_intervalIntegral_real_smul_le_primitive
#print axioms intervalIntegral_abs_plateauDeriv_restricted_le
#print axioms norm_explicitPlateau_restricted_integral_le_primitive
#print axioms norm_explicitMellin_restricted_phaseIntegral_le_firstDerivative
