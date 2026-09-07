import HardyTheorem.AFEExplicitPoissonInnerMode

open HardyTheorem AFE Complex Set MeasureTheory

-- Actual Gamma coefficient and both smoothing transitions, with no assumed error bound.
example {C₁ sigma x t : ℝ} {N m : ℕ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1) (hx : 1 < x) (hxN : x ≤ (N : ℝ))
    (hm : 1 ≤ m) (hgap : 2 * Real.pi * (m : ℝ) * x < t)
    (hfar : 2 * t ≤ 2 * Real.pi * (m : ℝ) * (N : ℝ))
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    let s : ℂ := (sigma : ℂ) + I * t
    ‖explicitPoissonMode sigma x N t (-(m : ℤ)) -
      ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ^ (s - 1) *
        (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))‖ ≤
      ((3 + 8 * C₁) / Real.pi) * (x - 1) ^ (-sigma) /
        (t / (2 * Real.pi * x) - m) +
      (1 + 4 / (Real.pi * m)) * (N : ℝ) ^ (-sigma) :=
  norm_explicitPoissonMode_sub_gamma_le hs0 hs1 hx hxN hm hgap hfar hC₁0 hC₁

#print axioms norm_explicitPoissonMode_sub_gamma_le
