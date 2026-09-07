import HardyTheorem.AFEExplicitPoissonInnerSum

open HardyTheorem AFE Complex Set MeasureTheory

-- The mode errors are summed without assuming a reciprocal-gap estimate.
example {C₁ sigma x t : ℝ} {N R : ℕ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1) (hx : 1 < x) (hxN : x ≤ (N : ℝ))
    (hbeta : (R : ℝ) + 1 ≤ t / (2 * Real.pi * x))
    (hfar : 2 * t ≤ 2 * Real.pi * (N : ℝ)) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ m ∈ Finset.Icc 1 R,
      ‖explicitPoissonMode sigma x N t (-(m : ℤ)) - poissonGammaTerm sigma t m‖) ≤
      ((3 + 8 * C₁) / Real.pi) * (x - 1) ^ (-sigma) * (harmonic R : ℝ) +
      ((R : ℝ) + (4 / Real.pi) * (harmonic R : ℝ)) * (N : ℝ) ^ (-sigma) :=
  sum_norm_explicitPoissonMode_sub_gamma_le_harmonic
    hs0 hs1 hx hxN hbeta hfar hC₁0 hC₁

-- The exact inner band K-2 follows from the height cell, not a postulated gap.
example {C₁ sigma t : ℝ} {K N : ℕ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1) (hK : 3 ≤ K) (hN : K + 1 ≤ N)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (hfar : 2 * t ≤ 2 * Real.pi * (N : ℝ)) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∑ m ∈ Finset.Icc 1 (K - 2),
      ‖explicitPoissonMode sigma ((K : ℝ) + 1) N t (-(m : ℤ)) - poissonGammaTerm sigma t m‖) ≤
      ((3 + 8 * C₁) / Real.pi) * (K : ℝ) ^ (-sigma) * (harmonic (K - 2) : ℝ) +
      (((K - 2 : ℕ) : ℝ) + (4 / Real.pi) * (harmonic (K - 2) : ℝ)) * (N : ℝ) ^ (-sigma) :=
  sum_norm_explicitPoissonMode_inner_sqrt_sub_gamma_le
    hs0 hs1 hK hN htL hfar hC₁0 hC₁

#print axioms sum_norm_explicitPoissonMode_sub_gamma_le_harmonic
#print axioms sum_norm_explicitPoissonMode_inner_sqrt_sub_gamma_le
