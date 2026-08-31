import HardyTheorem.AFEExplicitPoissonEndpointMode

open HardyTheorem AFE Complex Set MeasureTheory

-- Covers the dangerous m=K-1 endpoint as well as the other four nearby modes.
-- No assumed curvature bound, gap estimate, or N-dependent remainder is allowed.
example {C₁ sigma K N t : ℝ} {m : ℕ}
    (hs : 0 < sigma) (hK : 6 ≤ K) (hN : 2 * K ≤ N)
    (htL : 2 * Real.pi * K ^ 2 ≤ t) (htU : t ≤ 2 * Real.pi * (K + 1) ^ 2)
    (hm : K - 1 ≤ (m : ℝ)) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    ‖explicitPoissonMode sigma (K + 1) N t (-(m : ℤ))‖ ≤
      (12 * (4 * C₁ + 2) / Real.sqrt (Real.pi / 2) +
        4 * (1 + 4 * C₁) / Real.pi) * K ^ (-sigma) :=
  norm_explicitPoissonMode_near_sqrt_endpoint_le hs hK hN htL htU hm hC₁0 hC₁

#print axioms norm_explicitPoissonMode_near_sqrt_endpoint_le
