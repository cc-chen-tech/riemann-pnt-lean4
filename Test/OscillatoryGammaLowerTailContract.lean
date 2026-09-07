import HardyTheorem.OscillatoryGammaLowerTail

open Complex MeasureTheory HardyTheorem.OscillatoryGammaTail

-- No lower-cutoff power loss is allowed in this bound.
example {sigma c t A x : ℝ} (hs : sigma < 1) (hc : 0 ≤ c)
    (hA : 0 < A) (hAx : A ≤ x) (hgap : c * x < t) :
    ‖∫ u in A..x, (u : ℂ) ^ (-((sigma : ℂ) + I * t)) *
      Complex.exp (I * (c * u))‖ ≤ 2 * x ^ (1 - sigma) / (t - c * x) :=
  norm_intervalIntegral_mellin_linear_lower_le hs hc hA hAx hgap

-- The singular endpoint is handled using local integrability, not an assumed limit.
example {sigma c t x : ℝ} (hs : sigma < 1) (hc : 0 ≤ c)
    (hx : 0 < x) (hgap : c * x < t) :
    ‖∫ u in (0 : ℝ)..x, (u : ℂ) ^ (-((sigma : ℂ) + I * t)) *
      Complex.exp (I * (c * u))‖ ≤ 2 * x ^ (1 - sigma) / (t - c * x) :=
  norm_intervalIntegral_mellin_linear_zero_lower_le hs hc hx hgap

#print axioms norm_intervalIntegral_mellin_linear_lower_le
#print axioms norm_intervalIntegral_mellin_linear_zero_lower_le
