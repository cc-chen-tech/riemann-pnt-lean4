import PrimeNumberTheorem.CarlsonHalfRangeInteriorPower

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem.CarlsonZeroDensity

example : ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
    ∀ x ∈ Icc (1 / 2 : ℝ) (2 / 3),
    (∫ t : ℝ, (Icc (2 * V) (5 * V / 2)).indicator (fun t =>
      ‖twoScaleMollifiedZetaError (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
        ((x : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
      K * V ^ (1 - (12 / 5 : ℝ) * ((x - 1 / 2) / (4 - 1 / 2))) *
        (1 + Real.log V) ^ 6 :=
  exists_eventually_halfRange_leftStrip_moment_le_powerLog

#print axioms exists_eventually_halfRange_leftStrip_moment_le_powerLog
