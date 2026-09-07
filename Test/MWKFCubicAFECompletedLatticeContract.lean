import PrimeNumberTheorem.MWKFCubicAFECompletedLattice

open PrimeNumberTheorem.MWKFCubic

#check summable_cubicAFECompletedLatticePower
#check tsum_cubicAFECompletedLatticePower_le
#check cubicAFECompletedLatticeConstant_nonneg
#check measurable_cubicAFECompletedHalfLinePower
#check cubicAFECompletedHalfLinePower_le_endpoint

-- At J=1 the endpoint is 1/4 and is excluded, not the old 1/2.
example : cubicAFECompletedHalfLinePower 1 1 (1 / 4) = 0 := by
  norm_num [cubicAFECompletedHalfLinePower, cubicAFECompletionLowerEndpoint]

-- A nonintegral positive modulus below 1 is allowed; no hidden s>=1.
example (b : ℝ) : Summable (fun δ : ℤ ↦
    cubicAFECompletedHalfLinePower 1 3 (((δ : ℝ) + b) / (1 / 3))) := by
  exact summable_cubicAFECompletedLatticePower (by norm_num) (by norm_num) 3 b

-- The constant must remain independent of the real translation b.
example (b : ℝ) :
    (∑' δ : ℤ, cubicAFECompletedHalfLinePower 1 2 (((δ : ℝ) + b) / 3)) ≤
      cubicAFECompletedLatticeConstant 1 2 3 := by
  exact tsum_cubicAFECompletedLatticePower_le (by norm_num) (by norm_num) 2 b
