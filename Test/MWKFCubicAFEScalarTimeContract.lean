import PrimeNumberTheorem.MWKFCubicAFEScalarTime

open PrimeNumberTheorem.MWKFCubic
open MeasureTheory Set

#check continuous_cubicAFEGammaProduct_zero_inv
#check continuous_cubicAFEScalar_joint_of_halfPlane
#check exists_norm_cubicAFEScalar_vertical_le_on_compact
#check continuous_cubicAFEWeightNormMass
#check integrable_cubicAFEPhysicalHeightMass

-- The left line used at the physical endpoint is included; this is not
-- merely the already known right-half-plane finite-height continuity.
example : Continuous (fun t : ℝ ↦ cubicAFEWeightNormMass t (-1 / 4)) :=
  continuous_cubicAFEWeightNormMass (by norm_num) (by norm_num)

-- One constant controls the whole compact time interval and every height.
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (-2 : ℝ) 3, ∀ y : ℝ,
    ‖cubicAFEScalar t (cubicAFEVerticalPoint (-1 / 4) y)‖ ≤
      C * cubicAFEVerticalGaussianMajorant (-1 / 4) y :=
  exists_norm_cubicAFEScalar_vertical_le_on_compact (by norm_num) (by norm_num) isCompact_Icc

-- Negative nonzero dilation is permitted, but zero dilation is not assumed.
example (W : CubicTestWeight) : Integrable (cubicAFEPhysicalHeightMass W (-2) (-1 / 4) 2 3) :=
  integrable_cubicAFEPhysicalHeightMass W (by norm_num) (by norm_num) (by norm_num) 2 3
