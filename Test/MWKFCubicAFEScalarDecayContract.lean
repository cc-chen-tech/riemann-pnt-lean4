import PrimeNumberTheorem.MWKFCubicAFEScalarDecay

open PrimeNumberTheorem.MWKFCubic

#check norm_cubicAFEKernelG_le
#check norm_cubicAFEKernelG_vertical_le
#check integrable_cubicAFEVerticalGaussianMajorant
#check continuous_cubicAFEScalar_vertical_of_halfPlane
#check exists_norm_cubicAFEScalar_vertical_le
#check integrable_cubicAFEScalar_vertical

-- The negative line required for the small-product contour shift is included.
example (t : ℝ) : MeasureTheory.Integrable (fun y : ℝ ↦
    cubicAFEScalar t (cubicAFEVerticalPoint (-1 / 4) y)) :=
  integrable_cubicAFEScalar_vertical t (by norm_num) (by norm_num)

example (t : ℝ) : MeasureTheory.Integrable (fun y : ℝ ↦
    cubicAFEScalar t (cubicAFEVerticalPoint (3 / 4) y)) :=
  integrable_cubicAFEScalar_vertical t (by norm_num) (by norm_num)
