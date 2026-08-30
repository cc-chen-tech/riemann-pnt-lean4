import PrimeNumberTheorem.MWKFCubicAFECompletedTime

open PrimeNumberTheorem.MWKFCubic
open Complex Filter MeasureTheory
open scoped Topology

#check measurable_cubicAFEProgressionPhysicalSummand_joint
#check integrable_cubicAFECompletedPhysicalMajorant
#check stronglyMeasurable_cubicAFECompletedPhysicalKernelVertical
#check integrable_cubicAFECompletedPhysicalKernelVertical
#check tendsto_cubicAFECompletedPhysicalDoubleIntegral_height
#check tendsto_cubicAFECompletedZeroMode_height

-- Proper absolute integrability of the actual full-height double kernel,
-- not a totalized integral of a nonintegrable function.
example (W : CubicTestWeight) : Integrable (fun p : ℝ × ℝ ↦
    ‖cubicAFECompletedPhysicalKernelVertical W 2 1 2 3 (-5) 2 p.1 p.2‖) :=
  (integrable_cubicAFECompletedPhysicalKernelVertical W (by norm_num) (by norm_num) 2 3 (-5) 2).norm

-- The actual time integral is included, and zero shift is allowed at fixed depth.
example (W : CubicTestWeight) :
    Tendsto (fun V : ℝ ↦ ∫ t : ℝ, ∫ x : ℝ,
      cubicAFECompletedBoundaryPhysicalKernel W 2 1 V 2 3 0 2 t x) atTop
      (nhds (∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedPhysicalKernelVertical W 2 1 2 3 0 2 t x)) :=
  tendsto_cubicAFECompletedPhysicalDoubleIntegral_height W (by norm_num) (by norm_num) 2 3 0 2

-- Preserve the Poisson Jacobian: d=2,e=3 gives s=3, not s=1.
example (W : CubicTestWeight) :
    Tendsto (fun V : ℝ ↦ ∑' jk : ℕ × ℕ,
      cubicAFECompletedZeroModeBox (d := 2) W 2 1 V (e := 3) (by decide) (-5) 2 jk) atTop
      (nhds ((3 : ℂ)⁻¹ * ∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedPhysicalKernelVertical W 2 1 2 3 (-5) 2 t x)) := by
  simpa only [show Nat.gcd 2 3 = 1 by decide, Nat.div_one, Nat.cast_ofNat]
    using tendsto_cubicAFECompletedZeroMode_height W (T := 2) (by norm_num)
      (X := 1) (by norm_num) (d := 2) (e := 3) (by decide) (by decide) (-5) 2
