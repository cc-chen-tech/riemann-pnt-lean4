import PrimeNumberTheorem.MWKFCubicAFECompletedShift

open PrimeNumberTheorem.MWKFCubic
open Complex Filter MeasureTheory
open scoped Topology

#check summable_integral_cubicAFECompletedShiftMajorant
#check norm_integral_cubicAFECompletedKernel_le_shiftMajorant
#check summable_integral_norm_cubicAFECompletedKernelVertical
#check tendsto_cubicAFECompletedShiftIntegral_height
#check tendsto_cubicAFECompletedZeroMode_allShift_height

-- Fixed-depth summability covers all shifts, including zero. Negative
-- nonzero time dilation is allowed; no positivity of T is smuggled in.
example (W : CubicTestWeight) : Summable (fun δ : ℤ ↦ ∫ p : ℝ × ℝ,
    ‖cubicAFECompletedPhysicalKernelVertical W (-2) 1 2 3 δ 2 p.1 p.2‖) := by
  exact summable_integral_norm_cubicAFECompletedKernelVertical W (by norm_num)
    (by norm_num) (by decide) 2

-- Every nonzero integer shift is present, including negative shifts;
-- J=2 is fixed, while the Mellin height is free to tend to infinity.
example (W : CubicTestWeight) :
    Tendsto (fun V : ℝ ↦ ∑' δ : {δ : ℤ // δ ≠ 0}, ∫ t : ℝ, ∫ x : ℝ,
      cubicAFECompletedBoundaryPhysicalKernel W 2 1 V 2 3 δ.val 2 t x) atTop
      (nhds (∑' δ : {δ : ℤ // δ ≠ 0}, ∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedPhysicalKernelVertical W 2 1 2 3 δ.val 2 t x)) := by
  exact tendsto_cubicAFECompletedShiftIntegral_height W (by norm_num) (by norm_num)
    (by decide) 2

-- The full dyadic zero-mode sum retains the nontrivial Poisson factor 1/3.
example (W : CubicTestWeight) :
    Tendsto (fun V : ℝ ↦ ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' jk : ℕ × ℕ,
      cubicAFECompletedZeroModeBox (d := 2) W 2 1 V (by decide : 0 < 3) δ.val 2 jk) atTop
      (nhds ((3 : ℂ)⁻¹ * ∑' δ : {δ : ℤ // δ ≠ 0}, ∫ t : ℝ, ∫ x : ℝ,
        cubicAFECompletedPhysicalKernelVertical W 2 1 2 3 δ.val 2 t x)) := by
  simpa only [show Nat.gcd 2 3 = 1 from rfl, Nat.div_one, Nat.cast_ofNat] using
    tendsto_cubicAFECompletedZeroMode_allShift_height W (T := 2) (by norm_num)
      (X := 1) (by norm_num) (d := 2) (e := 3) (by decide) (by decide) 2
