import PrimeNumberTheorem.CarlsonGaussianPoleFreeLpValue

open Complex Set MeasureTheory
open scoped ENNReal MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    {f : alpha → ℂ} (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂mu :=
  norm_sq_toLp_eq_integral_norm_sq hf

example {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    (carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
      hDelta hY0 hY01 z hzre : ℝ → ℂ) =ᵐ[volume]
      carlsonGaussianHilbertSection Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z :=
  coeFn_carlsonGaussianPoleFreeLpValue_ae_eq
    hDelta hY0 hY01 hzre

example {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 z hzre‖ ^ 2 =
      ∫ t : ℝ,
        ‖carlsonGaussianHilbertSection Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z t‖ ^ 2 :=
  norm_sq_carlsonGaussianPoleFreeLpValue
    hDelta hY0 hY01 hzre

example {Delta w : ℝ} (hDelta : 0 < Delta) :
    (∫ t : ℝ, carlsonGaussianWeight Delta w t) =
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) :=
  integral_carlsonGaussianWeight hDelta

example {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 (4 : ℂ)
          (by norm_num : (4 : ℂ).re ∈ Icc (1 / 2 : ℝ) 4)‖ ^ 2 ≤
      Real.exp (16 / Delta ^ 2) *
        ((10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3)) ^ 2 *
          Real.sqrt (Real.pi / (1 / Delta ^ 2)) :=
  norm_sq_carlsonGaussianPoleFreeLpValue_four_le hDelta hY0 hY01

#print axioms norm_sq_toLp_eq_integral_norm_sq
#print axioms coeFn_carlsonGaussianPoleFreeLpValue_ae_eq
#print axioms norm_sq_carlsonGaussianPoleFreeLpValue
#print axioms integral_carlsonGaussianWeight
#print axioms norm_sq_carlsonGaussianPoleFreeLpValue_four_le

end CarlsonZeroDensity
end PrimeNumberTheorem
