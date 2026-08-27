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

#print axioms norm_sq_toLp_eq_integral_norm_sq
#print axioms coeFn_carlsonGaussianPoleFreeLpValue_ae_eq
#print axioms norm_sq_carlsonGaussianPoleFreeLpValue

end CarlsonZeroDensity
end PrimeNumberTheorem
