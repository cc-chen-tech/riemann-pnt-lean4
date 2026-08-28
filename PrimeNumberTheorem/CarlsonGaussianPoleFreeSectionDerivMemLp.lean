import PrimeNumberTheorem.CarlsonGaussianHilbertSectionDeriv
import PrimeNumberTheorem.CarlsonGaussianPoleFreeDerivMemLp
import PrimeNumberTheorem.CarlsonGaussianPoleFreeLinearMemLp

/-!
# `L²` membership of the exact Carlson Gaussian section derivative

The exact pointwise derivative is the sum of the previously controlled
linear-times-error term and error-derivative term.  This file records the
pointwise identity and combines their `MemLp` certificates.
-/

open Complex Set MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The displayed pointwise derivative is exactly the sum of its linear and
scalar-derivative Gaussian sections. -/
theorem carlsonGaussianHilbertSectionDeriv_eq_add
    (Delta w : ℝ) (H : ℂ → ℂ) (z : ℂ) :
    carlsonGaussianHilbertSectionDeriv Delta w H z =
      carlsonGaussianHilbertSection Delta w
          (carlsonGaussianLinearErrorFactor Delta w H) z +
        carlsonGaussianHilbertSection Delta w (deriv H) z := by
  funext t
  simp only [carlsonGaussianHilbertSectionDeriv,
    carlsonGaussianHilbertSection, carlsonGaussianLinearErrorFactor,
    Pi.add_apply]
  ring

/-- On the fixed inner strip, the exact pointwise derivative of the concrete
pole-free Gaussian section belongs to `L²(ℝ)`. -/
theorem memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_wide_inner_strip
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (7 / 12 : ℝ) (47 / 12)) :
    MemLp
      (carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z) 2 volume := by
  rw [carlsonGaussianHilbertSectionDeriv_eq_add]
  exact
    (memLp_carlsonGaussian_linear_poleFreeTwoScaleMollifiedZetaError_on_wide_inner_strip
      hDelta hY0 hY01 hzre).add
      (memLp_carlsonGaussian_deriv_poleFreeTwoScaleMollifiedZetaError_on_wide_inner_strip
        hDelta hY0 hY01 hzre)

/-- The original narrower interface, retained for existing callers. -/
theorem memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_inner_strip
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (2 / 3 : ℝ) (47 / 12)) :
    MemLp
      (carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z) 2 volume := by
  apply memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_wide_inner_strip
    hDelta hY0 hY01
  constructor <;> linarith [hzre.1, hzre.2]

end CarlsonZeroDensity
end PrimeNumberTheorem
