import PrimeNumberTheorem.CarlsonGaussianPoleFreeLpAnalytic

open Complex Set MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {z : ℂ} (hzre : z.re ∈ Icc (29 / 48 : ℝ) (187 / 48)) :
    HasDerivAt
      (carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1 hDelta hY0 hY01)
      ((memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_wide_inner_strip
        hDelta hY0 hY01 (by constructor <;> linarith [hzre.1, hzre.2])).toLp
        (carlsonGaussianHilbertSectionDeriv Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z)) z :=
  hasDerivAt_carlsonGaussianPoleFreeLpValueTotal hDelta hY0 hY01 hzre

#print axioms hasDerivAt_carlsonGaussianPoleFreeLpValueTotal

end CarlsonZeroDensity
end PrimeNumberTheorem
