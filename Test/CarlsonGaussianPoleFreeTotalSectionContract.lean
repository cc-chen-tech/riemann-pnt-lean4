import PrimeNumberTheorem.CarlsonGaussianPoleFreeTotalSection

open Complex Set MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) (z : ℂ) :
    MemLp (carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 z) 2 volume :=
  memLp_carlsonGaussianPoleFreeSectionTotal hDelta hY0 hY01 z

example {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {z : ℂ} (hzre : z.re ∈ Icc (7 / 12 : ℝ) (47 / 12)) (t : ℝ) :
    HasDerivAt
      (fun u : ℂ => carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 u t)
      (carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z t) z :=
  hasDerivAt_carlsonGaussianPoleFreeSectionTotal_on_wide_inner_strip
    hDelta hY0 hY01 hzre t

#print axioms memLp_carlsonGaussianPoleFreeSectionTotal
#print axioms
  hasDerivAt_carlsonGaussianPoleFreeSectionTotal_on_wide_inner_strip

end CarlsonZeroDensity
end PrimeNumberTheorem
