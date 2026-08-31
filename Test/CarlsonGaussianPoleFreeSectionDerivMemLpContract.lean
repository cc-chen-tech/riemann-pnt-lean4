import PrimeNumberTheorem.CarlsonGaussianPoleFreeSectionDerivMemLp

open Complex Set MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (7 / 12 : ℝ) (47 / 12)) :
    MemLp
      (carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z) 2 volume :=
  memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_wide_inner_strip
    hDelta hY0 hY01 hzre

example {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (2 / 3 : ℝ) (47 / 12)) :
    MemLp
      (carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z) 2 volume :=
  memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_inner_strip
    hDelta hY0 hY01 hzre

#print axioms memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_inner_strip
#print axioms memLp_carlsonGaussianHilbertSectionDeriv_poleFree_on_wide_inner_strip

end CarlsonZeroDensity
end PrimeNumberTheorem
