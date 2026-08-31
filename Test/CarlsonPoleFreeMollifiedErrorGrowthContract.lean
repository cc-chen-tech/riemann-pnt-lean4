import PrimeNumberTheorem.CarlsonPoleFreeMollifiedErrorGrowth

open Complex Set MeasureTheory
open scoped ENNReal MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (Y0 Y1 : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {x t : ℝ},
      x ∈ Icc (1 / 2 : ℝ) 4 → t ∈ Icc (-1 : ℝ) 1 →
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          ((x : ℂ) + I * (t : ℂ))‖ ≤ M :=
  exists_norm_poleFreeTwoScaleMollifiedZetaError_le_on_compact_strip Y0 Y1

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ},
      s.re ∈ Icc (1 / 2 : ℝ) 4 →
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2 ≤
        C * (|s.im| + 3) ^ 10 :=
  exists_norm_sq_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_half_four
    hY0 hY01

example {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    MemLp
      (carlsonGaussianHilbertSection Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z) 2 volume :=
  memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
    hDelta hY0 hY01 hzre

#print axioms
  exists_norm_poleFreeTwoScaleMollifiedZetaError_le_on_compact_strip
#print axioms
  exists_norm_sq_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_half_four
#print axioms
  memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four

end CarlsonZeroDensity
end PrimeNumberTheorem
