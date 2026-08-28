import PrimeNumberTheorem.CarlsonPoleFreeMollifiedErrorDerivGrowth

open Complex Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {a b r : ℝ} (hr : 0 < r)
    (ha : 1 / 2 + r ≤ a) (hb : b + r ≤ 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ},
      s.re ∈ Icc a b →
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ^ 2 ≤
        C * (|s.im| + 3 + r) ^ 20 :=
  exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_compact_inner_strip
    hY0 hY01 hr ha hb

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ},
      s.re ∈ Icc (2 / 3 : ℝ) (47 / 12) →
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ^ 2 ≤
        C * (|s.im| + 4) ^ 20 :=
  exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_inner_strip
    hY0 hY01

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ},
      s.re ∈ Icc (7 / 12 : ℝ) (47 / 12) →
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ^ 2 ≤
        C * (|s.im| + 4) ^ 20 :=
  exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_wide_inner_strip
    hY0 hY01

#print axioms exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_inner_strip
#print axioms exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_wide_inner_strip
#print axioms exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_compact_inner_strip

end CarlsonZeroDensity
end PrimeNumberTheorem
