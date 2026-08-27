import PrimeNumberTheorem.CarlsonPoleFreeMollifiedErrorDerivGrowth

open Complex Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℂ},
      s.re ∈ Icc (2 / 3 : ℝ) (47 / 12) →
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1) s‖ ^ 2 ≤
        C * (|s.im| + 4) ^ 20 :=
  exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_inner_strip
    hY0 hY01

#print axioms exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_inner_strip

end CarlsonZeroDensity
end PrimeNumberTheorem
