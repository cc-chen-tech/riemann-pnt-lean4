import PrimeNumberTheorem.CarlsonPoleFreeMollifiedError

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {theta : ℝ} (htheta : 0 ≤ theta) (Y0 Y1 : ℕ) :
    AnalyticOnNhd ℂ (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
      {s : ℂ | theta < s.re} :=
  analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt htheta Y0 Y1

example {Y0 Y1 : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsneg1 : s ≠ -1) :
    poleFreeTwoScaleMollifiedZetaError Y0 Y1 s =
      (s - 1) / (s + 1) * twoScaleMollifiedZetaError Y0 Y1 s :=
  poleFreeTwoScaleMollifiedZetaError_eq_mul hs0 hs1 hsneg1

example {x : ℝ} (hx : 0 < x) (Y0 Y1 : ℕ) :
    Continuous fun t : ℝ =>
      poleFreeTwoScaleMollifiedZetaError Y0 Y1
        ((x : ℂ) + I * (t : ℂ)) :=
  continuous_poleFreeTwoScaleMollifiedZetaError_vertical hx Y0 Y1

#print axioms analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
#print axioms poleFreeTwoScaleMollifiedZetaError_eq_mul
#print axioms continuous_poleFreeTwoScaleMollifiedZetaError_vertical

end CarlsonZeroDensity
end PrimeNumberTheorem
