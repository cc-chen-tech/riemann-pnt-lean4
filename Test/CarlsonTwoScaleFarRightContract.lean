import PrimeNumberTheorem.CarlsonTwoScaleFarRight

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤ (5 / 36 : ℝ) :=
  norm_twoScaleMollifiedZetaError_le_five_div_thirty_six_of_four_le_re
    hY0 hY01 hs

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤ (1 / 3 : ℝ) :=
  norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re
    hY0 hY01 hs

end CarlsonZeroDensity
end PrimeNumberTheorem
