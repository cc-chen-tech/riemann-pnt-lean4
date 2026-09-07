import PrimeNumberTheorem.CarlsonTwoScaleFarRight

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, 1 / (N + n + 1 : ℝ) ^ 4) ≤
      1 / (N : ℝ) ^ 3 :=
  tsum_inv_nat_add_one_pow_four_le_inv_cube hN

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s -
        mobiusMollifier Y0 s‖ ≤ 1 / (Y0 : ℝ) ^ 3 :=
  norm_twoScaleSelbergMollifier_sub_mobiusMollifier_le_inv_cube
    hY0 hY01 hs

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤
      (10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3) :=
  norm_twoScaleMollifiedZetaError_le_ten_div_three_mul_inv_cube
    hY0 hY01 hs

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1 s‖ ≤
      (10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3) :=
  norm_poleFreeTwoScaleMollifiedZetaError_le_ten_div_three_mul_inv_cube
    hY0 hY01 hs

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

#print axioms tsum_inv_nat_add_one_pow_four_le_inv_cube
#print axioms norm_twoScaleSelbergMollifier_sub_mobiusMollifier_le_inv_cube
#print axioms norm_twoScaleMollifiedZetaError_le_ten_div_three_mul_inv_cube
#print axioms norm_poleFreeTwoScaleMollifiedZetaError_le_ten_div_three_mul_inv_cube

end CarlsonZeroDensity
end PrimeNumberTheorem
