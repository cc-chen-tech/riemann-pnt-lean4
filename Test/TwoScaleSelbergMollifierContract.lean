import HardyTheorem.TwoScaleSelbergMollifier

open scoped BigOperators

namespace HardyTheorem

example {Y0 Y1 n : ℕ} (hn : n ≤ Y0) :
    twoScaleSelbergWeight Y0 Y1 n = 1 :=
  twoScaleSelbergWeight_eq_one hn

example {Y0 Y1 n : ℕ} (hn : n ≤ Y0) :
    twoScaleSelbergCoeff Y0 Y1 n =
      (ArithmeticFunction.moebius n : ℝ) :=
  twoScaleSelbergCoeff_eq_moebius hn

example {Y0 Y1 k : ℕ} (hk : 1 < k) (hkY0 : k ≤ Y0) :
    twoScaleMollifiedZetaCoeff Y0 Y1 k = 0 :=
  twoScaleMollifiedZetaCoeff_eq_zero hk hkY0

example {Y0 Y1 n : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hn1 : 1 ≤ n) (hnY1 : n ≤ Y1) :
    twoScaleSelbergWeight Y0 Y1 n ∈ Set.Icc (0 : ℝ) 1 :=
  twoScaleSelbergWeight_mem_Icc hY0 hY01 hn1 hnY1

example {Y0 Y1 n : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hn1 : 1 ≤ n) (hnY1 : n ≤ Y1) :
    |twoScaleSelbergCoeff Y0 Y1 n| ≤ 1 :=
  abs_twoScaleSelbergCoeff_le_one hY0 hY01 hn1 hnY1

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) :
    twoScaleSelbergCoeff Y0 Y1 1 = 1 :=
  twoScaleSelbergCoeff_one hY0

end HardyTheorem
