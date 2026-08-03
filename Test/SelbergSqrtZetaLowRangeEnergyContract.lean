import HardyTheorem.SelbergSqrtZetaLowRangeEnergy

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

noncomputable example : ArithmeticFunction ℝ :=
  weightedVonMangoldt

example (n : ℕ) :
    weightedVonMangoldt n =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
  weightedVonMangoldt_apply n

example (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt *
      ArithmeticFunction.vonMangoldt) n :=
  vonMangoldt_selfConvolution_nonneg n

example {n : ℕ} (hn : 1 ≤ n) :
    (ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt) n ≤
      Real.log n ^ 2 :=
  vonMangoldt_selfConvolution_le_log_sq hn

example {n : ℕ} :
    (weightedVonMangoldt * weightedVonMangoldt) n =
      (ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt) n / (n : ℝ) :=
  weightedVonMangoldt_mul_self_apply

example (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) n / (n : ℝ)) ≤
      (∑ n ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt n / (n : ℝ)) ^ 2 :=
  sum_weightedVonMangoldt_selfConvolution_le_sq X

noncomputable example (X n : ℕ) : ℝ :=
  selbergSqrtZetaLowRangeCoeff X n

example {X n : ℕ} (hX : 1 < X) (hn : 1 < n) (hnX : n ≤ X) :
    (((selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) =
      selbergSqrtZetaLowRangeCoeff X n :=
  selbergShortTaperedSqrtZeta_collected_eq_lowRangeCoeff hX hn hnX

example {X n : ℕ} (hX : 1 < X) :
    0 ≤ selbergSqrtZetaLowRangeCoeff X n :=
  selbergSqrtZetaLowRangeCoeff_nonneg hX

example {X n : ℕ} (hX : 1 < X) (hn : 1 ≤ n) (hnX : n ≤ X) :
    selbergSqrtZetaLowRangeCoeff X n ≤ 5 / 4 :=
  selbergSqrtZetaLowRangeCoeff_le_five_fourths hX hn hnX

example {X : ℕ} (hX : 1 < X) :
    (∑ n ∈ Finset.Icc 1 X,
        selbergSqrtZetaLowRangeCoeff X n / (n : ℝ)) ≤
      (Real.log X + (Real.log 4 + 5)) / Real.log X +
        ((Real.log X + (Real.log 4 + 5)) / Real.log X) ^ 2 / 4 :=
  sum_selbergSqrtZetaLowRangeCoeff_div_le hX

example {X : ℕ} (hX : 1 < X) :
    (∑ n ∈ Finset.Ioc 1 X,
        selbergSqrtZetaLowRangeCoeff X n ^ 2 / (n : ℝ)) ≤
      (5 / 4 : ℝ) *
        ∑ n ∈ Finset.Ioc 1 X,
          selbergSqrtZetaLowRangeCoeff X n / (n : ℝ) :=
  sum_sq_selbergSqrtZetaLowRangeCoeff_div_le_firstMoment hX

example {X : ℕ} (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    (∑ n ∈ Finset.Ioc 1 X,
        selbergSqrtZetaLowRangeCoeff X n ^ 2 / (n : ℝ)) ≤
      (15 : ℝ) / 4 :=
  sum_sq_selbergSqrtZetaLowRangeCoeff_div_le_fifteen_fourths hX hlarge

end HardyTheorem
