import HardyTheorem.SelbergSqrtZetaLowRangeSliding

open Complex
open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

noncomputable example (X n : ℕ) : ℂ :=
  selbergSqrtZetaArithmeticDirichletCoeff X n

noncomputable example (X n : ℕ) : ℂ :=
  selbergSqrtZetaLowRangeDirichletCoeff X n

example {X n : ℕ} (hX : 1 < X) (hn : 1 < n) (hnX : n ≤ X) :
    selbergSqrtZetaArithmeticDirichletCoeff X n =
      selbergSqrtZetaLowRangeDirichletCoeff X n :=
  selbergSqrtZetaArithmeticDirichletCoeff_eq_lowRange hX hn hnX

example {X n : ℕ} (hn : 1 ≤ n) :
    Complex.normSq (selbergSqrtZetaLowRangeDirichletCoeff X n) =
      selbergSqrtZetaLowRangeCoeff X n ^ 2 / (n : ℝ) :=
  normSq_selbergSqrtZetaLowRangeDirichletCoeff hn

example {X : ℕ} (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    (∑ n ∈ Finset.Ioc 1 X,
        Complex.normSq
          (selbergSqrtZetaLowRangeDirichletCoeff X n)) ≤
      (15 : ℝ) / 4 :=
  sum_normSq_selbergSqrtZetaLowRangeDirichletCoeff_le_fifteen_fourths
    hX hlarge

example {ι : Type*} (H : ℝ) (coeff : ι → ℂ) (freq : ι → ℝ) (j : ι) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H coeff freq j) ≤
      H ^ 2 * Complex.normSq (coeff j) :=
  normSq_slidingExponentialCoefficient_le_mul_sq H coeff freq j

example {X : ℕ} (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ n ∈ Finset.Ioc 1 X,
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaLowRangeDirichletCoeff X)
            selbergShortDirichletCollectedFrequency n)) ≤
      (15 : ℝ) / 4 * H ^ 2 :=
  sum_normSq_sliding_selbergSqrtZetaLowRangeDirichletCoeff_le
    hX hlarge H

end HardyTheorem
