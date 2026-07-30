import HardyTheorem.SelbergSqrtZetaComparableNearDiagonalSchur

open Complex
open scoped BigOperators

namespace Test.SelbergSqrtZetaComparableNearDiagonalSchurContract

open HardyTheorem

#check sum_inv_natDist_Ioc_le_two_mul_harmonic
#check comparableNearDiagonalSquareSum_le_weightedHarmonic
#check selbergSqrtZetaComparableNearDiagonalSquareBudget_le_weightedHarmonic
#check selbergSqrtZetaComparableNearDiagonalSquareBudget_le_globalHarmonic
#check selbergSqrtZetaComparableNearDiagonalSquareBudget_le_globalLog

example {M m : ℕ} (hm : m ∈ Finset.Ioc 1 M) :
    (∑ n ∈ Finset.Ioc 1 M,
        if n ≠ m then ((Nat.dist m n : ℝ))⁻¹ else 0) ≤
      2 * (harmonic M : ℝ) :=
  sum_inv_natDist_Ioc_le_two_mul_harmonic hm

example (M : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Finset.Ioc 1 M,
      ∑ n ∈ Finset.Ioc 1 M,
        if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          (max m n : ℝ) * (a m ^ 2 + a n ^ 2) /
            (Nat.dist m n : ℝ)
        else 0) ≤
      8 * (harmonic M : ℝ) *
        ∑ m ∈ Finset.Ioc 1 M, (m : ℝ) * a m ^ 2 :=
  comparableNearDiagonalSquareSum_le_weightedHarmonic M a

example (N X : ℕ) :
    selbergSqrtZetaComparableNearDiagonalSquareBudget N X ≤
      8 * ((N * X * X : ℕ) : ℝ) *
        (1 + Real.log ((N * X * X : ℕ) : ℝ)) *
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ ^ 2 :=
  selbergSqrtZetaComparableNearDiagonalSquareBudget_le_globalLog N X

end Test.SelbergSqrtZetaComparableNearDiagonalSchurContract
