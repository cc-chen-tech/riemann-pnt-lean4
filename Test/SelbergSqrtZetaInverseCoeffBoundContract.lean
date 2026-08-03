import HardyTheorem.SelbergSqrtZetaInverseCoeffBound

open Complex Polynomial
open scoped BigOperators

namespace HardyTheorem

example (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), selbergSqrtZetaLocalCoeff j) =
      (-1 : ℝ) ^ k * Ring.choose (-1 / 2 : ℝ) k :=
  sum_range_selbergSqrtZetaLocalCoeff_eq k

example (k : ℕ) :
    |∑ j ∈ Finset.range (k + 1), selbergSqrtZetaLocalCoeff j| ≤ 1 :=
  abs_sum_range_selbergSqrtZetaLocalCoeff_le_one k

example {p k : ℕ} (hp : p.Prime) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        selbergSqrtZetaCoeff) (p ^ k)) =
      ∑ j ∈ Finset.range (k + 1), selbergSqrtZetaLocalCoeff j :=
  zeta_mul_selbergSqrtZetaCoeff_apply_prime_pow hp

example (n : ℕ) :
    |(((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        selbergSqrtZetaCoeff) n)| ≤ 1 :=
  abs_zeta_mul_selbergSqrtZetaCoeff_le_one n

end HardyTheorem
