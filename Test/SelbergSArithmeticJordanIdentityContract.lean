import HardyTheorem.SelbergSArithmeticJordanIdentity

open Complex Nat Finset
open scoped BigOperators

namespace HardyTheorem

#check selbergArithmeticDiagonalGcd
#check selbergArithmeticDiagonalSum
#check selbergArithmeticJordanQuadraticSum
#check selbergArithmeticDiagonalSum_eq_jordanQuadratic

example (X : ℕ) (theta : ℝ) :
    selbergArithmeticDiagonalSum X theta =
      selbergArithmeticJordanQuadraticSum X theta :=
  selbergArithmeticDiagonalSum_eq_jordanQuadratic X theta

end HardyTheorem
