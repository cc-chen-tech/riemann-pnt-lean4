import HardyTheorem.SelbergSqrtZetaArithmetic

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

noncomputable section

example : ArithmeticFunction ℝ :=
  selbergSqrtZetaCoeff

example : selbergSqrtZetaCoeff 0 = 0 :=
  selbergSqrtZetaCoeff_zero

example : selbergSqrtZetaCoeff 1 = 1 :=
  selbergSqrtZetaCoeff_one

example {n : ℕ} (hn : n ≠ 0) :
    selbergSqrtZetaCoeff n =
      n.factorization.prod fun _ k => selbergSqrtZetaLocalCoeff k :=
  selbergSqrtZetaCoeff_apply_ne_zero hn

example {p k : ℕ} (hp : p.Prime) :
    selbergSqrtZetaCoeff (p ^ k) = selbergSqrtZetaLocalCoeff k :=
  selbergSqrtZetaCoeff_apply_prime_pow hp

example : ArithmeticFunction.IsMultiplicative selbergSqrtZetaCoeff :=
  selbergSqrtZetaCoeff_isMultiplicative

example {p k : ℕ} (hp : p.Prime) :
    (selbergSqrtZetaCoeff * selbergSqrtZetaCoeff) (p ^ k) =
      if k = 0 then 1 else if k = 1 then -1 else 0 :=
  selbergSqrtZetaCoeff_sq_apply_prime_pow hp

example :
    selbergSqrtZetaCoeff * selbergSqrtZetaCoeff =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) :=
  selbergSqrtZetaCoeff_mul_self

end

end HardyTheorem
