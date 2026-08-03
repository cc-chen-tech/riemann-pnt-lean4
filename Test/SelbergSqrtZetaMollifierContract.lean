import HardyTheorem.SelbergSqrtZetaMollifier

open scoped ArithmeticFunction

namespace HardyTheorem

noncomputable example (X n : ℕ) : ℝ :=
  selbergSqrtZetaTaperedCoeff X n

noncomputable example (X : ℕ) : ArithmeticFunction ℝ :=
  selbergShortTaperedSqrtZeta X

example (X n : ℕ) :
    selbergShortTaperedSqrtZeta X n =
      if n ∈ Finset.Icc 1 X then selbergSqrtZetaTaperedCoeff X n else 0 :=
  selbergShortTaperedSqrtZeta_apply X n

example (X : ℕ) :
    selbergSqrtZetaTaperedCoeff X 1 = 1 :=
  selbergSqrtZetaTaperedCoeff_one X

example {X : ℕ} (hX : 1 ≤ X) :
    selbergShortTaperedSqrtZeta X 1 = 1 :=
  selbergShortTaperedSqrtZeta_one hX

example {X p : ℕ} (hp : p.Prime) :
    selbergSqrtZetaTaperedCoeff X p =
      -(1 / 2 : ℝ) * (1 - Real.log p / Real.log X) :=
  selbergSqrtZetaTaperedCoeff_prime hp

example {X p i : ℕ} (hp : p.Prime) (hpiX : p ^ i ≤ X) :
    selbergShortTaperedSqrtZeta X (p ^ i) =
      selbergSqrtZetaLocalTaperedCoeff (Real.log p / Real.log X) i :=
  selbergShortTaperedSqrtZeta_apply_prime_pow hp hpiX

example {X p : ℕ} (hX : 1 ≤ X) (hp : p.Prime) (hpX : p ≤ X) :
    (selbergShortTaperedSqrtZeta X * selbergShortTaperedSqrtZeta X) p =
      -1 + Real.log p / Real.log X :=
  selbergShortTaperedSqrtZeta_sq_apply_prime hX hp hpX

example {X p k : ℕ} (hp : p.Prime) (hpkX : p ^ k ≤ X) :
    (selbergShortTaperedSqrtZeta X * selbergShortTaperedSqrtZeta X) (p ^ k) =
      if k = 0 then 1
      else if k = 1 then -1 + Real.log p / Real.log X
      else (Real.log p / Real.log X) ^ 2 / 4 :=
  selbergShortTaperedSqrtZeta_sq_apply_prime_pow hp hpkX

example {X p : ℕ} (hX : 1 ≤ X) (hp : p.Prime) (hpX : p ≤ X) :
    (((selbergShortTaperedSqrtZeta X * selbergShortTaperedSqrtZeta X) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) p) =
        Real.log p / Real.log X :=
  selbergShortTaperedSqrtZeta_sq_mul_zeta_apply_prime hX hp hpX

example {X p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hpkX : p ^ k ≤ X) :
    (((selbergShortTaperedSqrtZeta X * selbergShortTaperedSqrtZeta X) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p ^ k)) =
        Real.log p / Real.log X +
          ((k - 1 : ℕ) : ℝ) * (Real.log p / Real.log X) ^ 2 / 4 :=
  selbergShortTaperedSqrtZeta_sq_mul_zeta_apply_prime_pow hp hk hpkX

end HardyTheorem
