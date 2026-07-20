import HardyTheorem.SelbergMollifiedCoefficientArithmetic

open scoped BigOperators

namespace HardyTheorem

example {N X k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergMollifiedDirichletPairs N X k = k.divisorsAntidiagonal :=
  selbergMollifiedDirichletPairs_eq_divisorsAntidiagonal hk1 hkN hkX

example {N X k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergMollifiedDirichletCoeff N X k =
      ∑ d ∈ k.divisors, selbergMoebiusCoeff X d :=
  selbergMollifiedDirichletCoeff_eq_sum_divisors hk1 hkN hkX

example {k : ℕ} (hk : 1 < k) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 :=
  sum_moebius_divisors_eq_zero hk

example {X k : ℕ} (hk : 1 < k) :
    (∑ d ∈ k.divisors, selbergMoebiusCoeff X d) =
      ArithmeticFunction.vonMangoldt k / Real.log X :=
  sum_selbergMoebiusCoeff_divisors_eq_vonMangoldt_div_log hk

example {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    selbergMollifiedDirichletCoeff N X 1 = 1 :=
  selbergMollifiedDirichletCoeff_one hN hX

example {N X k : ℕ} (hk : 1 < k)
    (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergMollifiedDirichletCoeff N X k =
      ArithmeticFunction.vonMangoldt k / Real.log X :=
  selbergMollifiedDirichletCoeff_eq_vonMangoldt_div_log hk hkN hkX

#print axioms selbergMollifiedDirichletPairs_eq_divisorsAntidiagonal
#print axioms selbergMollifiedDirichletCoeff_eq_sum_divisors
#print axioms sum_moebius_divisors_eq_zero
#print axioms sum_selbergMoebiusCoeff_divisors_eq_vonMangoldt_div_log
#print axioms selbergMollifiedDirichletCoeff_one
#print axioms selbergMollifiedDirichletCoeff_eq_vonMangoldt_div_log

end HardyTheorem
