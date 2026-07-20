import HardyTheorem.SelbergShortDirichletExpansion

open Complex

namespace Test.SelbergShortDirichletExpansionContract

#check HardyTheorem.selbergShortDirichletTripleSupport
#check HardyTheorem.selbergShortDirichletTripleCoeff
#check HardyTheorem.selbergShortDirichletTripleFrequency
#check HardyTheorem.selbergShortDirichletTriplePolynomial
#check HardyTheorem.criticalLineDirichletPolynomial_mul_mollifier_sq_eq_tripleSum
#check HardyTheorem.selbergShortDirichletTripleFrequency_eq_neg_log_product
#check HardyTheorem.criticalLineDirichletPolynomial_mul_mollifier_sq_eq_exponentialPolynomial
#check HardyTheorem.selbergShortDirichletIntegrand_eq_exponentialPolynomial_sub_one
#check HardyTheorem.selbergMollifiedShortDirichletPolynomial_eq_integral_expansion

example (m n l : ℕ) :
    HardyTheorem.selbergShortDirichletTripleFrequency (m, n, l) =
      -Real.log ((m * n * l : ℕ) : ℝ) :=
  HardyTheorem.selbergShortDirichletTripleFrequency_eq_neg_log_product m n l

example (N X : ℕ) (t : ℝ) :
    (((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
      HardyTheorem.selbergMoebiusMollifier X
        ((1 / 2 : ℂ) + I * t)) *
      HardyTheorem.selbergMoebiusMollifier X
        ((1 / 2 : ℂ) + I * t) - 1) =
      HardyTheorem.selbergShortDirichletTriplePolynomial N X t - 1 :=
  HardyTheorem.selbergShortDirichletIntegrand_eq_exponentialPolynomial_sub_one N X t

#print axioms HardyTheorem.selbergShortDirichletTripleFrequency_eq_neg_log_product
#print axioms HardyTheorem.criticalLineDirichletPolynomial_mul_mollifier_sq_eq_exponentialPolynomial
#print axioms HardyTheorem.selbergShortDirichletIntegrand_eq_exponentialPolynomial_sub_one
#print axioms HardyTheorem.selbergMollifiedShortDirichletPolynomial_eq_integral_expansion

end Test.SelbergShortDirichletExpansionContract
