import HardyTheorem.CriticalLineShortDirichlet

#check HardyTheorem.criticalLineShortDirichletCoeff
#check HardyTheorem.criticalLineShortDirichletPolynomial
#check HardyTheorem.norm_criticalLineShortDirichletCoeff_le_two_div
#check HardyTheorem.norm_criticalLineShortDirichletCoeff_le_abs_delta
#check HardyTheorem.integral_criticalLineDirichletPolynomial_eq_shortPolynomial
#check HardyTheorem.integral_normSq_criticalLineShortDirichletPolynomial_le

example (δ t : ℝ) (N : ℕ) :
    (∫ u in t..t + δ,
        ∑ n ∈ Finset.Icc 2 N,
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + Complex.I * u)) =
      HardyTheorem.criticalLineShortDirichletPolynomial δ N t :=
  HardyTheorem.integral_criticalLineDirichletPolynomial_eq_shortPolynomial δ t N

#print axioms HardyTheorem.integral_criticalLineDirichletPolynomial_eq_shortPolynomial
#print axioms HardyTheorem.norm_criticalLineShortDirichletCoeff_le_two_div
#print axioms HardyTheorem.norm_criticalLineShortDirichletCoeff_le_abs_delta
#print axioms HardyTheorem.integral_normSq_criticalLineShortDirichletPolynomial_le
