import HardyTheorem.CriticalLineShortDirichlet

#check HardyTheorem.criticalLineShortDirichletCoeff
#check HardyTheorem.criticalLineShortDirichletPolynomial
#check HardyTheorem.integral_criticalLineDirichletPolynomial_eq_shortPolynomial
#check HardyTheorem.integral_normSq_criticalLineShortDirichletPolynomial_le

example (δ t : ℝ) (N : ℕ) :
    (∫ u in t..t + δ,
        ∑ n ∈ Finset.Icc 2 N,
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + Complex.I * u)) =
      HardyTheorem.criticalLineShortDirichletPolynomial δ N t :=
  HardyTheorem.integral_criticalLineDirichletPolynomial_eq_shortPolynomial δ t N

#print axioms HardyTheorem.integral_criticalLineDirichletPolynomial_eq_shortPolynomial
#print axioms HardyTheorem.integral_normSq_criticalLineShortDirichletPolynomial_le
