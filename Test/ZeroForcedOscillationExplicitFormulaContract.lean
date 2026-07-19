import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula

open Complex Set
open scoped BigOperators

open PrimeNumberTheorem
open PrimeNumberTheorem.ZeroForcedOscillation

example (y T β : ℝ) :
    zeroPackageExplicitFormulaRemainder y T β =
      zeroPackageUncontrolledRemainder y T β + zeroPackageClosedTerms y :=
  zeroPackageExplicitFormulaRemainder_eq_uncontrolled_add_closed y T β

example (y : ℝ) :
    zeroPackageClosedTerms y =
      (Real.log (2 * Real.pi) : ℂ) +
        (1 / 2 : ℂ) *
          (Real.log (1 - Real.exp (-2 * y)) : ℂ) :=
  zeroPackageClosedTerms_eq_log_two_pi_add_log_term y

example {y : ℝ} (hy : 0 < y) :
    ‖zeroPackageClosedTerms y‖ ≤
      Real.log (2 * Real.pi) +
        (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) :=
  norm_zeroPackageClosedTerms_le_log_two_pi_add_exp_neg_div hy

example {y T β : ℝ} (hy : 0 < y) :
    ‖zeroPackageExplicitFormulaRemainder y T β‖ ≤
      ‖zeroPackageUncontrolledRemainder y T β‖ +
        Real.log (2 * Real.pi) +
          (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) :=
  norm_zeroPackageExplicitFormulaRemainder_le_uncontrolled_add_closed hy

example {y T β : ℝ} (hy : 0 < y) :
    ‖equalRealPartZeroPackageContribution (Real.exp y) T β‖ -
        ‖zeroPackageUncontrolledRemainder y T β‖ -
          (Real.log (2 * Real.pi) +
            (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y))) ≤
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  norm_zeroPackage_sub_norm_uncontrolled_sub_closed_le_norm_chebyshevPsi0_sub_exp hy

example (x T β : ℝ) :
    finiteNontrivialZeroSumWithMultiplicity x T =
      equalRealPartZeroPackageContribution x T β +
        complementaryZeroPackageContribution x T β :=
  finiteNontrivialZeroSumWithMultiplicity_eq_zeroPackage_add_complement x T β

example (T β y : ℝ) :
    equalRealPartZeroPackageContribution (Real.exp y) T β =
      ((Real.exp (β * y) : ℝ) : ℂ) *
        multiplicityWeightedExponentialPolynomial
          (equalRealPartZeroPackage T β)
          (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y :=
  equalRealPartZeroPackageContribution_exp_eq_exponentialPolynomial T β y

example (T β y : ℝ) :
    (((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)) =
      -equalRealPartZeroPackageContribution (Real.exp y) T β -
        zeroPackageExplicitFormulaRemainder y T β :=
  chebyshevPsi0_sub_exp_eq_neg_zeroPackage_sub_remainder T β y

example (T β y : ℝ) :
    ‖equalRealPartZeroPackageContribution (Real.exp y) T β‖ -
        ‖zeroPackageExplicitFormulaRemainder y T β‖ ≤
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ :=
  norm_zeroPackage_sub_norm_remainder_le_norm_chebyshevPsi0_sub_exp T β y

example (T β : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Set.Ioo a b,
      Real.exp (β * y) ^ 2 *
          ((∑ ρ ∈ equalRealPartZeroPackage T β,
              ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
            offDiagonalBound (equalRealPartZeroPackage T β)
                (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
                Complex.im / (b - a)) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T β‖ ^ 2 :=
  exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge T β hab
