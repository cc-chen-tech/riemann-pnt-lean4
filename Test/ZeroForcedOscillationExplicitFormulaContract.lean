import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula

open Complex Set
open scoped BigOperators

open PrimeNumberTheorem
open PrimeNumberTheorem.ZeroForcedOscillation

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
