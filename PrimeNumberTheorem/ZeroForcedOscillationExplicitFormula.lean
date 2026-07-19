import PrimeNumberTheorem.ExplicitFormulaAllHeights
import PrimeNumberTheorem.ZeroForcedOscillation

/-!
# Isolating an equal-real-part zero package in the explicit formula

This module connects the finite mean-square mechanism to the repository's
actual multiplicity-aware zeta-zero sum. It makes no estimate for the
complementary zeros or the explicit-formula approximation remainder.
-/

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem.ZeroForcedOscillation

noncomputable section

/-- The zeros in the symmetric height truncation whose real part is exactly
`β`. Distinct points remain distinct; analytic multiplicity is carried by the
coefficient, not by repeated finset entries. -/
def equalRealPartZeroPackage (T β : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset T).filter fun ρ : ℂ => ρ.re = β

/-- The complementary zeros at the same height truncation. -/
def complementaryZeroPackage (T β : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset T).filter fun ρ : ℂ => ρ.re ≠ β

/-- Multiplicity-aware contribution of the selected equal-real-part package. -/
def equalRealPartZeroPackageContribution (x T β : ℝ) : ℂ :=
  ∑ ρ ∈ equalRealPartZeroPackage T β,
    (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ

/-- Multiplicity-aware contribution of all other zeros in the truncation. -/
def complementaryZeroPackageContribution (x T β : ℝ) : ℂ :=
  ∑ ρ ∈ complementaryZeroPackage T β,
    (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ

/-- The complete finite nontrivial-zero contribution splits exactly into the
selected real-part package and its complement. -/
theorem finiteNontrivialZeroSumWithMultiplicity_eq_zeroPackage_add_complement
    (x T β : ℝ) :
    finiteNontrivialZeroSumWithMultiplicity x T =
      equalRealPartZeroPackageContribution x T β +
        complementaryZeroPackageContribution x T β := by
  classical
  unfold finiteNontrivialZeroSumWithMultiplicity
  dsimp [equalRealPartZeroPackageContribution,
    complementaryZeroPackageContribution, equalRealPartZeroPackage,
    complementaryZeroPackage]
  symm
  exact Finset.sum_filter_add_sum_filter_not
    (nontrivialZerosFinset T) (fun ρ : ℂ => ρ.re = β)
      (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)

/-- Every member of the selected package is an actual nontrivial zeta zero at
the requested height and has the selected real part. -/
theorem mem_equalRealPartZeroPackage {ρ : ℂ} {T β : ℝ} :
    ρ ∈ equalRealPartZeroPackage T β ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T ∧ ρ.re = β := by
  classical
  simp only [equalRealPartZeroPackage, Finset.mem_filter,
    mem_nontrivialZerosFinset, and_assoc]

/-- In logarithmic coordinates the actual selected zeta-zero contribution is
exactly the growth factor `exp(β y)` times the finite exponential polynomial. -/
theorem equalRealPartZeroPackageContribution_exp_eq_exponentialPolynomial
    (T β y : ℝ) :
    equalRealPartZeroPackageContribution (Real.exp y) T β =
      ((Real.exp (β * y) : ℝ) : ℂ) *
        multiplicityWeightedExponentialPolynomial
          (equalRealPartZeroPackage T β)
          (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y := by
  apply equalRealPart_zeroPackage_eq_exponentialPolynomial
  intro ρ hρ
  exact (mem_equalRealPartZeroPackage.mp hρ).2.2

/-- All terms other than the selected package in the exact finite-height
identity for `ψ₀(exp y)-exp y`. No smallness is asserted here. -/
def zeroPackageExplicitFormulaRemainder (y T β : ℝ) : ℂ :=
  complementaryZeroPackageContribution (Real.exp y) T β +
    deriv riemannZeta 0 / riemannZeta 0 +
    (1 / 2 : ℂ) *
      (Real.log (1 - Real.exp y ^ (-2 : ℝ)) : ℂ) +
    (explicitFormulaApproxWithMultiplicity (Real.exp y) T -
      (chebyshevPsi0 (Real.exp y) : ℂ))

/-- Exact package-versus-remainder decomposition of the finite-height explicit
formula. The remaining analytic task is to make the displayed remainder
smaller than the package on a suitable logarithmic interval. -/
theorem chebyshevPsi0_sub_exp_eq_neg_zeroPackage_sub_remainder
    (T β y : ℝ) :
    (((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)) =
      -equalRealPartZeroPackageContribution (Real.exp y) T β -
        zeroPackageExplicitFormulaRemainder y T β := by
  dsimp [zeroPackageExplicitFormulaRemainder,
    explicitFormulaApproxWithMultiplicity]
  rw [finiteNontrivialZeroSumWithMultiplicity_eq_zeroPackage_add_complement
    (Real.exp y) T β]
  push_cast
  ring

/-- The F0 mean-square lower bound specialized to an actual equal-real-part
package of nontrivial zeta zeros with analytic multiplicity. -/
theorem exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge
    (T β : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Set.Ioo a b,
      Real.exp (β * y) ^ 2 *
          ((∑ ρ ∈ equalRealPartZeroPackage T β,
              ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
            offDiagonalBound (equalRealPartZeroPackage T β)
                (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
                Complex.im / (b - a)) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T β‖ ^ 2 := by
  have hre : ∀ ρ ∈ equalRealPartZeroPackage T β, ρ.re = β := by
    intro ρ hρ
    exact (mem_equalRealPartZeroPackage.mp hρ).2.2
  simpa [equalRealPartZeroPackageContribution] using
    (exists_mem_Ioo_sqNorm_equalRealPart_zeroPackage_ge
      (equalRealPartZeroPackage T β) (analyticOrderNatAt riemannZeta) β hab hre)

/-- Reverse-triangle transfer: once the explicit remainder is bounded, the
selected zero package forces a visible prime-counting error. -/
theorem norm_zeroPackage_sub_norm_remainder_le_norm_chebyshevPsi0_sub_exp
    (T β y : ℝ) :
    ‖equalRealPartZeroPackageContribution (Real.exp y) T β‖ -
        ‖zeroPackageExplicitFormulaRemainder y T β‖ ≤
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  let P := equalRealPartZeroPackageContribution (Real.exp y) T β
  let R := zeroPackageExplicitFormulaRemainder y T β
  have hreverse : ‖P‖ - ‖R‖ ≤ ‖P + R‖ := by
    simpa using (norm_sub_norm_le P (-R))
  rw [chebyshevPsi0_sub_exp_eq_neg_zeroPackage_sub_remainder T β y]
  change ‖P‖ - ‖R‖ ≤ ‖-P - R‖
  calc
    ‖P‖ - ‖R‖ ≤ ‖P + R‖ := hreverse
    _ = ‖-P - R‖ := by
      rw [show -P - R = -(P + R) by ring, norm_neg]

end

end PrimeNumberTheorem.ZeroForcedOscillation
