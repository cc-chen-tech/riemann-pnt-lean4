import PrimeNumberTheorem.ExplicitFormulaAllHeights
import PrimeNumberTheorem.ZeroForcedOscillation
import PrimeNumberTheorem.ZetaDerivativeZero

/-!
# Isolating an equal-real-part zero package in the explicit formula

This module connects the finite mean-square mechanism to the repository's
actual multiplicity-aware zeta-zero sum. It makes no estimate for the
complementary zeros or the explicit-formula approximation error.
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

/-- The closed-form terms in the finite-height explicit formula. -/
def zeroPackageClosedTerms (y : ℝ) : ℂ :=
  deriv riemannZeta 0 / riemannZeta 0 +
    (1 / 2 : ℂ) *
      (Real.log (1 - Real.exp y ^ (-2 : ℝ)) : ℂ)

/-- The terms in the finite-height explicit formula which are not controlled
by the closed-form estimate: the complementary zero package and the genuine
explicit-formula approximation error. -/
def zeroPackageUncontrolledRemainder (y T β : ℝ) : ℂ :=
  complementaryZeroPackageContribution (Real.exp y) T β +
    (explicitFormulaApproxWithMultiplicity (Real.exp y) T -
      (chebyshevPsi0 (Real.exp y) : ℂ))

/-- All terms other than the selected package in the exact finite-height
identity for `ψ₀(exp y)-exp y`. -/
def zeroPackageExplicitFormulaRemainder (y T β : ℝ) : ℂ :=
  zeroPackageUncontrolledRemainder y T β + zeroPackageClosedTerms y

/-- Separates the uncontrolled analytic terms from the closed-form terms. -/
theorem zeroPackageExplicitFormulaRemainder_eq_uncontrolled_add_closed
    (y T β : ℝ) :
    zeroPackageExplicitFormulaRemainder y T β =
      zeroPackageUncontrolledRemainder y T β + zeroPackageClosedTerms y :=
  rfl

/-- The `ζ'(0)/ζ(0)` term is exactly `log(2π)`, and the remaining closed
term is the elementary trivial-zero logarithm in logarithmic coordinates. -/
theorem zeroPackageClosedTerms_eq_log_two_pi_add_log_term (y : ℝ) :
    zeroPackageClosedTerms y =
      (Real.log (2 * Real.pi) : ℂ) +
        (1 / 2 : ℂ) *
          (Real.log (1 - Real.exp (-2 * y)) : ℂ) := by
  have hpow : Real.exp y ^ (-2 : ℝ) = Real.exp (-2 * y) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos y)]
    congr 1
    rw [Real.log_exp]
    ring
  rw [zeroPackageClosedTerms, deriv_riemannZeta_zero_div_riemannZeta_zero,
    hpow]

private theorem abs_log_one_sub_exp_neg_le_exp_neg_div {y : ℝ} (hy : 0 < y) :
    |Real.log (1 - Real.exp (-2 * y))| ≤
      Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) := by
  let q : ℝ := Real.exp (-2 * y)
  have hqpos : 0 < q := Real.exp_pos _
  have hqle : q ≤ 1 := by
    dsimp [q]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hsubpos : 0 < 1 - q := by
    dsimp [q]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hlognonpos : Real.log (1 - q) ≤ 0 :=
    Real.log_nonpos hsubpos.le (by linarith)
  rw [show Real.exp (-2 * y) = q by rfl, abs_of_nonpos hlognonpos]
  calc
    -Real.log (1 - q) = Real.log (1 - q)⁻¹ := (Real.log_inv _).symm
    _ ≤ (1 - q)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hsubpos)
    _ = q / (1 - q) := by
      field_simp [hsubpos.ne']
      ring

/-- Explicit decay bound for the closed-form terms for positive logarithmic
coordinates. This is independent of the zero cutoff and does not estimate
the complementary zero package or truncation error. -/
theorem norm_zeroPackageClosedTerms_le_log_two_pi_add_exp_neg_div
    {y : ℝ} (hy : 0 < y) :
    ‖zeroPackageClosedTerms y‖ ≤
      Real.log (2 * Real.pi) +
        (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) := by
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have htail := abs_log_one_sub_exp_neg_le_exp_neg_div hy
  rw [zeroPackageClosedTerms_eq_log_two_pi_add_log_term]
  calc
    ‖(Real.log (2 * Real.pi) : ℂ) +
          (1 / 2 : ℂ) * (Real.log (1 - Real.exp (-2 * y)) : ℂ)‖ ≤
        ‖(Real.log (2 * Real.pi) : ℂ)‖ +
          ‖(1 / 2 : ℂ) * (Real.log (1 - Real.exp (-2 * y)) : ℂ)‖ :=
      norm_add_le _ _
    _ = Real.log (2 * Real.pi) +
          (1 / 2 : ℝ) * |Real.log (1 - Real.exp (-2 * y))| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hlog, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    _ ≤ Real.log (2 * Real.pi) +
          (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) := by
      calc
        Real.log (2 * Real.pi) +
            (1 / 2 : ℝ) * |Real.log (1 - Real.exp (-2 * y))| ≤
            Real.log (2 * Real.pi) +
              (1 / 2 : ℝ) *
                (Real.exp (-2 * y) / (1 - Real.exp (-2 * y))) := by
          simpa [add_comm] using
            add_le_add_right
              (mul_le_mul_of_nonneg_left htail (show 0 ≤ (1 / 2 : ℝ) by norm_num))
              (Real.log (2 * Real.pi))
        _ = Real.log (2 * Real.pi) +
            (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) := by
          ring

/-- The complete remainder is controlled by the still-uncontrolled analytic
terms plus the explicit closed-form budget. -/
theorem norm_zeroPackageExplicitFormulaRemainder_le_uncontrolled_add_closed
    {y T β : ℝ} (hy : 0 < y) :
    ‖zeroPackageExplicitFormulaRemainder y T β‖ ≤
      ‖zeroPackageUncontrolledRemainder y T β‖ +
        Real.log (2 * Real.pi) +
          (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) := by
  rw [zeroPackageExplicitFormulaRemainder_eq_uncontrolled_add_closed]
  calc
    ‖zeroPackageUncontrolledRemainder y T β + zeroPackageClosedTerms y‖ ≤
        ‖zeroPackageUncontrolledRemainder y T β‖ + ‖zeroPackageClosedTerms y‖ :=
      norm_add_le _ _
    _ ≤ ‖zeroPackageUncontrolledRemainder y T β‖ +
          (Real.log (2 * Real.pi) +
            (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y))) := by
      simpa [add_comm] using
        add_le_add_right (norm_zeroPackageClosedTerms_le_log_two_pi_add_exp_neg_div hy)
          ‖zeroPackageUncontrolledRemainder y T β‖
    _ = ‖zeroPackageUncontrolledRemainder y T β‖ +
          Real.log (2 * Real.pi) +
            (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) := by
      ring

/-- Exact package-versus-remainder decomposition of the finite-height explicit
formula. The remaining analytic task is to make the displayed remainder
smaller than the package on a suitable logarithmic interval. -/
theorem chebyshevPsi0_sub_exp_eq_neg_zeroPackage_sub_remainder
    (T β y : ℝ) :
    (((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ)) =
      -equalRealPartZeroPackageContribution (Real.exp y) T β -
        zeroPackageExplicitFormulaRemainder y T β := by
  dsimp [zeroPackageExplicitFormulaRemainder,
    zeroPackageUncontrolledRemainder, zeroPackageClosedTerms,
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

/-- Quantitative package-to-`ψ₀` transfer after removing only the proved
closed-form budget. The complementary zero package and the explicit-formula
approximation error remain together in `zeroPackageUncontrolledRemainder`. -/
theorem norm_zeroPackage_sub_norm_uncontrolled_sub_closed_le_norm_chebyshevPsi0_sub_exp
    {y T β : ℝ} (hy : 0 < y) :
    ‖equalRealPartZeroPackageContribution (Real.exp y) T β‖ -
        ‖zeroPackageUncontrolledRemainder y T β‖ -
          (Real.log (2 * Real.pi) +
            (1 / 2 : ℝ) * Real.exp (-2 * y) / (1 - Real.exp (-2 * y))) ≤
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  have hremainder :=
    norm_zeroPackageExplicitFormulaRemainder_le_uncontrolled_add_closed
      (T := T) (β := β) hy
  have htransfer :=
    norm_zeroPackage_sub_norm_remainder_le_norm_chebyshevPsi0_sub_exp T β y
  linarith

end

end PrimeNumberTheorem.ZeroForcedOscillation
