import PrimeNumberTheorem.GlobalZeroCount
import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula

/-!
# Elementary norm bounds for the complementary zero package

This module proves the purely elementary estimates for the complementary zero
package of `ZeroForcedOscillationExplicitFormula.lean`:

* an exact per-term norm identity
  `‖(m : ℂ) * (x : ℂ) ^ ρ / ρ‖ = (m : ℝ) * x ^ ρ.re / ‖ρ‖` for positive real
  `x`, valid for every `ρ : ℂ` including `ρ = 0` (complex division by zero is
  defined to be zero, and both sides vanish in that case);
* a triangle-inequality bound for
  `‖complementaryZeroPackageContribution (Real.exp y) T β‖` by
  `Real.exp (B * y)` times the multiplicity-weighted reciprocal-norm sum,
  under a uniform real-part cap `ρ.re ≤ B` on the package (with the two
  instances `B = β` and `B = β - δ` used downstream);
* monotonicity of the complementary reciprocal-norm sum up to the full
  height-`T` truncation sum.

What is NOT proved here: no bound on the full truncation sum
`∑ ρ ∈ nontrivialZerosFinset T, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖`
itself (that requires zero-counting input), no real-part cap on actual zeta
zeros, and no relation between `β` and the Riemann Hypothesis.
-/

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem.ZeroForcedOscillation

noncomputable section

/-- Every member of the complementary package is an actual nontrivial zeta
zero at the requested height whose real part differs from `β`. -/
theorem mem_complementaryZeroPackage {ρ : ℂ} {T β : ℝ} :
    ρ ∈ complementaryZeroPackage T β ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T ∧ ρ.re ≠ β := by
  classical
  simp only [complementaryZeroPackage, Finset.mem_filter,
    mem_nontrivialZerosFinset, and_assoc]

/-- Exact norm of one multiplicity-weighted zero-summand `(m : ℂ) * (x : ℂ) ^ ρ / ρ`
at positive real `x`. No hypothesis on `ρ` is needed: when `ρ = 0` both sides
reduce to `0` because complex division by zero is defined to be zero. -/
theorem norm_natCast_mul_cpow_div (x : ℝ) (hx : 0 < x) (ρ : ℂ) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ ρ / ρ‖ = (m : ℝ) * x ^ ρ.re / ‖ρ‖ := by
  rw [norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- Triangle-inequality bound for the complementary package contribution at
`x = Real.exp y`, under a uniform cap `B` on the real parts in the package.
The growth factor `Real.exp (B * y)` is uniform in the zeros; all
zero-dependent data remains in the multiplicity-weighted reciprocal-norm sum,
which is NOT estimated here. -/
theorem norm_complementaryZeroPackageContribution_le_exp_mul_sum_of_re_le
    (T β B y : ℝ) (hy : 0 ≤ y)
    (hdom : ∀ ρ ∈ complementaryZeroPackage T β, ρ.re ≤ B) :
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
      Real.exp (B * y) *
        ∑ ρ ∈ complementaryZeroPackage T β,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
  classical
  calc
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖
        = ‖∑ ρ ∈ complementaryZeroPackage T β,
            (analyticOrderNatAt riemannZeta ρ : ℂ) * (Real.exp y : ℂ) ^ ρ / ρ‖ :=
        rfl
    _ ≤ ∑ ρ ∈ complementaryZeroPackage T β,
          ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (Real.exp y : ℂ) ^ ρ / ρ‖ :=
      norm_sum_le _ _
    _ = ∑ ρ ∈ complementaryZeroPackage T β,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (Real.exp y) ^ ρ.re / ‖ρ‖ := by
      refine Finset.sum_congr rfl fun ρ _ => ?_
      exact norm_natCast_mul_cpow_div (Real.exp y) (Real.exp_pos y) ρ _
    _ ≤ ∑ ρ ∈ complementaryZeroPackage T β,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (B * y) / ‖ρ‖ := by
      refine Finset.sum_le_sum fun ρ hρ => ?_
      have hexp : (Real.exp y) ^ ρ.re ≤ Real.exp (B * y) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp, mul_comm y ρ.re]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hdom ρ hρ) hy)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)) (norm_nonneg ρ)
    _ = Real.exp (B * y) *
          ∑ ρ ∈ complementaryZeroPackage T β,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      ring

/-- Aggregate triangle bound at the natural cap `B = β`: the complementary
package contribution grows at most like `Real.exp (β * y)` times the
complementary reciprocal-norm sum. -/
theorem norm_complementaryZeroPackageContribution_le_exp_mul_sum
    (T β y : ℝ) (hy : 0 ≤ y)
    (hdom : ∀ ρ ∈ complementaryZeroPackage T β, ρ.re ≤ β) :
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
      Real.exp (β * y) *
        ∑ ρ ∈ complementaryZeroPackage T β,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  norm_complementaryZeroPackageContribution_le_exp_mul_sum_of_re_le
    T β β y hy hdom

/-- Gap-refined bound: a uniform gap `ρ.re ≤ β - δ` in the complementary
package improves the growth factor to `Real.exp ((β - δ) * y)`. -/
theorem norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum
    (T β δ y : ℝ) (hy : 0 ≤ y)
    (hgap : ∀ ρ ∈ complementaryZeroPackage T β, ρ.re ≤ β - δ) :
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
      Real.exp ((β - δ) * y) *
        ∑ ρ ∈ complementaryZeroPackage T β,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  norm_complementaryZeroPackageContribution_le_exp_mul_sum_of_re_le
    T β (β - δ) y hy hgap

/-- The complementary multiplicity-weighted reciprocal-norm sum is
nonnegative. -/
theorem sum_complementary_multiplicity_div_norm_nonneg (T β : ℝ) :
    0 ≤ ∑ ρ ∈ complementaryZeroPackage T β,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  Finset.sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

/-- The complementary package is a sub-finset of the full height-`T`
truncation, so its reciprocal-norm sum is bounded by the full truncation
sum. The full sum itself is NOT estimated here. -/
theorem sum_complementary_multiplicity_div_norm_le_sum_nontrivialZerosFinset
    (T β : ℝ) :
    ∑ ρ ∈ complementaryZeroPackage T β,
        (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤
      ∑ ρ ∈ nontrivialZerosFinset T,
        (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ρ _ _ =>
    div_nonneg (Nat.cast_nonneg _) (norm_nonneg ρ)
  intro ρ hρ
  simp only [complementaryZeroPackage, Finset.mem_filter] at hρ
  exact hρ.1

/-- Combined gap-refined bound against the full height-`T` truncation sum:
the complementary contribution is at most `Real.exp ((β - δ) * y)` times the
full multiplicity-weighted reciprocal-norm sum of the truncation. -/
theorem norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum_nontrivialZerosFinset
    (T β δ y : ℝ) (hy : 0 ≤ y)
    (hgap : ∀ ρ ∈ complementaryZeroPackage T β, ρ.re ≤ β - δ) :
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
      Real.exp ((β - δ) * y) *
        ∑ ρ ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  (norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum
    T β δ y hy hgap).trans
      (mul_le_mul_of_nonneg_left
        (sum_complementary_multiplicity_div_norm_le_sum_nontrivialZerosFinset T β)
        (Real.exp_nonneg _))

/-- Quantitative complementary-package bound: with a uniform real-part gap
`δ` below `β` on the complementary zeros at height `T ≥ 4`, the complementary
contribution is at most `Real.exp ((β - δ) * y)` times an explicit
`O(log^2 T)` budget.  This chains the gap-refined triangle bound to the
repository's global reciprocal-norm multiplicity estimate. -/
theorem exists_norm_complementaryZeroPackageContribution_le_exp_gap_mul_log_sq
    (β δ y : ℝ) (hy : 0 ≤ y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      (∀ ρ ∈ complementaryZeroPackage T β, ρ.re ≤ β - δ) →
        ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
          Real.exp ((β - δ) * y) * (C * (1 + Real.log (T + 6)) ^ 2) := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  intro T hT hgap
  calc
    ‖complementaryZeroPackageContribution (Real.exp y) T β‖ ≤
        Real.exp ((β - δ) * y) *
          ∑ ρ ∈ nontrivialZerosFinset T,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
      norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum_nontrivialZerosFinset
        T β δ y hy hgap
    _ = Real.exp ((β - δ) * y) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
      simp only [ExplicitFormulaAux.globalReciprocalZeroMultiplicity]
    _ ≤ Real.exp ((β - δ) * y) * (C * (1 + Real.log (T + 6)) ^ 2) :=
      mul_le_mul_of_nonneg_left (hCbound T hT) (Real.exp_nonneg _)

end

end PrimeNumberTheorem.ZeroForcedOscillation
