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

/-- The maximal real part among the nontrivial zeros in the height-`T`
truncation. It is defined to be `0` when the truncation is empty. -/
def maximalZeroRealPart (T : ℝ) : ℝ :=
  if hT : (nontrivialZerosFinset T).Nonempty then
    (nontrivialZerosFinset T).sup' hT Complex.re
  else
    0

/-- The complete package of height-`T` zeros on the maximal-real-part layer. -/
def maximalRealPartZeroPackage (T : ℝ) : Finset ℂ :=
  equalRealPartZeroPackage T (maximalZeroRealPart T)

/-- The explicit gap below the maximal real part at height `T`. When the
complement is nonempty, this is the difference between the maximal real part
and the largest real part in the complement. When the complement is empty, the
arbitrary positive value `1` makes the definition total. -/
def maximalComplementaryRealPartGap (T : ℝ) : ℝ :=
  if hC :
      (complementaryZeroPackage T (maximalZeroRealPart T)).Nonempty then
    maximalZeroRealPart T -
      (complementaryZeroPackage T (maximalZeroRealPart T)).sup' hC Complex.re
  else
    1

/-- The empty truncation uses the specified default maximal real part `0`. -/
theorem maximalZeroRealPart_eq_zero_of_empty
    (T : ℝ) (hT : nontrivialZerosFinset T = ∅) :
    maximalZeroRealPart T = 0 := by
  simp [maximalZeroRealPart, hT]

/-- Every zero in the height-`T` truncation lies at or to the left of the
selected maximal real part. -/
theorem re_le_maximalZeroRealPart {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ nontrivialZerosFinset T) :
    ρ.re ≤ maximalZeroRealPart T := by
  classical
  have hT : (nontrivialZerosFinset T).Nonempty := ⟨ρ, hρ⟩
  rw [maximalZeroRealPart, dif_pos hT]
  exact Finset.le_sup' Complex.re hρ

/-- Membership in the maximal package exactly records a nontrivial zero in the
height truncation whose real part is the selected maximum. -/
theorem mem_maximalRealPartZeroPackage {ρ : ℂ} {T : ℝ} :
    ρ ∈ maximalRealPartZeroPackage T ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧
        |ρ.im| ≤ T ∧ ρ.re = maximalZeroRealPart T := by
  simpa only [maximalRealPartZeroPackage] using
    (mem_equalRealPartZeroPackage
      (ρ := ρ) (T := T) (β := maximalZeroRealPart T))

/-- A nonempty height truncation has at least one zero on its maximal-real-part
layer. -/
theorem maximalRealPartZeroPackage_nonempty
    (T : ℝ) (hT : (nontrivialZerosFinset T).Nonempty) :
    (maximalRealPartZeroPackage T).Nonempty := by
  classical
  rcases Finset.exists_mem_eq_sup' hT Complex.re with ⟨ρ, hρ, hre⟩
  refine ⟨ρ, mem_maximalRealPartZeroPackage.mpr ?_⟩
  rcases mem_nontrivialZerosFinset.mp hρ with ⟨hzero, him⟩
  refine ⟨hzero, him, ?_⟩
  rw [maximalZeroRealPart, dif_pos hT, hre]

/-- Every member of the complementary package is an actual nontrivial zeta
zero at the requested height whose real part differs from `β`. -/
theorem mem_complementaryZeroPackage {ρ : ℂ} {T β : ℝ} :
    ρ ∈ complementaryZeroPackage T β ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T ∧ ρ.re ≠ β := by
  classical
  simp only [complementaryZeroPackage, Finset.mem_filter,
    mem_nontrivialZerosFinset, and_assoc]

/-- Every zero outside the maximal-real-part package has strictly smaller real
part. -/
private theorem re_lt_maximalZeroRealPart_of_mem_complementary
    {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T)) :
    ρ.re < maximalZeroRealPart T := by
  rcases mem_complementaryZeroPackage.mp hρ with ⟨hzero, him, hne⟩
  exact lt_of_le_of_ne
    (re_le_maximalZeroRealPart (mem_nontrivialZerosFinset.mpr ⟨hzero, him⟩)) hne

/-- The explicitly selected complementary real-part gap is always positive.
For an empty complement this is the default value `1`; otherwise positivity
follows from finiteness and strict maximality of the selected layer. -/
theorem maximalComplementaryRealPartGap_pos (T : ℝ) :
    0 < maximalComplementaryRealPartGap T := by
  classical
  by_cases hC :
      (complementaryZeroPackage T (maximalZeroRealPart T)).Nonempty
  · rw [maximalComplementaryRealPartGap, dif_pos hC]
    exact sub_pos.mpr ((Finset.sup'_lt_iff hC).mpr fun ρ hρ =>
      re_lt_maximalZeroRealPart_of_mem_complementary hρ)
  · simp [maximalComplementaryRealPartGap, hC]

/-- Every complementary zero lies at least the explicit fixed-height gap below
the maximal real part. -/
theorem re_le_maximalZeroRealPart_sub_gap
    {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T)) :
    ρ.re ≤ maximalZeroRealPart T - maximalComplementaryRealPartGap T := by
  classical
  have hC :
      (complementaryZeroPackage T (maximalZeroRealPart T)).Nonempty :=
    ⟨ρ, hρ⟩
  rw [maximalComplementaryRealPartGap, dif_pos hC]
  have hsup := Finset.le_sup' Complex.re hρ
  linarith

/-- At fixed height the complement is empty or the explicit positive gap
separates every complementary zero from the maximal-real-part layer. -/
theorem complementaryZeroPackage_maximal_eq_empty_or_pos_gap (T : ℝ) :
    complementaryZeroPackage T (maximalZeroRealPart T) = ∅ ∨
      (0 < maximalComplementaryRealPartGap T ∧
        ∀ ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T),
          ρ.re ≤ maximalZeroRealPart T - maximalComplementaryRealPartGap T) := by
  classical
  by_cases hC :
      complementaryZeroPackage T (maximalZeroRealPart T) = ∅
  · exact Or.inl hC
  · exact Or.inr ⟨maximalComplementaryRealPartGap_pos T,
      fun _ hρ => re_le_maximalZeroRealPart_sub_gap hρ⟩

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

/-- Fixed-height complementary bound with no abstract gap hypothesis: the
maximal layer and its positive gap are selected directly from the finite
height-`T` zero finset. This says nothing uniform as `T` varies. -/
theorem
    norm_complementaryZeroPackageContribution_le_exp_maximal_gap_mul_sum_nontrivialZerosFinset
    (T y : ℝ) (hy : 0 ≤ y) :
    ‖complementaryZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ≤
      Real.exp ((maximalZeroRealPart T -
          maximalComplementaryRealPartGap T) * y) *
        ∑ ρ ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
  norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum_nontrivialZerosFinset
    T (maximalZeroRealPart T) (maximalComplementaryRealPartGap T) y hy
      (fun _ hρ => re_le_maximalZeroRealPart_sub_gap hρ)

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

/-- Fixed-height quantitative complementary bound with no externally supplied
real-part layer or gap.  The maximal layer and its positive gap are selected
from `nontrivialZerosFinset T`, and the remaining reciprocal-norm sum is
absorbed into the repository's global `O(log^2 T)` estimate. -/
theorem
    exists_norm_complementaryZeroPackageContribution_le_exp_maximal_gap_mul_log_sq
    (y : ℝ) (hy : 0 ≤ y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ≤
        Real.exp ((maximalZeroRealPart T -
            maximalComplementaryRealPartGap T) * y) *
          (C * (1 + Real.log (T + 6)) ^ 2) := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  intro T hT
  calc
    ‖complementaryZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ≤
      Real.exp ((maximalZeroRealPart T -
          maximalComplementaryRealPartGap T) * y) *
        ∑ ρ ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
      norm_complementaryZeroPackageContribution_le_exp_maximal_gap_mul_sum_nontrivialZerosFinset
        T y hy
    _ = Real.exp ((maximalZeroRealPart T -
          maximalComplementaryRealPartGap T) * y) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
      simp only [ExplicitFormulaAux.globalReciprocalZeroMultiplicity]
    _ ≤ Real.exp ((maximalZeroRealPart T -
          maximalComplementaryRealPartGap T) * y) *
        (C * (1 + Real.log (T + 6)) ^ 2) :=
      mul_le_mul_of_nonneg_left (hCbound T hT) (Real.exp_nonneg _)

/-- The uncontrolled part of the finite-height formula is bounded by the
maximal-layer complement and by the genuine finite-height approximation
error.  This is an exact triangle-inequality bridge, with no assumption on
the zero configuration. -/
theorem norm_zeroPackageUncontrolledRemainder_le_complementary_add_approximation
    (y T : ℝ) :
    ‖zeroPackageUncontrolledRemainder y T (maximalZeroRealPart T)‖ ≤
      ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ +
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ := by
  exact norm_add_le _ _

/-- Fixed-height zero-forced oscillation transfer with the dominant layer and
the complementary real-part gap selected automatically from the actual
height-`T` zero finset.  A single global constant controls the complementary
layer by the already proved reciprocal-zero `O(log^2 T)` estimate.

The theorem leaves only the genuine finite-height explicit-formula error and
the elementary closed terms in the lower bound for `ψ₀(exp y) - exp y`; it
requires no externally supplied `β`, `δ`, or zero-gap hypothesis.  It is a
fixed-height statement: neither the selected maximum nor its positive gap is
claimed uniform as `T` varies.  When the finite zero package is empty, or when
the displayed mean-square main term is nonpositive, the conclusion is a valid
but degenerate transfer rather than a nontrivial oscillation lower bound. -/
theorem exists_C_forall_fixedHeight_maximalZeroPackage_transfers_to_psi0_error
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T → ∀ {a b : ℝ},
      0 < a → a < b →
        ∃ y ∈ Set.Ioo a b,
          Real.exp (maximalZeroRealPart T * y) ^ 2 *
              ((∑ ρ ∈ maximalRealPartZeroPackage T,
                  ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2) -
                offDiagonalBound (maximalRealPartZeroPackage T)
                  (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
                  Complex.im / (b - a)) ≤
            ‖equalRealPartZeroPackageContribution (Real.exp y) T
                (maximalZeroRealPart T)‖ ^ 2 ∧
          ‖equalRealPartZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ -
              (Real.exp ((maximalZeroRealPart T -
                  maximalComplementaryRealPartGap T) * y) *
                (C * (1 + Real.log (T + 6)) ^ 2) +
                ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖) -
              (Real.log (2 * Real.pi) +
                (1 / 2 : ℝ) * Real.exp (-2 * y) /
                  (1 - Real.exp (-2 * y))) ≤
            ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  intro T hT a b ha hab
  rcases exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge
      T (maximalZeroRealPart T) hab with ⟨y, hy, hmean⟩
  have hypos : 0 < y := lt_trans ha hy.1
  have hynonneg : 0 ≤ y := hypos.le
  have hcomplement :
      ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ≤
        Real.exp ((maximalZeroRealPart T -
            maximalComplementaryRealPartGap T) * y) *
          (C * (1 + Real.log (T + 6)) ^ 2) := by
    calc
      ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ≤
          Real.exp ((maximalZeroRealPart T -
              maximalComplementaryRealPartGap T) * y) *
            ∑ ρ ∈ nontrivialZerosFinset T,
              (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
        norm_complementaryZeroPackageContribution_le_exp_maximal_gap_mul_sum_nontrivialZerosFinset
          T y hynonneg
      _ = Real.exp ((maximalZeroRealPart T -
              maximalComplementaryRealPartGap T) * y) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
        simp only [ExplicitFormulaAux.globalReciprocalZeroMultiplicity]
      _ ≤ Real.exp ((maximalZeroRealPart T -
              maximalComplementaryRealPartGap T) * y) *
            (C * (1 + Real.log (T + 6)) ^ 2) :=
        mul_le_mul_of_nonneg_left (hCbound T hT) (Real.exp_nonneg _)
  have huncontrolled :=
    norm_zeroPackageUncontrolledRemainder_le_complementary_add_approximation y T
  have htransfer :=
    norm_zeroPackage_sub_norm_uncontrolled_sub_closed_le_norm_chebyshevPsi0_sub_exp
      (T := T) (β := maximalZeroRealPart T) hypos
  refine ⟨y, hy, ?_, ?_⟩
  · simpa only [maximalRealPartZeroPackage] using hmean
  · linarith

end

end PrimeNumberTheorem.ZeroForcedOscillation
