import PrimeNumberTheorem.GlobalZeroCount
import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula
import HardyTheorem.HardyIntegralContradiction

/-!
# Quantitative maximal zero packages and moving-height transfer

This module starts with elementary estimates for the complementary zero
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
  height-`T` truncation sum;
* an explicit `B_T / E_T` interval-length threshold making the finite
  mean-square amplitude strictly positive;
* eventual nonemptiness of every maximal package from Hardy's theorem;
* a moving-height lower bound in which the raw finite-height approximation
  norm is replaced by the proved pointwise-in-`x`, all-heights rate.

What is NOT proved here: the pointwise all-heights constant is not controlled
uniformly over the moving logarithmic intervals, the complementary gap and
`B_T / E_T` are not bounded uniformly as `T` grows, and no unconditional
`Omega` or `Omega_±` theorem is claimed.
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

/-- Hardy's theorem supplies one nontrivial zero. Monotonicity of the
height-truncated zero finset then makes every sufficiently large truncation
nonempty. -/
theorem exists_eventually_nontrivialZerosFinset_nonempty :
    ∃ T0 : ℝ, 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      (nontrivialZerosFinset T).Nonempty := by
  rcases HardyTheorem.hardy_zeros_unbounded_target_proved 1 with
    ⟨t, ht, hzero⟩
  let ρ : ℂ := (1 / 2 : ℂ) + I * t
  have hzeta : riemannZeta ρ = 0 := by
    have hrho : ρ = (0.5 : ℂ) + I * t := by
      norm_num [ρ]
    rw [hrho]
    exact hzero
  have hρ : RiemannHypothesis.IsNontrivialZero ρ := by
    refine ⟨hzeta, ?_, ?_⟩
    · norm_num [ρ]
    · norm_num [ρ]
  let T0 : ℝ := max 8 t
  refine ⟨T0, le_max_left _ _, ?_⟩
  intro T hT
  have htT : t ≤ T := (le_max_right (8 : ℝ) t).trans hT
  have hρmem : ρ ∈ nontrivialZerosFinset T := by
    apply mem_nontrivialZerosFinset.mpr
    refine ⟨hρ, ?_⟩
    have ht0 : 0 ≤ t := by linarith
    simpa [ρ, abs_of_nonneg ht0] using htT
  exact ⟨ρ, hρmem⟩

/-- Consequently the automatically selected maximal-real-part package is
nonempty at every sufficiently large height. -/
theorem exists_eventually_maximalRealPartZeroPackage_nonempty :
    ∃ T0 : ℝ, 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      (maximalRealPartZeroPackage T).Nonempty := by
  rcases exists_eventually_nontrivialZerosFinset_nonempty with
    ⟨T0, hT0, hnonempty⟩
  refine ⟨T0, hT0, ?_⟩
  intro T hT
  exact maximalRealPartZeroPackage_nonempty T (hnonempty T hT)

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

/-- The diagonal energy of the automatically selected maximal-real-part zero
package. Analytic multiplicity remains part of each coefficient. -/
def maximalZeroPackageEnergy (T : ℝ) : ℝ :=
  ∑ ρ ∈ maximalRealPartZeroPackage T,
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ ^ 2

/-- The ordered off-diagonal budget of the automatically selected maximal
zero package. -/
def maximalZeroPackageOffDiagonalBound (T : ℝ) : ℝ :=
  offDiagonalBound (maximalRealPartZeroPackage T)
    (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹) Complex.im

/-- Ordered pairs of distinct members of a finite frequency package. -/
def distinctOrderedPairs {ι : Type*} [DecidableEq ι]
    (S : Finset ι) : Finset (ι × ι) :=
  (S ×ˢ S).filter fun p => p.1 ≠ p.2

/-- The minimum positive frequency spacing of a finite package. The value is
`1` when there is no distinct pair, so the definition remains positive for
empty and singleton packages. -/
def minimumPositiveFrequencySpacing {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (ω : ι → ℝ) : ℝ :=
  if h : (distinctOrderedPairs S).Nonempty then
    ((distinctOrderedPairs S).image fun p => |ω p.2 - ω p.1|).min'
      (h.image fun p => |ω p.2 - ω p.1|)
  else
    1

/-- A coefficient-aware pairwise upper bound for `B / E`. It retains the
actual coefficient norms and every actual pair spacing before the coarser
cardinality/minimum-spacing estimate is applied. -/
def coefficientAwareSpacingThreshold {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (ω : ι → ℝ) : ℝ :=
  (∑ i ∈ S, ∑ j ∈ S.erase i,
      (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / |ω j - ω i|) /
    ∑ i ∈ S, ‖c i‖ ^ 2

/-- The actual minimum imaginary-part spacing of the maximal zero package. -/
def maximalZeroPackageMinimumImaginarySpacing (T : ℝ) : ℝ :=
  minimumPositiveFrequencySpacing (maximalRealPartZeroPackage T) Complex.im

/-- The coefficient-aware pairwise threshold for the maximal package.
Analytic multiplicity remains inside both coefficient norms. -/
def maximalZeroPackageCoefficientAwareSpacingThreshold (T : ℝ) : ℝ :=
  coefficientAwareSpacingThreshold (maximalRealPartZeroPackage T)
    (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹) Complex.im

/-- The exact interval-length threshold `B_T / E_T` above which the
finite-package mean-square bracket `E_T - B_T / L` is strictly positive.
The definition is total; its positivity use requires a nonempty package. -/
def maximalZeroPackageIntervalLengthThreshold (T : ℝ) : ℝ :=
  maximalZeroPackageOffDiagonalBound T / maximalZeroPackageEnergy T

/-- A canonical, computable-in-the-finite-data interval length that strictly
exceeds the mean-square threshold whenever the maximal package is nonempty. -/
def maximalZeroPackageCanonicalIntervalLength (T : ℝ) : ℝ :=
  maximalZeroPackageIntervalLengthThreshold T + 1

/-- The explicit positive-amplitude candidate supplied by the mean-square
argument on a logarithmic interval of length `L`. -/
def maximalZeroPackageMeanSquareMain (T L y : ℝ) : ℝ :=
  Real.exp (maximalZeroRealPart T * y) ^ 2 *
    (maximalZeroPackageEnergy T -
      maximalZeroPackageOffDiagonalBound T / L)

/-- Pointwise-in-`x`, uniform-in-height approximation budget supplied by the
all-heights explicit formula after `x = exp y` has been selected. -/
def movingHeightApproximationBudget (K T : ℝ) : ℝ :=
  K * (1 + Real.log (T + 8)) ^ 2 / T

/-- Membership in the ordered distinct-pair finset. -/
theorem mem_distinctOrderedPairs_iff {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {i j : ι} :
    (i, j) ∈ distinctOrderedPairs S ↔ i ∈ S ∧ j ∈ S ∧ i ≠ j := by
  simp only [distinctOrderedPairs, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hi, hj⟩, hij⟩
    exact ⟨hi, hj, hij⟩
  · rintro ⟨hi, hj, hij⟩
    exact ⟨⟨hi, hj⟩, hij⟩

/-- The minimum spacing controls every distinct pair in the package. -/
theorem minimumPositiveFrequencySpacing_le_abs_sub
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (ω : ι → ℝ) {i j : ι}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    minimumPositiveFrequencySpacing S ω ≤ |ω j - ω i| := by
  classical
  unfold minimumPositiveFrequencySpacing
  split_ifs with h
  · apply Finset.min'_le
    exact Finset.mem_image.mpr
      ⟨(i, j), mem_distinctOrderedPairs_iff.mpr ⟨hi, hj, hij⟩, rfl⟩
  · exfalso
    exact h ⟨(i, j), mem_distinctOrderedPairs_iff.mpr ⟨hi, hj, hij⟩⟩

/-- Injective frequencies make the totalized minimum spacing strictly
positive, including the empty and singleton conventions. -/
theorem minimumPositiveFrequencySpacing_pos
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (ω : ι → ℝ) (hω : Set.InjOn ω ↑S) :
    0 < minimumPositiveFrequencySpacing S ω := by
  classical
  unfold minimumPositiveFrequencySpacing
  split_ifs with h
  · let D : Finset ℝ :=
      (distinctOrderedPairs S).image fun p => |ω p.2 - ω p.1|
    have hD : D.Nonempty := h.image fun p => |ω p.2 - ω p.1|
    have hmem : D.min' hD ∈ D := Finset.min'_mem D hD
    rcases Finset.mem_image.mp hmem with ⟨p, hp, hpval⟩
    have hpdata := mem_distinctOrderedPairs_iff.mp hp
    have hfreq : ω p.2 ≠ ω p.1 := by
      intro heq
      exact hpdata.2.2 (hω hpdata.2.1 hpdata.1 heq).symm
    rw [← hpval]
    exact abs_pos.mpr (sub_ne_zero.mpr hfreq)
  · norm_num

/-- The moving-height approximation budget is nonnegative in its range of
use. -/
theorem movingHeightApproximationBudget_nonneg (K T : ℝ)
    (hK : 0 ≤ K) (hT : 8 ≤ T) :
    0 ≤ movingHeightApproximationBudget K T := by
  unfold movingHeightApproximationBudget
  exact div_nonneg (mul_nonneg hK (sq_nonneg _)) (by linarith)

/-- Every ordered off-diagonal budget is nonnegative. -/
theorem offDiagonalBound_nonneg {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (ω : ι → ℝ) :
    0 ≤ offDiagonalBound S c ω := by
  unfold offDiagonalBound
  exact Finset.sum_nonneg fun i hi =>
    Finset.sum_nonneg fun j hj =>
      div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (norm_nonneg (c i)))
          (norm_nonneg (c j)))
        (abs_nonneg (ω j - ω i))

/-- Termwise AM-GM turns the original off-diagonal budget into the
coefficient-aware pairwise threshold. -/
theorem offDiagonalBound_div_energy_le_coefficientAwareSpacingThreshold
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (ω : ι → ℝ)
    (henergy : 0 < ∑ i ∈ S, ‖c i‖ ^ 2) :
    offDiagonalBound S c ω / (∑ i ∈ S, ‖c i‖ ^ 2) ≤
      coefficientAwareSpacingThreshold S c ω := by
  unfold offDiagonalBound coefficientAwareSpacingThreshold
  apply div_le_div_of_nonneg_right _ henergy.le
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]

/-- In a nonempty finite package, each member occurs in exactly `card - 1`
ordered pairs in each coordinate. -/
theorem sum_orderedDistinct_sq_add_sq
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (hS : S.Nonempty) :
    (∑ i ∈ S, ∑ j ∈ S.erase i, (f i + f j)) =
      2 * ((S.card - 1 : ℕ) : ℝ) * ∑ i ∈ S, f i := by
  classical
  have hcard : (1 : ℕ) ≤ S.card := Finset.one_le_card.mpr hS
  have hcast :
      ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
    rw [Nat.cast_sub hcard]
    norm_num
  have hfirst :
      (∑ i ∈ S, ∑ _j ∈ S.erase i, f i) =
        ((S.card - 1 : ℕ) : ℝ) * ∑ i ∈ S, f i := by
    calc
      (∑ i ∈ S, ∑ _j ∈ S.erase i, f i) =
          ∑ i ∈ S, ((S.erase i).card : ℝ) * f i := by
            apply Finset.sum_congr rfl
            intro i hi
            simp
      _ = ∑ i ∈ S, (((S.card - 1 : ℕ) : ℝ) * f i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.card_erase_of_mem hi]
      _ = ((S.card - 1 : ℕ) : ℝ) * ∑ i ∈ S, f i := by
            rw [Finset.mul_sum]
  have hsecond :
      (∑ i ∈ S, ∑ j ∈ S.erase i, f j) =
        ((S.card - 1 : ℕ) : ℝ) * ∑ i ∈ S, f i := by
    calc
      (∑ i ∈ S, ∑ j ∈ S.erase i, f j) =
          ∑ i ∈ S, ((∑ j ∈ S, f j) - f i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.sum_erase_add _ _ hi]
            ring
      _ = (S.card : ℝ) * (∑ j ∈ S, f j) - ∑ i ∈ S, f i := by
            rw [Finset.sum_sub_distrib]
            simp
      _ = ((S.card - 1 : ℕ) : ℝ) * ∑ i ∈ S, f i := by
            rw [hcast]
            ring
  simp_rw [Finset.sum_add_distrib]
  rw [hfirst, hsecond]
  ring

/-- The coefficient-aware threshold is bounded by the package cardinality and
the rigorously defined minimum spacing. -/
theorem coefficientAwareSpacingThreshold_le_card_sub_one_div_spacing
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (ω : ι → ℝ)
    (hS : S.Nonempty) (hω : Set.InjOn ω ↑S)
    (henergy : 0 < ∑ i ∈ S, ‖c i‖ ^ 2) :
    coefficientAwareSpacingThreshold S c ω ≤
      2 * ((S.card - 1 : ℕ) : ℝ) /
        minimumPositiveFrequencySpacing S ω := by
  let δ := minimumPositiveFrequencySpacing S ω
  have hδ : 0 < δ := minimumPositiveFrequencySpacing_pos S ω hω
  have hpairs :
      (∑ i ∈ S, ∑ j ∈ S.erase i,
          (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / |ω j - ω i|) ≤
        ∑ i ∈ S, ∑ j ∈ S.erase i,
          (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / δ := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hδij : δ ≤ |ω j - ω i| :=
      minimumPositiveFrequencySpacing_le_abs_sub S ω hi hjS hij
    exact div_le_div_of_nonneg_left
      (add_nonneg (sq_nonneg _) (sq_nonneg _)) hδ hδij
  unfold coefficientAwareSpacingThreshold
  calc
    (∑ i ∈ S, ∑ j ∈ S.erase i,
          (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / |ω j - ω i|) /
        (∑ i ∈ S, ‖c i‖ ^ 2) ≤
      (∑ i ∈ S, ∑ j ∈ S.erase i,
          (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / δ) /
        (∑ i ∈ S, ‖c i‖ ^ 2) :=
      div_le_div_of_nonneg_right hpairs henergy.le
    _ = ((∑ i ∈ S, ∑ j ∈ S.erase i,
          (‖c i‖ ^ 2 + ‖c j‖ ^ 2)) / δ) /
        (∑ i ∈ S, ‖c i‖ ^ 2) := by
      congr 1
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_div]
    _ = 2 * ((S.card - 1 : ℕ) : ℝ) / δ := by
      rw [sum_orderedDistinct_sq_add_sq S (fun i => ‖c i‖ ^ 2) hS]
      field_simp
    _ = 2 * ((S.card - 1 : ℕ) : ℝ) /
        minimumPositiveFrequencySpacing S ω := rfl

/-- The maximal-package diagonal energy is always nonnegative. -/
theorem maximalZeroPackageEnergy_nonneg (T : ℝ) :
    0 ≤ maximalZeroPackageEnergy T := by
  unfold maximalZeroPackageEnergy
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A nonempty maximal package has strictly positive diagonal energy. The
proof uses both facts encoded by nontrivial-zero membership: `ρ ≠ 0` and
positive analytic multiplicity. -/
theorem maximalZeroPackageEnergy_pos (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    0 < maximalZeroPackageEnergy T := by
  classical
  rcases hpackage with ⟨ρ, hρ⟩
  unfold maximalZeroPackageEnergy
  refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨ρ, hρ, ?_⟩
  have hzero := (mem_maximalRealPartZeroPackage.mp hρ).1
  have hρ0 : ρ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith [hzero.2.1]
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith [hzero.2.2]
  have horder : 0 < analyticOrderNatAt riemannZeta ρ :=
    ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hρ1 hzero.1
  have horderCast : (analyticOrderNatAt riemannZeta ρ : ℂ) ≠ 0 := by
    exact_mod_cast horder.ne'
  have hcoeff :
      (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹ ≠ 0 :=
    mul_ne_zero horderCast (inv_ne_zero hρ0)
  have hnorm :
      0 < ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ :=
    norm_pos_iff.mpr hcoeff
  nlinarith

/-- Distinct zeros in the maximal equal-real-part package have a strictly
positive minimum imaginary-part spacing. -/
theorem maximalZeroPackageMinimumImaginarySpacing_pos (T : ℝ) :
    0 < maximalZeroPackageMinimumImaginarySpacing T := by
  unfold maximalZeroPackageMinimumImaginarySpacing
  apply minimumPositiveFrequencySpacing_pos
  apply im_injOn_of_re_eq _ (maximalZeroRealPart T)
  intro ρ hρ
  exact (mem_maximalRealPartZeroPackage.mp hρ).2.2

/-- The exact `B_T / E_T` threshold is bounded by the stronger
coefficient-aware finite-data invariant. Analytic multiplicities are retained
inside both quantities. -/
theorem
    maximalZeroPackageIntervalLengthThreshold_le_coefficientAwareSpacingThreshold
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    maximalZeroPackageIntervalLengthThreshold T ≤
      maximalZeroPackageCoefficientAwareSpacingThreshold T := by
  exact
    offDiagonalBound_div_energy_le_coefficientAwareSpacingThreshold
      (maximalRealPartZeroPackage T)
      (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
      Complex.im (maximalZeroPackageEnergy_pos T hpackage)

/-- The coefficient-aware threshold is at most
`2 * (card - 1) / minimumSpacing`. -/
theorem
    maximalZeroPackageCoefficientAwareSpacingThreshold_le_card_sub_one_div_spacing
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    maximalZeroPackageCoefficientAwareSpacingThreshold T ≤
      2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
        maximalZeroPackageMinimumImaginarySpacing T := by
  apply coefficientAwareSpacingThreshold_le_card_sub_one_div_spacing
  · exact hpackage
  · apply im_injOn_of_re_eq _ (maximalZeroRealPart T)
    intro ρ hρ
    exact (mem_maximalRealPartZeroPackage.mp hρ).2.2
  · exact maximalZeroPackageEnergy_pos T hpackage

/-- Explicit cardinality/minimum-spacing upper bound for the exact
mean-square interval threshold. -/
theorem maximalZeroPackageIntervalLengthThreshold_le_card_sub_one_div_spacing
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    maximalZeroPackageIntervalLengthThreshold T ≤
      2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
        maximalZeroPackageMinimumImaginarySpacing T :=
  (maximalZeroPackageIntervalLengthThreshold_le_coefficientAwareSpacingThreshold
      T hpackage).trans
    (maximalZeroPackageCoefficientAwareSpacingThreshold_le_card_sub_one_div_spacing
      T hpackage)

/-- The previously opaque canonical interval length is therefore explicitly
controlled by finite cardinality and the actual minimum imaginary spacing. -/
theorem maximalZeroPackageCanonicalIntervalLength_le_card_sub_one_div_spacing
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    maximalZeroPackageCanonicalIntervalLength T ≤
      2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T + 1 := by
  unfold maximalZeroPackageCanonicalIntervalLength
  linarith
    [maximalZeroPackageIntervalLengthThreshold_le_card_sub_one_div_spacing
      T hpackage]

/-- The maximal-package ordered off-diagonal budget is nonnegative. -/
theorem maximalZeroPackageOffDiagonalBound_nonneg (T : ℝ) :
    0 ≤ maximalZeroPackageOffDiagonalBound T := by
  exact offDiagonalBound_nonneg _ _ _

/-- The explicit interval-length threshold is nonnegative, including under
the total empty-package convention. -/
theorem maximalZeroPackageIntervalLengthThreshold_nonneg (T : ℝ) :
    0 ≤ maximalZeroPackageIntervalLengthThreshold T := by
  exact div_nonneg (maximalZeroPackageOffDiagonalBound_nonneg T)
    (maximalZeroPackageEnergy_nonneg T)

/-- The canonical length exceeds the exact mean-square threshold by one. -/
theorem maximalZeroPackageIntervalLengthThreshold_lt_canonical (T : ℝ) :
    maximalZeroPackageIntervalLengthThreshold T <
      maximalZeroPackageCanonicalIntervalLength T := by
  unfold maximalZeroPackageCanonicalIntervalLength
  linarith

/-- For a nonempty maximal package, every interval longer than `B_T / E_T`
has a strictly positive mean-square bracket. No positivity assumption on the
bracket is supplied by the caller. -/
theorem maximalZeroPackageMeanSquareBracket_pos (T : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    {a b : ℝ}
    (hlength : maximalZeroPackageIntervalLengthThreshold T < b - a) :
    0 < maximalZeroPackageEnergy T -
      maximalZeroPackageOffDiagonalBound T / (b - a) := by
  have henergy := maximalZeroPackageEnergy_pos T hpackage
  have hthreshold :=
    maximalZeroPackageIntervalLengthThreshold_nonneg T
  have hinterval : 0 < b - a := lt_of_le_of_lt hthreshold hlength
  have hoff_lt :
      maximalZeroPackageOffDiagonalBound T <
        (b - a) * maximalZeroPackageEnergy T := by
    exact (div_lt_iff₀ henergy).mp hlength
  have hratio :
      maximalZeroPackageOffDiagonalBound T / (b - a) <
        maximalZeroPackageEnergy T := by
    apply (div_lt_iff₀ hinterval).mpr
    simpa [mul_comm] using hoff_lt
  linarith

/-- The full mean-square main term is strictly positive on every interval
whose length exceeds the explicit threshold. -/
theorem maximalZeroPackageMeanSquareMain_pos (T y : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    {a b : ℝ}
    (hlength : maximalZeroPackageIntervalLengthThreshold T < b - a) :
    0 < maximalZeroPackageMeanSquareMain T (b - a) y := by
  unfold maximalZeroPackageMeanSquareMain
  exact mul_pos (sq_pos_of_pos (Real.exp_pos _))
    (maximalZeroPackageMeanSquareBracket_pos T hpackage hlength)

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

/-- A nonempty maximal zero package forces a strictly positive mean-square
amplitude on every logarithmic interval longer than the explicit threshold
`B_T / E_T`. The square root of that amplitude is transferred all the way to
the actual `ψ₀(exp y) - exp y` error.

The finite-height approximation norm, complementary package budget, and
closed terms remain explicitly subtracted. Consequently the theorem removes
the former mean-square-sign degeneracy but does not claim that the final
right-hand lower-bound expression is positive without controlling those
genuine remainders. -/
theorem exists_C_forall_fixedHeight_maximalZeroPackage_strict_lower_bound
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      (maximalRealPartZeroPackage T).Nonempty → ∀ {a b : ℝ},
        0 < a → maximalZeroPackageIntervalLengthThreshold T < b - a →
          ∃ y ∈ Set.Ioo a b,
            0 < maximalZeroPackageMeanSquareMain T (b - a) y ∧
            0 < Real.sqrt (maximalZeroPackageMeanSquareMain T (b - a) y) ∧
            Real.sqrt (maximalZeroPackageMeanSquareMain T (b - a) y) -
                (Real.exp ((maximalZeroRealPart T -
                    maximalComplementaryRealPartGap T) * y) *
                  (C * (1 + Real.log (T + 6)) ^ 2) +
                  ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                    (chebyshevPsi0 (Real.exp y) : ℂ)‖) -
                (Real.log (2 * Real.pi) +
                  (1 / 2 : ℝ) * Real.exp (-2 * y) /
                    (1 - Real.exp (-2 * y))) ≤
              ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  rcases
      exists_C_forall_fixedHeight_maximalZeroPackage_transfers_to_psi0_error with
    ⟨C, hC, htransfer⟩
  refine ⟨C, hC, ?_⟩
  intro T hT hpackage a b ha hlength
  have hlength_pos : 0 < b - a :=
    lt_of_le_of_lt
      (maximalZeroPackageIntervalLengthThreshold_nonneg T) hlength
  have hab : a < b := sub_pos.mp hlength_pos
  rcases htransfer T hT ha hab with
    ⟨y, hy, hmean, hpsi⟩
  have hmain_pos :
      0 < maximalZeroPackageMeanSquareMain T (b - a) y :=
    maximalZeroPackageMeanSquareMain_pos T y hpackage hlength
  have hmean' :
      maximalZeroPackageMeanSquareMain T (b - a) y ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ ^ 2 := by
    simpa only [maximalZeroPackageMeanSquareMain,
      maximalZeroPackageEnergy, maximalZeroPackageOffDiagonalBound,
      maximalRealPartZeroPackage] using hmean
  have hsqrt_le :
      Real.sqrt (maximalZeroPackageMeanSquareMain T (b - a) y) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ := by
    calc
      Real.sqrt (maximalZeroPackageMeanSquareMain T (b - a) y) ≤
          Real.sqrt
            (‖equalRealPartZeroPackageContribution (Real.exp y) T
                (maximalZeroRealPart T)‖ ^ 2) :=
        Real.sqrt_le_sqrt hmean'
      _ = ‖equalRealPartZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ :=
        Real.sqrt_sq (norm_nonneg _)
  refine ⟨y, hy, hmain_pos, Real.sqrt_pos.mpr hmain_pos, ?_⟩
  linarith

/-- Canonical fixed-height form of the strict transfer. The interval length is
chosen directly from the finite zero data as `B_T / E_T + 1`, so callers no
longer supply an interval-length inequality. This length may vary with `T`;
no uniform control as `T → ∞` is asserted. -/
theorem
    exists_C_forall_fixedHeight_maximalZeroPackage_strict_lower_bound_on_canonical_interval
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      (maximalRealPartZeroPackage T).Nonempty → ∀ {a : ℝ},
        0 < a →
          ∃ y ∈ Set.Ioo a (a + maximalZeroPackageCanonicalIntervalLength T),
            0 < maximalZeroPackageMeanSquareMain T
                (maximalZeroPackageCanonicalIntervalLength T) y ∧
            0 < Real.sqrt (maximalZeroPackageMeanSquareMain T
                  (maximalZeroPackageCanonicalIntervalLength T) y) ∧
            Real.sqrt (maximalZeroPackageMeanSquareMain T
                  (maximalZeroPackageCanonicalIntervalLength T) y) -
                (Real.exp ((maximalZeroRealPart T -
                    maximalComplementaryRealPartGap T) * y) *
                  (C * (1 + Real.log (T + 6)) ^ 2) +
                  ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                    (chebyshevPsi0 (Real.exp y) : ℂ)‖) -
                (Real.log (2 * Real.pi) +
                  (1 / 2 : ℝ) * Real.exp (-2 * y) /
                    (1 - Real.exp (-2 * y))) ≤
              ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  rcases
      exists_C_forall_fixedHeight_maximalZeroPackage_strict_lower_bound with
    ⟨C, hC, hstrict⟩
  refine ⟨C, hC, ?_⟩
  intro T hT hpackage a ha
  have hlength :
      maximalZeroPackageIntervalLengthThreshold T <
        (a + maximalZeroPackageCanonicalIntervalLength T) - a := by
    simpa only [add_sub_cancel_left] using
      maximalZeroPackageIntervalLengthThreshold_lt_canonical T
  rcases hstrict T hT hpackage ha hlength with
    ⟨y, hy, hmain, hsqrt, hpsi⟩
  refine ⟨y, hy, ?_, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using hmain
  · simpa only [add_sub_cancel_left] using hsqrt
  · simpa only [add_sub_cancel_left] using hpsi

/-- Moving-height quantitative zero-forced transfer. Hardy's theorem removes
the maximal-package nonemptiness hypothesis beyond one fixed threshold. For
every later truncation height and every positive logarithmic starting point,
the canonical interval has a point with strictly positive mean-square
amplitude.

The raw finite-height approximation norm is eliminated using the proved
all-heights explicit-formula rate. The returned constant `K` depends on the
selected point `y`, but its certificate controls every height `U ≥ 8`, not only
the chosen `T`. Analytic multiplicities, the actual complementary gap, and the
closed terms remain explicit. -/
theorem
    exists_C_T0_forall_movingHeight_maximalZeroPackage_quantitative_lower_bound :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      ∀ {a : ℝ}, 0 < a →
        ∃ y ∈ Set.Ioo a (a + maximalZeroPackageCanonicalIntervalLength T),
          ∃ K : ℝ, 0 ≤ K ∧
            (∀ U : ℝ, 8 ≤ U →
              ‖explicitFormulaApproxWithMultiplicity (Real.exp y) U -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
                movingHeightApproximationBudget K U) ∧
            0 < maximalZeroPackageMeanSquareMain T
                (maximalZeroPackageCanonicalIntervalLength T) y ∧
            0 < Real.sqrt (maximalZeroPackageMeanSquareMain T
                (maximalZeroPackageCanonicalIntervalLength T) y) ∧
            Real.sqrt (maximalZeroPackageMeanSquareMain T
                  (maximalZeroPackageCanonicalIntervalLength T) y) -
                (Real.exp ((maximalZeroRealPart T -
                    maximalComplementaryRealPartGap T) * y) *
                  (C * (1 + Real.log (T + 6)) ^ 2) +
                  movingHeightApproximationBudget K T) -
                (Real.log (2 * Real.pi) +
                  (1 / 2 : ℝ) * Real.exp (-2 * y) /
                    (1 - Real.exp (-2 * y))) ≤
              ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  rcases
      exists_C_forall_fixedHeight_maximalZeroPackage_strict_lower_bound_on_canonical_interval
      with ⟨C, hC, hfixed⟩
  rcases exists_eventually_maximalRealPartZeroPackage_nonempty with
    ⟨T0, hT0, hpackage⟩
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT a ha
  have hT8 : 8 ≤ T := hT0.trans hT
  rcases hfixed T (by linarith) (hpackage T hT) ha with
    ⟨y, hy, hmain, hsqrt, hpsi⟩
  have hypos : 0 < y := lt_trans ha hy.1
  have hx : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hypos
  rcases
      _root_.PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div
        hx with ⟨K, hK, happrox⟩
  have happroxT :
      ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
        movingHeightApproximationBudget K T := by
    simpa only [movingHeightApproximationBudget] using happrox T hT8
  refine ⟨y, hy, K, hK, ?_, hmain, hsqrt, ?_⟩
  · intro U hU
    simpa only [movingHeightApproximationBudget] using happrox U hU
  · linarith

end

end PrimeNumberTheorem.ZeroForcedOscillation
