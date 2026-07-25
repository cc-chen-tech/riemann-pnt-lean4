import PrimeNumberTheorem.CarneiroLittmannProfile
import PrimeNumberTheorem.GlobalZeroCount
import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula
import HardyTheorem.HardyIntegralContradiction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

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
* fixed-height exponential decay of the complementary contribution after
  normalization by the maximal real-part layer;
* a moving-height sufficient condition phrased in terms of the exact gap and
  the global `O(log^2 T)` reciprocal-multiplicity majorant;
* a concrete moving-height criterion reducing that majorant to the condition
  `gap(τ y) * y - 2 * log (1 + log (τ y + 6)) → +∞`;
* monotonicity of the complementary reciprocal-norm sum up to the full
  height-`T` truncation sum;
* an explicit `B_T / E_T` interval-length threshold making the finite
  mean-square amplitude strictly positive;
* a cardinality-free Hilbert mean-square bound and a unified exact/Hilbert
  visibility interval for the maximal zero package;
* a quantitative Hilbert lower main transferred through the complementary
  budget, explicit-formula approximation norm, and closed terms to the actual
  `ψ₀(exp y) - exp y` detector;
* a fixed-height asymptotic reduction showing that, for a nonempty maximal
  package, both the complementary package and the elementary closed terms
  vanish after normalization by the maximal-package scale; consequently a
  uniform approximation-smallness hypothesis on a translated canonical
  interval forces a genuinely positive `ψ₀` error at some point of that
  interval;
* a pointwise moving-height positivity criterion at height `T = τ(y)`,
  together with an instantiation of the genuine all-heights explicit-formula
  approximation budget at the same visible point;
* an `O(T log T)` bound for the size of the maximal package, converting the
  canonical interval length to an explicit `O(T log T / Δ_T)` bound;
* eventual nonemptiness of every maximal package from Hardy's theorem;
* a moving-height lower bound in which the raw finite-height approximation
  norm is replaced by the proved pointwise-in-`x`, all-heights rate.
* an explicit exponential-height rate transfer: if the pointwise constants
  grow at most like `K0 * exp (κ y)`, then choosing height `exp (lam * y)`
  makes the normalized approximation budget tend to zero whenever
  `κ < lam + β`, and hence eventually smaller than every prescribed positive
  gap.
* a complete structural refinement of the all-heights constant:
  `K(x) = Ch * x^2 + 2π * Cp(x) + 2 + 4 * Cg * x`, where `Ch` and `Cg` are
  global, the contour and bounded-gap growth is explicit, and `Cp(x)` is
  isolated as a first-order Perron residual carrying its own integral-error
  certificate;
* a family-level rate transfer showing that a bound only on
  `Cp(exp y)` controls the genuine all-heights approximation budget.

What is NOT proved here: the hard-cutoff Perron residual `Cp(exp y)` is not
controlled uniformly or exponentially over all moving logarithmic intervals.
The complementary gap and `B_T / E_T` are also not bounded uniformly as `T`
grows, and no unconditional `Omega` or `Omega_±` theorem is claimed.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem.ZeroForcedOscillation

noncomputable section

open DirichletPolynomial
open ExplicitFormulaResidues

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

/-- The maximal-real-part package is a subfamily of the full height
truncation. -/
theorem maximalRealPartZeroPackage_subset_nontrivialZerosFinset (T : ℝ) :
    maximalRealPartZeroPackage T ⊆ nontrivialZerosFinset T := by
  intro ρ hρ
  have hdata := mem_maximalRealPartZeroPackage.mp hρ
  exact mem_nontrivialZerosFinset.mpr ⟨hdata.1, hdata.2.1⟩

/-- In particular, the maximal package cannot contain more zeros than the
full height truncation. -/
theorem card_maximalRealPartZeroPackage_le_card_nontrivialZerosFinset (T : ℝ) :
    (maximalRealPartZeroPackage T).card ≤
      (nontrivialZerosFinset T).card :=
  Finset.card_le_card
    (maximalRealPartZeroPackage_subset_nontrivialZerosFinset T)

/-- The global zero-count estimate bounds the cardinality of every maximal
real-part package by `O(T log T)`. -/
theorem exists_card_maximalRealPartZeroPackage_le_mul_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      ((maximalRealPartZeroPackage T).card : ℝ) ≤
        C * T * (1 + Real.log (T + 6)) := by
  rcases ExplicitFormulaAux.exists_card_nontrivialZerosFinset_le_mul_log with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hcard :
      ((maximalRealPartZeroPackage T).card : ℝ) ≤
        ((nontrivialZerosFinset T).card : ℝ) := by
    exact_mod_cast
      card_maximalRealPartZeroPackage_le_card_nontrivialZerosFinset T
  exact hcard.trans (hbound T hT)

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

/-- After normalization by the maximal real-part growth, the fixed-height
complementary package is bounded by exponential decay at the exact positive
complementary gap. The remaining factor is the finite multiplicity-weighted
reciprocal-norm sum over the complementary package. -/
theorem
    normalized_norm_complementaryZeroPackageContribution_le_exp_neg_gap_mul_sum
    (T y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-(maximalZeroRealPart T) * y) *
        ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ≤
      Real.exp (-maximalComplementaryRealPartGap T * y) *
        ∑ ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T),
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
  calc
    Real.exp (-(maximalZeroRealPart T) * y) *
        ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ≤
      Real.exp (-(maximalZeroRealPart T) * y) *
        (Real.exp ((maximalZeroRealPart T -
            maximalComplementaryRealPartGap T) * y) *
          ∑ ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T),
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_complementaryZeroPackageContribution_le_exp_gap_mul_sum
          T (maximalZeroRealPart T) (maximalComplementaryRealPartGap T) y hy
            (fun _ hρ => re_le_maximalZeroRealPart_sub_gap hρ))
        (Real.exp_nonneg _)
    _ = Real.exp (-maximalComplementaryRealPartGap T * y) *
        ∑ ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T),
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
      have harg :
          -(maximalZeroRealPart T) * y +
              (maximalZeroRealPart T -
                maximalComplementaryRealPartGap T) * y =
            -maximalComplementaryRealPartGap T * y := by
        ring
      rw [← mul_assoc, ← Real.exp_add, harg]

/-- For every fixed truncation height `T`, the complementary zero package is
little compared with the maximal real-part scale as `y → +∞`. The proof uses
the strict positivity of the finite-height gap and the finite reciprocal-norm
sum retained in the preceding pointwise estimate. -/
theorem tendsto_normalized_norm_complementaryZeroPackageContribution_atTop
    (T : ℝ) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-(maximalZeroRealPart T) * y) *
          ‖complementaryZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖)
      Filter.atTop (nhds 0) := by
  have hlinear :
      Filter.Tendsto
        (fun y : ℝ => -maximalComplementaryRealPartGap T * y)
        Filter.atTop Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg
      (neg_lt_zero.mpr (maximalComplementaryRealPartGap_pos T))
      Filter.tendsto_id
  have hdecay :
      Filter.Tendsto
        (fun y : ℝ => Real.exp (-maximalComplementaryRealPartGap T * y))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlinear
  have hsum :
      Filter.Tendsto
        (fun _ : ℝ =>
          ∑ ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T),
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖)
        Filter.atTop
        (nhds (∑ ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T),
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖)) :=
    tendsto_const_nhds
  have hupper :
      Filter.Tendsto
        (fun y : ℝ =>
          Real.exp (-maximalComplementaryRealPartGap T * y) *
            ∑ ρ ∈ complementaryZeroPackage T (maximalZeroRealPart T),
              (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖)
        Filter.atTop (nhds 0) := by
    simpa using hdecay.mul hsum
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun y =>
      mul_nonneg (Real.exp_nonneg _)
        (norm_nonneg (complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)))) ?_ hupper
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
  exact
    normalized_norm_complementaryZeroPackageContribution_le_exp_neg_gap_mul_sum
      T y hy

/-- Moving-height sufficient condition for decay of the complementary package.
The truncation height `τ y` may vary arbitrarily. The only analytic input is
that, eventually, it lies in the range of the global reciprocal-multiplicity
bound. If the resulting explicit gap-times-`log^2` majorant tends to zero,
then the complementary package is negligible after normalization by the
moving maximal-real-part scale.

This theorem does not assert a uniform lower bound for the complementary gap
and does not prove that its majorant tends to zero for any particular choice
of `τ`. -/
theorem
    exists_C_tendsto_normalized_norm_complementaryZeroPackageContribution_along_moving_height_of_majorant
    (τ : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ((∀ᶠ y : ℝ in Filter.atTop, 0 ≤ y) →
        (∀ᶠ y : ℝ in Filter.atTop, 4 ≤ τ y) →
        Filter.Tendsto
          (fun y : ℝ =>
            Real.exp (-maximalComplementaryRealPartGap (τ y) * y) *
              (C * (1 + Real.log (τ y + 6)) ^ 2))
          Filter.atTop (nhds 0) →
        Filter.Tendsto
          (fun y : ℝ =>
            Real.exp (-(maximalZeroRealPart (τ y)) * y) *
              ‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖)
          Filter.atTop (nhds 0)) := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  intro hy hτ hmajorant
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun y =>
      mul_nonneg (Real.exp_nonneg _)
        (norm_nonneg
          (complementaryZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))))) ?_ hmajorant
  filter_upwards [hy, hτ] with y hy hτ
  calc
    Real.exp (-(maximalZeroRealPart (τ y)) * y) *
          ‖complementaryZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖ ≤
        Real.exp (-maximalComplementaryRealPartGap (τ y) * y) *
          ∑ ρ ∈ complementaryZeroPackage (τ y)
              (maximalZeroRealPart (τ y)),
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
      normalized_norm_complementaryZeroPackageContribution_le_exp_neg_gap_mul_sum
        (τ y) y hy
    _ ≤ Real.exp (-maximalComplementaryRealPartGap (τ y) * y) *
          ∑ ρ ∈ nontrivialZerosFinset (τ y),
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ :=
      mul_le_mul_of_nonneg_left
        (sum_complementary_multiplicity_div_norm_le_sum_nontrivialZerosFinset
          (τ y) (maximalZeroRealPart (τ y)))
        (Real.exp_nonneg _)
    _ ≤ Real.exp (-maximalComplementaryRealPartGap (τ y) * y) *
          (C * (1 + Real.log (τ y + 6)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa only [ExplicitFormulaAux.globalReciprocalZeroMultiplicity] using
        hCbound (τ y) hτ

/-- Exponential domination of the logarithmic-square factor. If

`gap(y) * y - 2 * log (1 + log (τ(y) + 6)) → +∞`,

then `exp (-gap(y) * y) * C * (1 + log (τ(y) + 6))^2 → 0`.
The eventual lower bound `τ(y) ≥ 4` is used only to make the logarithmic
factor strictly positive, so that the square can be represented exactly as
an exponential of twice its logarithm. No lower bound on `gap` is inferred
by this theorem. -/
theorem tendsto_gap_log_sq_majorant_of_margin_atTop
    (C : ℝ) (τ gap : ℝ → ℝ)
    (hτ : ∀ᶠ y : ℝ in Filter.atTop, 4 ≤ τ y)
    (hmargin :
      Filter.Tendsto
        (fun y : ℝ =>
          gap y * y - 2 * Real.log (1 + Real.log (τ y + 6)))
        Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-gap y * y) *
          (C * (1 + Real.log (τ y + 6)) ^ 2))
      Filter.atTop (nhds 0) := by
  have hdecay :
      Filter.Tendsto
        (fun y : ℝ =>
          Real.exp
            (-(gap y * y -
              2 * Real.log (1 + Real.log (τ y + 6)))))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hmargin
  have hscaled :
      Filter.Tendsto
        (fun y : ℝ =>
          C * Real.exp
            (-(gap y * y -
              2 * Real.log (1 + Real.log (τ y + 6)))))
        Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hdecay
  refine hscaled.congr' ?_
  filter_upwards [hτ] with y hy
  have hlog_pos : 0 < Real.log (τ y + 6) :=
    Real.log_pos (by linarith)
  have hbase_pos : 0 < 1 + Real.log (τ y + 6) := by
    linarith
  have hsq :
      (1 + Real.log (τ y + 6)) ^ 2 =
        Real.exp (2 * Real.log (1 + Real.log (τ y + 6))) := by
    symm
    calc
      Real.exp (2 * Real.log (1 + Real.log (τ y + 6))) =
          Real.exp
            (Real.log (1 + Real.log (τ y + 6)) +
              Real.log (1 + Real.log (τ y + 6))) := by
        congr 1
        ring
      _ = Real.exp (Real.log (1 + Real.log (τ y + 6))) *
          Real.exp (Real.log (1 + Real.log (τ y + 6))) := by
        rw [Real.exp_add]
      _ = (1 + Real.log (τ y + 6)) ^ 2 := by
        rw [Real.exp_log hbase_pos]
        ring
  rw [hsq]
  rw [show -(gap y * y -
        2 * Real.log (1 + Real.log (τ y + 6))) =
      -gap y * y + 2 * Real.log (1 + Real.log (τ y + 6)) by
    ring]
  rw [Real.exp_add]
  ring

/-- Concrete moving-height complementary-decay criterion. It replaces the
abstract hypothesis that the complete `exp(-gap * y) log^2` majorant tends to
zero by the checkable asymptotic condition

`maximalComplementaryRealPartGap (τ y) * y
    - 2 * log (1 + log (τ y + 6)) → +∞`.

The theorem preserves the exact analytic multiplicities in the underlying
zero-package estimate. It neither supplies the margin hypothesis for a
particular moving height nor asserts uniform zero spacing. -/
theorem
    exists_C_tendsto_normalized_norm_complementaryZeroPackageContribution_along_moving_height_of_gap_log_sq_margin_atTop
    (τ : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ((∀ᶠ y : ℝ in Filter.atTop, 0 ≤ y) →
        (∀ᶠ y : ℝ in Filter.atTop, 4 ≤ τ y) →
        Filter.Tendsto
          (fun y : ℝ =>
            maximalComplementaryRealPartGap (τ y) * y -
              2 * Real.log (1 + Real.log (τ y + 6)))
          Filter.atTop Filter.atTop →
        Filter.Tendsto
          (fun y : ℝ =>
            Real.exp (-(maximalZeroRealPart (τ y)) * y) *
              ‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖)
          Filter.atTop (nhds 0)) := by
  rcases
      exists_C_tendsto_normalized_norm_complementaryZeroPackageContribution_along_moving_height_of_majorant
        τ with
    ⟨C, hC, htransfer⟩
  refine ⟨C, hC, ?_⟩
  intro hy hτ hmargin
  exact htransfer hy hτ
    (tendsto_gap_log_sq_majorant_of_margin_atTop C τ
      (fun y => maximalComplementaryRealPartGap (τ y)) hτ hmargin)

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

/-- The bounded-gap part of the all-heights promotion has one constant for
every real sample `x > 1`. The dependence on `x` is exactly the displayed
linear factor. This extracts the witness from the global local-zero
multiplicity estimate instead of retaining the pointwise existential wrapper
in `ExplicitFormulaAllHeights`. -/
theorem
    exists_uniform_norm_explicitFormulaApproxWithMultiplicity_sub_le_log_div_of_le_add_three :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ {x : ℝ}, 1 < x →
      ∀ {T U : ℝ}, 4 ≤ T → T ≤ U → U ≤ T + 3 →
        ‖explicitFormulaApproxWithMultiplicity x T -
            explicitFormulaApproxWithMultiplicity x U‖ ≤
          2 * Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2) := by
  classical
  rcases ExplicitFormulaAux.exists_localZeroMultiplicity_le_log_bound with
    ⟨Cg, hCg, hmult⟩
  refine ⟨Cg, hCg, ?_⟩
  intro x hx T U hT hTU hUT
  have hlocal (A : ℝ) (hA : 4 ≤ A) :
      ExplicitFormulaAux.localZeroContributionNorm x A ≤
        Cg * x * (1 + Real.log (A + 6)) / (A - 1 / 2) := by
    let S : Finset ℂ :=
      (nontrivialZerosFinset (A + 2)).filter fun ρ : ℂ =>
        A - 1 / 4 ≤ |ρ.im| ∧ |ρ.im| ≤ A + 5 / 4
    have hden : 0 < A - 1 / 2 := by linarith
    have hpoint (ρ : ℂ) (hρ : ρ ∈ S) :
        ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
          (analyticOrderNatAt riemannZeta ρ : ℝ) * x /
            (A - 1 / 2) := by
      rcases Finset.mem_filter.mp hρ with ⟨hρtrunc, hlow, _hhigh⟩
      have hzero := (mem_nontrivialZerosFinset.mp hρtrunc).1
      apply norm_multiplicity_zero_contribution_le_div_height hx hden hzero
      linarith
    have hsum :
        ExplicitFormulaAux.localZeroContributionNorm x A ≤
          ∑ ρ ∈ S,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * x /
              (A - 1 / 2) := by
      dsimp [ExplicitFormulaAux.localZeroContributionNorm, S]
      exact Finset.sum_le_sum fun ρ hρ => hpoint ρ hρ
    have hrewrite :
        (∑ ρ ∈ S,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * x /
              (A - 1 / 2)) =
          x / (A - 1 / 2) *
            ExplicitFormulaAux.localZeroMultiplicity A := by
      dsimp [ExplicitFormulaAux.localZeroMultiplicity, S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _hρ
      ring
    rw [hrewrite] at hsum
    calc
      ExplicitFormulaAux.localZeroContributionNorm x A ≤
          x / (A - 1 / 2) *
            ExplicitFormulaAux.localZeroMultiplicity A := hsum
      _ ≤ x / (A - 1 / 2) *
          (Cg * (1 + Real.log (A + 6))) := by
        apply mul_le_mul_of_nonneg_left (hmult A hA)
        exact div_nonneg (zero_lt_one.trans hx).le hden.le
      _ = Cg * x * (1 + Real.log (A + 6)) /
          (A - 1 / 2) := by ring
  have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
  have hCgx : 0 ≤ Cg * x := mul_nonneg hCg hx0
  have hden : 0 < T - 1 / 2 := by linarith
  have hnum : 0 ≤ Cg * x * (1 + Real.log (T + 8)) := by
    have hlog : 0 ≤ Real.log (T + 8) :=
      Real.log_nonneg (by linarith)
    positivity
  have hwindow1 := hlocal (T + 1 / 4) (by linarith)
  have hwindow2 := hlocal (T + 7 / 4) (by linarith)
  have hlog1 :
      Real.log ((T + 1 / 4) + 6) ≤ Real.log (T + 8) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2 :
      Real.log ((T + 7 / 4) + 6) ≤ Real.log (T + 8) :=
    Real.log_le_log (by linarith) (by linarith)
  have hterm1 :
      ExplicitFormulaAux.localZeroContributionNorm x (T + 1 / 4) ≤
        Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2) := by
    apply hwindow1.trans
    calc
      Cg * x * (1 + Real.log ((T + 1 / 4) + 6)) /
            ((T + 1 / 4) - 1 / 2) ≤
          Cg * x * (1 + Real.log (T + 8)) /
            ((T + 1 / 4) - 1 / 2) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left (by linarith) hCgx
      _ ≤ Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2) :=
        div_le_div_of_nonneg_left hnum hden (by linarith)
  have hterm2 :
      ExplicitFormulaAux.localZeroContributionNorm x (T + 7 / 4) ≤
        Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2) := by
    apply hwindow2.trans
    calc
      Cg * x * (1 + Real.log ((T + 7 / 4) + 6)) /
            ((T + 7 / 4) - 1 / 2) ≤
          Cg * x * (1 + Real.log (T + 8)) /
            ((T + 7 / 4) - 1 / 2) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left (by linarith) hCgx
      _ ≤ Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2) :=
        div_le_div_of_nonneg_left hnum hden (by linarith)
  calc
    ‖explicitFormulaApproxWithMultiplicity x T -
        explicitFormulaApproxWithMultiplicity x U‖ ≤
      ExplicitFormulaAux.localZeroContributionNorm x (T + 1 / 4) +
        ExplicitFormulaAux.localZeroContributionNorm x (T + 7 / 4) :=
      ExplicitFormulaResidues.norm_explicitFormulaApproxWithMultiplicity_sub_le_two_localWindows
        hTU hUT
    _ ≤ Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2) +
        Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2) :=
      add_le_add hterm1 hterm2
    _ = 2 * Cg * x * (1 + Real.log (T + 8)) /
        (T - 1 / 2) := by ring

/-- The exact residual certificate left by first-order Perron inversion on
the fixed line `Re(s) = 2`.  The contour part of the selected-height explicit
formula is uniform for `x ≥ 2`; this is the only pointwise input that remains
after that uniform contour estimate is used. -/
structure PerronResidualCertificate (x Cp : ℝ) : Prop where
  nonneg : 0 ≤ Cp
  bound :
    ∀ W : ℝ, 1 ≤ W →
      ‖(∫ w : ℝ in (-W)..W,
          (x : ℂ) ^ perronLine 2 w *
            (-deriv riemannZeta (perronLine 2 w) /
              riemannZeta (perronLine 2 w)) /
                perronLine 2 w) -
          (chebyshevPsi0 x : ℂ)‖ ≤ Cp / W

/-- The upper integral sample associated with the logarithmic coordinate `y`.
At this sample the fixed-line Perron residual has a polynomially uniform
bound, including the half-weight at a von Mangoldt jump. -/
def upperNaturalLogSampleNat (y : ℝ) : ℕ :=
  Nat.ceil (Real.exp y)

/-- Logarithmic coordinate of `upperNaturalLogSampleNat`. -/
def upperNaturalLogSample (y : ℝ) : ℝ :=
  Real.log (upperNaturalLogSampleNat y : ℝ)

/-- Upper natural logarithmic sampling moves `y` to the right by less than
`exp (-y)`. In particular its mesh tends to zero on translated detector
intervals. -/
theorem upperNaturalLogSample_mem_short_interval (y : ℝ) :
    y ≤ upperNaturalLogSample y ∧
      upperNaturalLogSample y - y < Real.exp (-y) := by
  let m : ℕ := upperNaturalLogSampleNat y
  have hexp : 0 < Real.exp y := Real.exp_pos y
  have hmposNat : 0 < m := by
    dsimp [m, upperNaturalLogSampleNat]
    exact Nat.ceil_pos.mpr hexp
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmposNat
  have hceil : Real.exp y ≤ (m : ℝ) := by
    dsimp [m, upperNaturalLogSampleNat]
    exact Nat.le_ceil _
  have hceilLt : (m : ℝ) < Real.exp y + 1 := by
    dsimp [m, upperNaturalLogSampleNat]
    exact Nat.ceil_lt_add_one (Real.exp_nonneg y)
  have hleft : y ≤ Real.log (m : ℝ) := by
    rw [← Real.log_exp y]
    exact Real.log_le_log hexp hceil
  have hratioPos : 0 < (m : ℝ) / Real.exp y := div_pos hmpos hexp
  have hratioLt :
      (m : ℝ) / Real.exp y < 1 + Real.exp (-y) := by
    rw [Real.exp_neg]
    apply (div_lt_iff₀ hexp).2
    field_simp [hexp.ne']
    linarith
  have hlogRatio :
      Real.log ((m : ℝ) / Real.exp y) ≤
        (m : ℝ) / Real.exp y - 1 :=
    Real.log_le_sub_one_of_pos hratioPos
  have hright :
      Real.log (m : ℝ) - y < Real.exp (-y) := by
    have hlogEq :
        Real.log (m : ℝ) - y =
          Real.log ((m : ℝ) / Real.exp y) := by
      rw [Real.log_div hmpos.ne' hexp.ne', Real.log_exp]
    rw [hlogEq]
    linarith
  simpa [upperNaturalLogSample, m] using And.intro hleft hright

theorem exp_upperNaturalLogSample (y : ℝ) :
    Real.exp (upperNaturalLogSample y) =
      (upperNaturalLogSampleNat y : ℝ) := by
  apply Real.exp_log
  exact_mod_cast
    (Nat.ceil_pos.mpr (Real.exp_pos y) :
      0 < upperNaturalLogSampleNat y)

theorem two_le_upperNaturalLogSampleNat {y : ℝ}
    (hy : Real.log 2 ≤ y) :
    2 ≤ upperNaturalLogSampleNat y := by
  have htwo : (2 : ℝ) ≤ Real.exp y := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) :=
        (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp y := Real.exp_le_exp.mpr hy
  have hceil :
      Real.exp y ≤ (upperNaturalLogSampleNat y : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast htwo.trans hceil

theorem tendsto_upperNaturalLogSample_atTop :
    Filter.Tendsto upperNaturalLogSample Filter.atTop Filter.atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [Filter.eventually_ge_atTop b] with y hy
  exact hy.trans (upperNaturalLogSample_mem_short_interval y).1

/-- Frequency-weighted coefficient budget for perturbing the normalized
maximal zero package in logarithmic coordinates. -/
def maximalZeroPackageFrequencyBudget (T : ℝ) : ℝ :=
  ∑ ρ ∈ maximalRealPartZeroPackage T,
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹‖ * |ρ.im|

theorem maximalZeroPackageFrequencyBudget_nonneg (T : ℝ) :
    0 ≤ maximalZeroPackageFrequencyBudget T := by
  unfold maximalZeroPackageFrequencyBudget
  positivity

private lemma norm_cexp_frequency_sub_le
    (c : ℂ) (ω u v : ℝ) :
    ‖c * Complex.exp (I * (ω * u)) -
        c * Complex.exp (I * (ω * v))‖ ≤
      ‖c‖ * |ω| * |u - v| := by
  have hfactor :
      Complex.exp (I * (ω * u)) - Complex.exp (I * (ω * v)) =
        Complex.exp (I * (ω * v)) *
          (Complex.exp (I * (ω * (u - v))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    ring
  rw [← mul_sub, hfactor, norm_mul, norm_mul]
  have hunit :
      ‖Complex.exp (I * (ω * v))‖ = 1 := by
    simpa using Complex.norm_exp_I_mul_ofReal (ω * v)
  rw [hunit]
  calc
    ‖c‖ * (1 * ‖Complex.exp (I * (ω * (u - v))) - 1‖) ≤
        ‖c‖ * (1 * ‖ω * (u - v)‖) := by
      gcongr
      simpa only [Complex.ofReal_mul, Complex.ofReal_sub] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := ω * (u - v)))
    _ = ‖c‖ * |ω| * |u - v| := by
      rw [Real.norm_eq_abs, abs_mul]
      ring

private lemma norm_multiplicityWeightedExponentialPolynomial_sub_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (multiplicity : ι → ℕ) (c : ι → ℂ) (ω : ι → ℝ) (u v : ℝ) :
    ‖multiplicityWeightedExponentialPolynomial S multiplicity c ω u -
        multiplicityWeightedExponentialPolynomial S multiplicity c ω v‖ ≤
      (∑ i ∈ S, ‖(multiplicity i : ℂ) * c i‖ * |ω i|) * |u - v| := by
  classical
  simp only [multiplicityWeightedExponentialPolynomial, exponentialPolynomial,
    ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ S,
        ((multiplicity i : ℂ) * c i * Complex.exp (I * (ω i * u)) -
          (multiplicity i : ℂ) * c i * Complex.exp (I * (ω i * v)))‖ ≤
        ∑ i ∈ S,
          ‖(multiplicity i : ℂ) * c i * Complex.exp (I * (ω i * u)) -
            (multiplicity i : ℂ) * c i * Complex.exp (I * (ω i * v))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S,
          (‖(multiplicity i : ℂ) * c i‖ * |ω i|) * |u - v| := by
      exact Finset.sum_le_sum fun i _hi =>
        norm_cexp_frequency_sub_le
          ((multiplicity i : ℂ) * c i) (ω i) u v
    _ = (∑ i ∈ S, ‖(multiplicity i : ℂ) * c i‖ * |ω i|) *
          |u - v| := by
      rw [Finset.sum_mul]

/-- After removing the common real-part growth, the maximal package is
globally Lipschitz in `y`, with an explicit finite frequency budget. -/
theorem abs_normalized_maximalZeroPackageContribution_sub_le
    (T u v : ℝ) :
    |Real.exp (-maximalZeroRealPart T * u) *
          ‖equalRealPartZeroPackageContribution (Real.exp u) T
            (maximalZeroRealPart T)‖ -
        Real.exp (-maximalZeroRealPart T * v) *
          ‖equalRealPartZeroPackageContribution (Real.exp v) T
            (maximalZeroRealPart T)‖| ≤
      maximalZeroPackageFrequencyBudget T * |u - v| := by
  let P : ℝ → ℂ := fun y =>
    multiplicityWeightedExponentialPolynomial
      (maximalRealPartZeroPackage T)
      (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y
  have hnormalized (y : ℝ) :
      Real.exp (-maximalZeroRealPart T * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ = ‖P y‖ := by
    rw [equalRealPartZeroPackageContribution_exp_eq_exponentialPolynomial,
      norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    change Real.exp (-maximalZeroRealPart T * y) *
        (Real.exp (maximalZeroRealPart T * y) * ‖P y‖) = ‖P y‖
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  rw [hnormalized u, hnormalized v]
  calc
    |‖P u‖ - ‖P v‖| ≤ ‖P u - P v‖ := abs_norm_sub_norm_le _ _
    _ ≤ maximalZeroPackageFrequencyBudget T * |u - v| := by
      simpa [P, maximalZeroPackageFrequencyBudget, maximalRealPartZeroPackage] using
        norm_multiplicityWeightedExponentialPolynomial_sub_le
          (maximalRealPartZeroPackage T)
          (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im u v

/-- Every positive sample has a Perron residual certificate.  This theorem
names the actual pointwise obstruction instead of folding it into the full
selected-height constant. -/
theorem exists_perronResidualCertificate {x : ℝ} (hx : 0 < x) :
    ∃ Cp : ℝ, PerronResidualCertificate x Cp := by
  rcases
      exists_norm_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le_div
        hx (by norm_num : (1 : ℝ) < 2) with
    ⟨Cp, hCp, hbound⟩
  exact ⟨Cp, ⟨hCp, hbound⟩⟩

/-- The first-order Perron residual is polynomially uniform on all positive
integral samples. This is an actual certificate family, not a pointwise
choice of constants. -/
theorem exists_uniform_nat_perronResidualCertificate :
    ∃ Cp0 : ℝ, 0 ≤ Cp0 ∧ ∀ m : ℕ, 2 ≤ m →
      PerronResidualCertificate (m : ℝ) (Cp0 * (m : ℝ) ^ 5) := by
  rcases
      exists_uniform_nat_norm_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le
    with ⟨Cp0, hCp0, hbound⟩
  refine ⟨Cp0, hCp0, ?_⟩
  intro m hm
  exact
    ⟨mul_nonneg hCp0 (pow_nonneg (Nat.cast_nonneg m) 5),
      fun W hW => hbound m W hm hW⟩

private theorem
    exists_uniform_nat_perronResidualCertificate_and_eventually_visible_of
    (T L amp : ℝ) (hamp : 0 < amp)
    (hvisibleInterval :
      ∀ a : ℝ, ∃ y ∈ Set.Ioo a (a + L),
        amp ≤
          Real.exp (-maximalZeroRealPart T * y) *
            ‖equalRealPartZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖) :
    ∃ Cp0 A : ℝ, 0 ≤ Cp0 ∧ ∀ a : ℝ, A ≤ a →
      ∃ m : ℕ, 2 ≤ m ∧
        Real.log (m : ℝ) ∈ Set.Ioo a (a + L + 1) ∧
        PerronResidualCertificate (m : ℝ) (Cp0 * (m : ℝ) ^ 5) ∧
        amp / 2 ≤
          Real.exp (-maximalZeroRealPart T * Real.log (m : ℝ)) *
            ‖equalRealPartZeroPackageContribution (m : ℝ) T
              (maximalZeroRealPart T)‖ := by
  rcases exists_uniform_nat_perronResidualCertificate with
    ⟨Cp0, hCp0, hcertificate⟩
  let B : ℝ := maximalZeroPackageFrequencyBudget T
  have hB : 0 ≤ B := by
    dsimp [B]
    exact maximalZeroPackageFrequencyBudget_nonneg T
  have htend :
      Filter.Tendsto (fun a : ℝ => B * Real.exp (-a))
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero :
        Filter.Tendsto (fun a : ℝ => B * Real.exp (-a))
          Filter.atTop (nhds (B * 0)))
  have hsmall :
      ∀ᶠ a : ℝ in Filter.atTop, B * Real.exp (-a) < amp / 2 :=
    (tendsto_order.1 htend).2 (amp / 2) (by linarith)
  have hbase :
      ∀ᶠ a : ℝ in Filter.atTop, Real.log 2 ≤ a :=
    Filter.eventually_ge_atTop (Real.log 2)
  rcases eventually_atTop.1 (hsmall.and hbase) with ⟨A, hA⟩
  refine ⟨Cp0, A, hCp0, ?_⟩
  intro a ha
  have haData := hA a ha
  have ha0 : 0 ≤ a := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [haData.2]
  rcases hvisibleInterval a with
    ⟨y, hy, hvisible⟩
  let m : ℕ := upperNaturalLogSampleNat y
  have hy0 : 0 ≤ y := le_trans ha0 hy.1.le
  have hsample := upperNaturalLogSample_mem_short_interval y
  have hmposNat : 0 < m := by
    dsimp [m, upperNaturalLogSampleNat]
    exact Nat.ceil_pos.mpr (Real.exp_pos y)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmposNat
  have hsampleEq :
      upperNaturalLogSample y = Real.log (m : ℝ) := by
    rfl
  have hmTwo : 2 ≤ m := by
    have htwoLtExp : (2 : ℝ) < Real.exp y := by
      calc
        (2 : ℝ) = Real.exp (Real.log 2) :=
          (Real.exp_log (by norm_num)).symm
        _ < Real.exp y := Real.exp_lt_exp.mpr (lt_of_le_of_lt haData.2 hy.1)
    have htwoLeCast : (2 : ℝ) ≤ (m : ℝ) := by
      have hexpLe : Real.exp y ≤ (m : ℝ) := by
        dsimp [m, upperNaturalLogSampleNat]
        exact Nat.le_ceil _
      exact htwoLtExp.le.trans hexpLe
    exact_mod_cast htwoLeCast
  have hsampleMem :
      Real.log (m : ℝ) ∈ Set.Ioo a (a + L + 1) := by
    constructor
    · rw [← hsampleEq]
      exact lt_of_lt_of_le hy.1 hsample.1
    · rw [← hsampleEq]
      have hexpNegLe : Real.exp (-y) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (neg_nonpos.mpr hy0)
      linarith [hy.2, hsample.2]
  have hshiftAbs :
      |upperNaturalLogSample y - y| <
        Real.exp (-y) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hsample.1)]
    exact hsample.2
  have hexpMono : Real.exp (-y) ≤ Real.exp (-a) :=
    Real.exp_le_exp.mpr (by linarith [hy.1])
  have hperturb :
      |Real.exp (-maximalZeroRealPart T * upperNaturalLogSample y) *
            ‖equalRealPartZeroPackageContribution
                (Real.exp (upperNaturalLogSample y)) T
              (maximalZeroRealPart T)‖ -
          Real.exp (-maximalZeroRealPart T * y) *
            ‖equalRealPartZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖| <
        amp / 2 := by
    calc
      _ ≤ B * |upperNaturalLogSample y - y| := by
        simpa [B] using
          abs_normalized_maximalZeroPackageContribution_sub_le
            T (upperNaturalLogSample y) y
      _ ≤ B * Real.exp (-y) :=
        mul_le_mul_of_nonneg_left hshiftAbs.le hB
      _ ≤ B * Real.exp (-a) :=
        mul_le_mul_of_nonneg_left hexpMono hB
      _ < amp / 2 := haData.1
  have hexpSample :
      Real.exp (upperNaturalLogSample y) = (m : ℝ) := by
    rw [hsampleEq, Real.exp_log hmpos]
  have hsampleVisible :
      amp / 2 ≤
        Real.exp (-maximalZeroRealPart T * upperNaturalLogSample y) *
          ‖equalRealPartZeroPackageContribution
              (Real.exp (upperNaturalLogSample y)) T
            (maximalZeroRealPart T)‖ := by
    have habsLower :
        Real.exp (-maximalZeroRealPart T * y) *
              ‖equalRealPartZeroPackageContribution (Real.exp y) T
                (maximalZeroRealPart T)‖ -
            Real.exp (-maximalZeroRealPart T * upperNaturalLogSample y) *
              ‖equalRealPartZeroPackageContribution
                  (Real.exp (upperNaturalLogSample y)) T
                (maximalZeroRealPart T)‖ ≤
          |Real.exp (-maximalZeroRealPart T * upperNaturalLogSample y) *
                ‖equalRealPartZeroPackageContribution
                    (Real.exp (upperNaturalLogSample y)) T
                  (maximalZeroRealPart T)‖ -
              Real.exp (-maximalZeroRealPart T * y) *
                ‖equalRealPartZeroPackageContribution (Real.exp y) T
                  (maximalZeroRealPart T)‖| := by
      simpa only [abs_sub_comm] using
        le_abs_self
          (Real.exp (-maximalZeroRealPart T * y) *
              ‖equalRealPartZeroPackageContribution (Real.exp y) T
                (maximalZeroRealPart T)‖ -
            Real.exp (-maximalZeroRealPart T * upperNaturalLogSample y) *
              ‖equalRealPartZeroPackageContribution
                  (Real.exp (upperNaturalLogSample y)) T
                (maximalZeroRealPart T)‖)
    linarith
  refine ⟨m, hmTwo, hsampleMem, hcertificate m hmTwo, ?_⟩
  rw [← hsampleEq, ← hexpSample]
  exact hsampleVisible

/-- A uniform selected horizontal estimate plus a Perron residual controls the
finite explicit formula before the moving-left and trivial-zero limits are
taken.  All sample dependence outside `Cp` is the displayed `x²`. -/
theorem
    norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_of_uniform_horizontal_of_perronResidual
    {x A T Ch Cp : ℝ} {N : ℕ}
    (hx : 2 ≤ x) (hA : 8 ≤ A) (hTmem : T ∈ Set.Icc A (A + 1))
    (hgood : ExplicitFormulaAux.goodHeight T) (hCh : 0 ≤ Ch)
    (hhorizontal :
      ∀ {a : ℝ}, a ≤ -1 →
        ‖(∫ σ : ℝ in a..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))) -
            (∫ σ : ℝ in a..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * T))‖ ≤
          Ch * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T)
    (hCp : PerronResidualCertificate x Cp) :
    ‖(∑ p ∈ ExplicitFormulaAux.finiteTrivialZeroSum (2 * (N : ℝ)),
          -((x : ℂ) ^ p) / p) +
        ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
          ∑ ρ ∈ nontrivialZerosFinset T,
            -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
        (chebyshevPsi0 x : ℂ)‖ ≤
      (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp) *
          (1 + Real.log (A + 6)) ^ 2 / T +
        (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
          x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
          (2 * Real.pi) := by
  let a : ℝ := -(2 * (N : ℝ) + 1)
  let L : ℝ := 1 + Real.log (A + 6)
  let approx : ℂ :=
    (∑ p ∈ ExplicitFormulaAux.finiteTrivialZeroSum (2 * (N : ℝ)),
        -((x : ℂ) ^ p) / p) +
      ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
        ∑ ρ ∈ nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)
  let rem : ℂ := firstOrderContourRemainder x a 2
    (T / (2 * Real.pi))
  let left : ℝ :=
    ((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
      x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)
  have hxpos : 0 < x := by linarith
  have ha : a ≤ -1 := by
    dsimp [a]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hTpos : 0 < T := by linarith [hTmem.1]
  have htwoPi : 2 * Real.pi ≤ T := by
    nlinarith [Real.pi_lt_four, hTmem.1]
  have hW : 1 ≤ T / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
    simpa using htwoPi
  have hWpos : 0 < T / (2 * Real.pi) := zero_lt_one.trans_le hW
  have hscale : 2 * Real.pi * (T / (2 * Real.pi)) = T := by
    field_simp
  have hgoodW : ExplicitFormulaAux.goodHeight
      (2 * Real.pi * (T / (2 * Real.pi))) := by
    simpa [hscale] using hgood
  have hidentity :=
    ExplicitFormulaResidues.movingLeft_scaledRightIntegral_eq_truncatedExplicitFormula
      (x := x) (c := 2) (W := T / (2 * Real.pi)) N
      hxpos (by norm_num) hWpos hgoodW
  have hintegral :
      (∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
          explicitFormulaIntegrand x ((2 : ℂ) + 2 * Real.pi * w * I)) =
        ∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
          (x : ℂ) ^ perronLine 2 w *
            (-deriv riemannZeta (perronLine 2 w) /
              riemannZeta (perronLine 2 w)) /
                perronLine 2 w := by
    apply intervalIntegral.integral_congr
    intro w _hw
    change explicitFormulaIntegrand x
        ((2 : ℂ) + 2 * Real.pi * w * I) =
      (x : ℂ) ^ perronLine 2 w *
        (-deriv riemannZeta (perronLine 2 w) /
          riemannZeta (perronLine 2 w)) /
            perronLine 2 w
    have hs : (2 : ℂ) + 2 * Real.pi * w * I = perronLine 2 w := by
      simp only [perronLine]
      push_cast
      ring
    rw [hs]
    simp only [explicitFormulaIntegrand, perronLine, logDeriv_apply]
    ring
  have hrightEq :
      (∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
          (x : ℂ) ^ perronLine 2 w *
            (-deriv riemannZeta (perronLine 2 w) /
              riemannZeta (perronLine 2 w)) /
                perronLine 2 w) = approx - rem := by
    calc
      _ = ∫ w : ℝ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
          explicitFormulaIntegrand x ((2 : ℂ) + 2 * Real.pi * w * I) :=
        hintegral.symm
      _ = (∑ p ∈ ExplicitFormulaAux.finiteTrivialZeroSum (2 * (N : ℝ)),
          -((x : ℂ) ^ p) / p) +
          ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
            ∑ ρ ∈ nontrivialZerosFinset
                (2 * Real.pi * (T / (2 * Real.pi))),
              -(analyticOrderNatAt riemannZeta ρ : ℂ) *
                (x : ℂ) ^ ρ / ρ) -
          firstOrderContourRemainder x a 2
            (T / (2 * Real.pi)) := hidentity
      _ = approx - rem := by simp [approx, rem, a, hscale]
  have hpBound :
      ‖(approx - rem) - (chebyshevPsi0 x : ℂ)‖ ≤
        Cp / (T / (2 * Real.pi)) := by
    rw [← hrightEq]
    exact hCp.bound _ hW
  have hleftIntegral :=
    (ExplicitFormulaResidues.norm_integral_explicitFormulaIntegrand_odd_vertical_le
      (N := N) (by linarith : 1 < x) hTpos.le).2
  have hhorizontal' :
      ‖(∫ σ : ℝ in a..2,
            explicitFormulaIntegrand x
              ((σ : ℂ) + (((-T : ℝ) : ℂ) * I))) -
        (∫ σ : ℝ in a..2,
            explicitFormulaIntegrand x
              ((σ : ℂ) + (((T : ℝ) : ℂ) * I)))‖ ≤
        Ch * x ^ (2 : ℝ) * L ^ 2 / T := by
    simpa [L, mul_comm] using hhorizontal ha
  have hden : ‖(2 * Real.pi : ℂ) * I‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hrem :
      ‖rem‖ ≤ Ch * x ^ (2 : ℝ) * L ^ 2 / T +
          left / (2 * Real.pi) := by
    have hraw :
        ‖rem‖ ≤
          (Ch * x ^ (2 : ℝ) * L ^ 2 / T + left) /
            (2 * Real.pi) := by
      change ‖firstOrderContourRemainder x a 2
          (T / (2 * Real.pi))‖ ≤ _
      rw [firstOrderContourRemainder, hscale, norm_div, hden]
      apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * Real.pi)
      calc
        ‖(∫ σ : ℝ in a..2,
              explicitFormulaIntegrand x
                ((σ : ℂ) + (((-T : ℝ) : ℂ) * I))) -
            (∫ σ : ℝ in a..2,
              explicitFormulaIntegrand x
                ((σ : ℂ) + (((T : ℝ) : ℂ) * I))) -
            I * (∫ t : ℝ in (-T)..T,
              explicitFormulaIntegrand x ((a : ℂ) + t * I))‖ ≤
          ‖(∫ σ : ℝ in a..2,
              explicitFormulaIntegrand x
                ((σ : ℂ) + (((-T : ℝ) : ℂ) * I))) -
            (∫ σ : ℝ in a..2,
              explicitFormulaIntegrand x
                ((σ : ℂ) + (((T : ℝ) : ℂ) * I)))‖ +
            ‖∫ t : ℝ in (-T)..T,
              explicitFormulaIntegrand x ((a : ℂ) + t * I)‖ := by
                calc
                  _ ≤ ‖(∫ σ : ℝ in a..2,
                        explicitFormulaIntegrand x
                          ((σ : ℂ) + (((-T : ℝ) : ℂ) * I))) -
                      (∫ σ : ℝ in a..2,
                        explicitFormulaIntegrand x
                          ((σ : ℂ) + (((T : ℝ) : ℂ) * I)))‖ +
                      ‖I * (∫ t : ℝ in (-T)..T,
                        explicitFormulaIntegrand x
                          ((a : ℂ) + t * I))‖ :=
                    norm_sub_le _ _
                  _ = _ := by rw [norm_mul, norm_I, one_mul]
        _ ≤ Ch * x ^ (2 : ℝ) * L ^ 2 / T + left := by
          apply add_le_add hhorizontal'
          simpa [a, left] using hleftIntegral
    apply hraw.trans
    rw [add_div]
    have hhoriz : 0 ≤ Ch * x ^ (2 : ℝ) * L ^ 2 / T := by positivity
    have hfirst := div_le_self hhoriz
      (by nlinarith [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
    linarith
  change ‖approx - (chebyshevPsi0 x : ℂ)‖ ≤ _
  have hsplit :
      approx - (chebyshevPsi0 x : ℂ) =
        ((approx - rem) - (chebyshevPsi0 x : ℂ)) + rem := by ring
  rw [hsplit]
  calc
    _ ≤ ‖(approx - rem) - (chebyshevPsi0 x : ℂ)‖ + ‖rem‖ :=
      norm_add_le _ _
    _ ≤ Cp / (T / (2 * Real.pi)) +
        (Ch * x ^ (2 : ℝ) * L ^ 2 / T +
          left / (2 * Real.pi)) :=
      add_le_add hpBound hrem
    _ ≤ (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp) * L ^ 2 / T +
        left / (2 * Real.pi) := by
      have hlog : 0 ≤ Real.log (A + 6) :=
        Real.log_nonneg (by linarith)
      have hLsq : 1 ≤ L ^ 2 := by
        have hL : 1 ≤ L := by dsimp [L]; linarith
        nlinarith [sq_nonneg (L - 1)]
      have hpRate : Cp / (T / (2 * Real.pi)) ≤
          (2 * Real.pi * Cp) * L ^ 2 / T := by
        have heq :
            Cp / (T / (2 * Real.pi)) = (2 * Real.pi * Cp) / T := by
          field_simp [hTpos.ne']
        rw [heq]
        apply div_le_div_of_nonneg_right _ hTpos.le
        nlinarith [mul_nonneg
          (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) hCp.nonneg)
          (sub_nonneg.mpr hLsq)]
      calc
        Cp / (T / (2 * Real.pi)) +
            (Ch * x ^ (2 : ℝ) * L ^ 2 / T +
              left / (2 * Real.pi)) ≤
          (2 * Real.pi * Cp) * L ^ 2 / T +
            (Ch * x ^ (2 : ℝ) * L ^ 2 / T +
              left / (2 * Real.pi)) := by
                exact add_le_add hpRate le_rfl
        _ = (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp) *
              L ^ 2 / T + left / (2 * Real.pi) := by ring
    _ = (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp) *
          (1 + Real.log (A + 6)) ^ 2 / T +
        (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
          x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
          (2 * Real.pi) := by rfl

/-- The selected-height constant is an explicit quadratic contour term plus
the first-order Perron residual.  The constants used to remove the moving-left
edge and the finite trivial-zero truncation are the final displayed `+ 2`.

This is the strongest uniform split available from the current hard Perron
kernel: the contour coefficient `Ch` is independent of `x`, while `Cp`
retains exactly the pointwise Perron inversion sensitivity. -/
theorem
    exists_uniform_contour_constant_selectedHeight_of_perronResidual :
    ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ {x : ℝ}, 2 ≤ x →
      ∀ {Cp : ℝ}, PerronResidualCertificate x Cp →
        ∀ A : ℝ, 8 ≤ A →
          ∃ T ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight T ∧
            ‖explicitFormulaApproxWithMultiplicity x T -
                (chebyshevPsi0 x : ℂ)‖ ≤
              (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp + 2) *
                (1 + Real.log (A + 6)) ^ 2 / T := by
  rcases
      ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_horizontal_complete_explicitFormulaContour_difference_le
    with ⟨Ch, hCh, hhorizontal⟩
  refine ⟨Ch, hCh, ?_⟩
  intro x hx Cp hCp
  intro A hA
  rcases hhorizontal A (by linarith) with
    ⟨T, hTmem, hgood, hhorizontalT⟩
  have hTpos : 0 < T := by linarith [hTmem.1]
  let L : ℝ := 1 + Real.log (A + 6)
  have hlog : 0 ≤ Real.log (A + 6) :=
    Real.log_nonneg (by linarith)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have heps : 0 < L ^ 2 / T := div_pos (sq_pos_of_pos hLpos) hTpos
  have hleft :=
    ExplicitFormulaResidues.tendsto_oddVerticalExplicitBound_atTop
      (by linarith : 1 < x) hTpos.le
  rcases (Metric.tendsto_atTop.mp hleft) (L ^ 2 / T) heps with
    ⟨Nleft, hNleft⟩
  have htrivial :=
    ExplicitFormulaAux.tendsto_finiteTrivialZeroSum_residues
      (by linarith : 1 < x)
  rcases (Metric.tendsto_atTop.mp htrivial) (L ^ 2 / T) heps with
    ⟨Ntrivial, hNtrivial⟩
  let N : ℕ := max Nleft Ntrivial
  let finite : ℂ :=
    ∑ p ∈ ExplicitFormulaAux.finiteTrivialZeroSum (2 * (N : ℝ)),
      -((x : ℂ) ^ p) / p
  let zeroSum : ℂ :=
    ∑ ρ ∈ nontrivialZerosFinset T,
      -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  let mainTerm : ℂ :=
    (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 + zeroSum
  let logTerm : ℂ :=
    ((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)
  let left : ℝ :=
    (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
      x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
      (2 * Real.pi)
  have hleftDist := hNleft N (le_max_left _ _)
  have hleftNonneg : 0 ≤ left := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hlogN : 0 ≤ Real.log (2 * (N : ℝ) + T + 4) :=
      Real.log_nonneg (by
        have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith)
    dsimp [left]
    positivity
  have hleftRate : left ≤ L ^ 2 / T := by
    change dist left 0 < L ^ 2 / T at hleftDist
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hleftNonneg] at hleftDist
    exact hleftDist.le
  have htrivialDist := hNtrivial N (le_max_right _ _)
  have htrivialRate : ‖logTerm - finite‖ ≤ L ^ 2 / T := by
    have hforward : ‖finite - logTerm‖ < L ^ 2 / T := by
      change dist finite logTerm < L ^ 2 / T at htrivialDist
      simpa [dist_eq_norm] using htrivialDist
    rw [norm_sub_rev]
    exact hforward.le
  have hfinite :
      ‖finite + mainTerm - (chebyshevPsi0 x : ℂ)‖ ≤
        (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp) * L ^ 2 / T +
          left := by
    simpa [finite, mainTerm, zeroSum, left, L] using
      norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_of_uniform_horizontal_of_perronResidual
        hx hA hTmem hgood hCh (hhorizontalT hx) hCp (N := N)
  have hzeroSum :
      zeroSum = -finiteNontrivialZeroSumWithMultiplicity x T := by
    dsimp [zeroSum, finiteNontrivialZeroSumWithMultiplicity]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ _hρ
    ring
  have happ :
      explicitFormulaApproxWithMultiplicity x T = mainTerm + logTerm := by
    dsimp [explicitFormulaApproxWithMultiplicity, mainTerm, logTerm]
    rw [hzeroSum]
    push_cast
    ring
  refine ⟨T, hTmem, hgood, ?_⟩
  have hsplit :
      explicitFormulaApproxWithMultiplicity x T -
          (chebyshevPsi0 x : ℂ) =
        (finite + mainTerm - (chebyshevPsi0 x : ℂ)) +
          (logTerm - finite) := by
    rw [happ]
    ring
  rw [hsplit]
  calc
    _ ≤ ‖finite + mainTerm - (chebyshevPsi0 x : ℂ)‖ +
        ‖logTerm - finite‖ := norm_add_le _ _
    _ ≤ ((Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp) * L ^ 2 / T +
          left) + L ^ 2 / T :=
      add_le_add hfinite htrivialRate
    _ ≤ ((Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp) * L ^ 2 / T +
          L ^ 2 / T) + L ^ 2 / T := by
      gcongr
    _ = (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp + 2) *
          (1 + Real.log (A + 6)) ^ 2 / T := by
      dsimp [L]
      ring

/-- Exact structural assembly behind the pointwise all-heights constant.
Given a selected-height constant `Cs` and a bounded-gap constant `Cg`, the
all-heights certificate uses `K(x) = Cs + 4 * Cg * x`. -/
theorem norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_structural_allHeights
    {x Cs Cg : ℝ} (hx : 1 < x) (hCs : 0 ≤ Cs) (hCg : 0 ≤ Cg)
    (hselected :
      ∀ A : ℝ, 8 ≤ A →
        ∃ U ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight U ∧
          ‖explicitFormulaApproxWithMultiplicity x U -
              (chebyshevPsi0 x : ℂ)‖ ≤
            Cs * (1 + Real.log (A + 6)) ^ 2 / U)
    (hgap :
      ∀ {T U : ℝ}, 4 ≤ T → T ≤ U → U ≤ T + 3 →
        ‖explicitFormulaApproxWithMultiplicity x T -
            explicitFormulaApproxWithMultiplicity x U‖ ≤
          2 * Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2))
    (T : ℝ) (hT : 8 ≤ T) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        (chebyshevPsi0 x : ℂ)‖ ≤
      movingHeightApproximationBudget (Cs + 4 * Cg * x) T := by
  rcases hselected T hT with ⟨U, hUmem, _hgood, hUbound⟩
  have hTpos : 0 < T := by linarith
  have hTU : T ≤ U := hUmem.1
  have hUT3 : U ≤ T + 3 := by linarith [hUmem.2]
  let L : ℝ := 1 + Real.log (T + 8)
  let L6 : ℝ := 1 + Real.log (T + 6)
  have hlog : 0 ≤ Real.log (T + 8) :=
    Real.log_nonneg (by linarith)
  have hlog6 : 0 ≤ Real.log (T + 6) :=
    Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL6 : 0 ≤ L6 := by dsimp [L6]; linarith
  have hlog_le : Real.log (T + 6) ≤ Real.log (T + 8) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL6sq : L6 ^ 2 ≤ L ^ 2 := by
    have hL6le : L6 ≤ L := by dsimp [L6, L]; linarith
    nlinarith
  have hselectedRate :
      ‖explicitFormulaApproxWithMultiplicity x U -
          (chebyshevPsi0 x : ℂ)‖ ≤ Cs * L ^ 2 / T := by
    apply hUbound.trans
    have hnum6 : 0 ≤ Cs * L6 ^ 2 := mul_nonneg hCs (sq_nonneg L6)
    calc
      Cs * (1 + Real.log (T + 6)) ^ 2 / U =
          Cs * L6 ^ 2 / U := by rfl
      _ ≤ Cs * L6 ^ 2 / T :=
        div_le_div_of_nonneg_left hnum6 hTpos hTU
      _ ≤ Cs * L ^ 2 / T := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        exact mul_le_mul_of_nonneg_left hL6sq hCs
  have hincrement := hgap (by linarith) hTU hUT3
  have hden : 0 < T - 1 / 2 := by linarith
  have hLleSq : L ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hK : 0 ≤ 2 * Cg * x * L := by positivity
  have hincrementRate :
      ‖explicitFormulaApproxWithMultiplicity x T -
          explicitFormulaApproxWithMultiplicity x U‖ ≤
        4 * Cg * x * L ^ 2 / T := by
    apply hincrement.trans
    calc
      2 * Cg * x * (1 + Real.log (T + 8)) / (T - 1 / 2) =
          (2 * Cg * x * L) / (T - 1 / 2) := by rfl
      _ ≤ (4 * Cg * x * L) / T := by
        apply (div_le_div_iff₀ hden hTpos).2
        nlinarith
      _ ≤ (4 * Cg * x * L ^ 2) / T := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        exact mul_le_mul_of_nonneg_left hLleSq (by positivity)
  have hsplit :
      explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ) =
        (explicitFormulaApproxWithMultiplicity x T -
          explicitFormulaApproxWithMultiplicity x U) +
        (explicitFormulaApproxWithMultiplicity x U -
          (chebyshevPsi0 x : ℂ)) := by ring
  rw [hsplit]
  unfold movingHeightApproximationBudget
  calc
    _ ≤ ‖explicitFormulaApproxWithMultiplicity x T -
            explicitFormulaApproxWithMultiplicity x U‖ +
          ‖explicitFormulaApproxWithMultiplicity x U -
            (chebyshevPsi0 x : ℂ)‖ := norm_add_le _ _
    _ ≤ 4 * Cg * x * L ^ 2 / T + Cs * L ^ 2 / T :=
      add_le_add hincrementRate hselectedRate
    _ = (Cs + 4 * Cg * x) *
        (1 + Real.log (T + 8)) ^ 2 / T := by
      dsimp [L]
      ring

/-- The actual all-heights theorem admits a decomposition with one global
gap constant `Cg`; only the selected-height constant `Cs` remains
point-dependent. -/
theorem
    exists_uniform_gap_constant_forall_exists_structural_allHeights_certificate :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ {x : ℝ}, 1 < x →
      ∃ Cs : ℝ, 0 ≤ Cs ∧
        (∀ A : ℝ, 8 ≤ A →
          ∃ U ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight U ∧
            ‖explicitFormulaApproxWithMultiplicity x U -
                (chebyshevPsi0 x : ℂ)‖ ≤
              Cs * (1 + Real.log (A + 6)) ^ 2 / U) ∧
        ∀ T : ℝ, 8 ≤ T →
          ‖explicitFormulaApproxWithMultiplicity x T -
              (chebyshevPsi0 x : ℂ)‖ ≤
            movingHeightApproximationBudget (Cs + 4 * Cg * x) T := by
  rcases
      exists_uniform_norm_explicitFormulaApproxWithMultiplicity_sub_le_log_div_of_le_add_three
    with ⟨Cg, hCg, hgap⟩
  refine ⟨Cg, hCg, ?_⟩
  intro x hx
  rcases
      ExplicitFormulaResidues.exists_goodHeight_Icc_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div
        hx with
    ⟨Cs, hCs, hselected⟩
  refine ⟨Cs, hCs, hselected, ?_⟩
  intro T hT
  exact
    norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_structural_allHeights
      hx hCs hCg hselected (hgap hx) T hT

/-- Fully exposed all-heights certificate for `x ≥ 2`.  There are two global
constants:

* `Ch`, multiplying the explicit contour term `x²`;
* `Cg`, multiplying the explicit bounded-height-gap term `x`.

The only sample-dependent witness left is `Cp`, and it carries the exact
first-order Perron residual certificate. -/
theorem
    exists_uniform_contour_gap_constants_structural_allHeights_of_perronResidual :
    ∃ Ch Cg : ℝ, 0 ≤ Ch ∧ 0 ≤ Cg ∧ ∀ {x : ℝ}, 2 ≤ x →
      ∀ {Cp : ℝ}, PerronResidualCertificate x Cp →
        (∀ A : ℝ, 8 ≤ A →
          ∃ U ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight U ∧
            ‖explicitFormulaApproxWithMultiplicity x U -
                (chebyshevPsi0 x : ℂ)‖ ≤
              (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp + 2) *
                (1 + Real.log (A + 6)) ^ 2 / U) ∧
        ∀ T : ℝ, 8 ≤ T →
          ‖explicitFormulaApproxWithMultiplicity x T -
              (chebyshevPsi0 x : ℂ)‖ ≤
            movingHeightApproximationBudget
              (Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp + 2 +
                4 * Cg * x) T := by
  rcases
      exists_uniform_contour_constant_selectedHeight_of_perronResidual
    with ⟨Ch, hCh, hselected⟩
  rcases
      exists_uniform_norm_explicitFormulaApproxWithMultiplicity_sub_le_log_div_of_le_add_three
    with ⟨Cg, hCg, hgap⟩
  refine ⟨Ch, Cg, hCh, hCg, ?_⟩
  intro x hx Cp hCp
  have hselectedCp := hselected hx hCp
  refine ⟨hselectedCp, ?_⟩
  intro T hT
  have hx1 : 1 < x := by linarith
  have hCs :
      0 ≤ Ch * x ^ (2 : ℝ) + 2 * Real.pi * Cp + 2 := by
    have hx0 : 0 ≤ x := by linarith
    have hxpow : 0 ≤ x ^ (2 : ℝ) := Real.rpow_nonneg hx0 _
    exact add_nonneg
      (add_nonneg (mul_nonneg hCh hxpow)
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hCp.nonneg))
      (by norm_num)
  exact
    norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_structural_allHeights
      hx1 hCs hCg hselectedCp (hgap hx1) T hT

/-- Explicit exponential-height rate transfer for the all-heights
approximation budget. If the pointwise explicit-formula constants satisfy
`0 ≤ K(y) ≤ K0 * exp (κ y)` eventually, then the choice
`τ(y) = exp (lam * y)` makes

`exp (-β y) * movingHeightApproximationBudget (K y) (τ y)`

tend to zero as soon as `κ < lam + β`. The proof retains the dependence of
`K` on `y`; it does not assert a uniform explicit-formula constant. -/
theorem tendsto_normalized_movingHeightApproximationBudget_exp_atTop
    (K : ℝ → ℝ) (K0 κ lam β : ℝ)
    (hK0 : 0 ≤ K0) (hlam : 0 < lam) (hrate : κ < lam + β)
    (hK :
      ∀ᶠ y : ℝ in Filter.atTop,
        0 ≤ K y ∧ K y ≤ K0 * Real.exp (κ * y)) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-β * y) *
          movingHeightApproximationBudget (K y) (Real.exp (lam * y)))
      Filter.atTop (nhds 0) := by
  let a : ℝ := lam + β - κ
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hpow (n : ℕ) :
      Filter.Tendsto
        (fun y : ℝ => y ^ n * Real.exp (-a * y))
        Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) a ha)
  have hpoly :
      Filter.Tendsto
        (fun y : ℝ =>
          K0 * (1 + Real.log 9 + lam * y) ^ 2 * Real.exp (-a * y))
        Filter.atTop (nhds 0) := by
    have h0 := (hpow 0).const_mul (K0 * (1 + Real.log 9) ^ 2)
    have h1 := (hpow 1).const_mul (2 * K0 * (1 + Real.log 9) * lam)
    have h2 := (hpow 2).const_mul (K0 * lam ^ 2)
    have heq :
        ∀ᶠ y : ℝ in Filter.atTop,
          K0 * (1 + Real.log 9) ^ 2 *
                (y ^ 0 * Real.exp (-a * y)) +
              2 * K0 * (1 + Real.log 9) * lam *
                (y ^ 1 * Real.exp (-a * y)) +
              K0 * lam ^ 2 * (y ^ 2 * Real.exp (-a * y)) =
            K0 * (1 + Real.log 9 + lam * y) ^ 2 *
              Real.exp (-a * y) := by
      filter_upwards with y
      ring
    simpa only [mul_zero, add_zero] using ((h0.add h1).add h2).congr' heq
  refine squeeze_zero' ?_ ?_ hpoly
  · filter_upwards [hK] with y hKy
    unfold movingHeightApproximationBudget
    exact mul_nonneg (Real.exp_nonneg _)
      (div_nonneg (mul_nonneg hKy.1 (sq_nonneg _)) (Real.exp_nonneg _))
  · filter_upwards [hK, Filter.eventually_ge_atTop (0 : ℝ)] with y hKy hy
    have hlamy : 0 ≤ lam * y := mul_nonneg hlam.le hy
    have hexp_one : 1 ≤ Real.exp (lam * y) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hlamy
    have hheight :
        Real.exp (lam * y) + 8 ≤ 9 * Real.exp (lam * y) := by
      linarith
    have hlog :
        Real.log (Real.exp (lam * y) + 8) ≤ Real.log 9 + lam * y := by
      calc
        Real.log (Real.exp (lam * y) + 8) ≤
            Real.log (9 * Real.exp (lam * y)) :=
          Real.log_le_log (by positivity) hheight
        _ = Real.log 9 + lam * y := by
          rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0)
            (Real.exp_ne_zero _), Real.log_exp]
    have hbase_nonneg :
        0 ≤ 1 + Real.log (Real.exp (lam * y) + 8) := by
      have : 0 ≤ Real.log (Real.exp (lam * y) + 8) :=
        Real.log_nonneg (by linarith)
      linarith
    have hupper_nonneg : 0 ≤ 1 + Real.log 9 + lam * y := by
      have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
      linarith
    have hsq :
        (1 + Real.log (Real.exp (lam * y) + 8)) ^ 2 ≤
          (1 + Real.log 9 + lam * y) ^ 2 :=
      (sq_le_sq₀ hbase_nonneg hupper_nonneg).mpr (by linarith)
    have hnum :
        K y * (1 + Real.log (Real.exp (lam * y) + 8)) ^ 2 ≤
          (K0 * Real.exp (κ * y)) * (1 + Real.log 9 + lam * y) ^ 2 :=
      calc
        K y * (1 + Real.log (Real.exp (lam * y) + 8)) ^ 2 ≤
            (K0 * Real.exp (κ * y)) *
              (1 + Real.log (Real.exp (lam * y) + 8)) ^ 2 :=
          mul_le_mul_of_nonneg_right hKy.2 (sq_nonneg _)
        _ ≤ (K0 * Real.exp (κ * y)) * (1 + Real.log 9 + lam * y) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq
            (mul_nonneg hK0 (Real.exp_nonneg _))
    have hexp :
        Real.exp (-β * y) * Real.exp (κ * y) *
            Real.exp (-(lam * y)) =
          Real.exp (-a * y) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp only [a]
      ring
    unfold movingHeightApproximationBudget
    calc
      Real.exp (-β * y) *
            (K y * (1 + Real.log (Real.exp (lam * y) + 8)) ^ 2 /
              Real.exp (lam * y)) ≤
          Real.exp (-β * y) *
            ((K0 * Real.exp (κ * y)) *
              (1 + Real.log 9 + lam * y) ^ 2 /
                Real.exp (lam * y)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hnum (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      _ = K0 * (1 + Real.log 9 + lam * y) ^ 2 * Real.exp (-a * y) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        calc
          Real.exp (-β * y) *
                (K0 * Real.exp (κ * y) *
                  (1 + Real.log 9 + lam * y) ^ 2 *
                    Real.exp (-(lam * y))) =
              K0 * (1 + Real.log 9 + lam * y) ^ 2 *
                (Real.exp (-β * y) * Real.exp (κ * y) *
                  Real.exp (-(lam * y))) := by
            ring
          _ = K0 * (1 + Real.log 9 + lam * y) ^ 2 *
                Real.exp (-a * y) := by
            rw [hexp]

/-- Every prescribed positive normalized gap eventually dominates the
exponential-height approximation budget under the same rate condition. -/
theorem eventually_normalized_movingHeightApproximationBudget_exp_lt_gap
    (K : ℝ → ℝ) (K0 κ lam β gap : ℝ)
    (hK0 : 0 ≤ K0) (hlam : 0 < lam) (hrate : κ < lam + β)
    (hgap : 0 < gap)
    (hK :
      ∀ᶠ y : ℝ in Filter.atTop,
        0 ≤ K y ∧ K y ≤ K0 * Real.exp (κ * y)) :
    ∀ᶠ y : ℝ in Filter.atTop,
      Real.exp (-β * y) *
          movingHeightApproximationBudget (K y) (Real.exp (lam * y)) <
        gap :=
  (tendsto_normalized_movingHeightApproximationBudget_exp_atTop
    K K0 κ lam β hK0 hlam hrate hK).eventually
      (eventually_lt_nhds hgap)

/-- Specialization of the rate-transfer theorem to the genuine structural
constant `K(exp y) = Cs(y) + 4 * Cg * exp y`. Once the selected-height
constants have exponent at most `κ`, the gap contribution has the same
exponent for every `κ ≥ 1`. -/
theorem tendsto_normalized_structural_allHeights_budget_exp_atTop
    (Cs : ℝ → ℝ) (Cg Cs0 κ lam β : ℝ)
    (hCg : 0 ≤ Cg) (hCs0 : 0 ≤ Cs0) (hkappa : 1 ≤ κ)
    (hlam : 0 < lam) (hrate : κ < lam + β)
    (hCs :
      ∀ᶠ y : ℝ in Filter.atTop,
        0 ≤ Cs y ∧ Cs y ≤ Cs0 * Real.exp (κ * y)) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-β * y) *
          movingHeightApproximationBudget
            (Cs y + 4 * Cg * Real.exp y) (Real.exp (lam * y)))
      Filter.atTop (nhds 0) := by
  have hK0 : 0 ≤ Cs0 + 4 * Cg := by positivity
  apply tendsto_normalized_movingHeightApproximationBudget_exp_atTop
    (fun y => Cs y + 4 * Cg * Real.exp y)
    (Cs0 + 4 * Cg) κ lam β hK0 hlam hrate
  filter_upwards [hCs, Filter.eventually_ge_atTop (0 : ℝ)] with y hCsy hy
  have hykappa : y ≤ κ * y := by
    have hprod : 0 ≤ (κ - 1) * y :=
      mul_nonneg (sub_nonneg.mpr hkappa) hy
    nlinarith
  have hexp : Real.exp y ≤ Real.exp (κ * y) :=
    Real.exp_le_exp.mpr hykappa
  constructor
  · exact add_nonneg hCsy.1
      (mul_nonneg (mul_nonneg (by norm_num) hCg) (Real.exp_nonneg _))
  · calc
      Cs y + 4 * Cg * Real.exp y ≤
          Cs0 * Real.exp (κ * y) + 4 * Cg * Real.exp y :=
        add_le_add hCsy.2 le_rfl
      _ ≤ Cs0 * Real.exp (κ * y) + 4 * Cg * Real.exp (κ * y) := by
        exact add_le_add le_rfl <|
          mul_le_mul_of_nonneg_left hexp
            (mul_nonneg (by norm_num) hCg)
      _ = (Cs0 + 4 * Cg) * Real.exp (κ * y) := by ring

/-- Rate transfer after exposing the selected-height constant.  The contour
and bounded-gap pieces have explicit exponents `2` and `1`; hence for
`κ ≥ 2` the only remaining rate hypothesis is the one on the Perron residual
`Cp(exp y)`.

This is strictly stronger than assuming a rate for an opaque selected-height
constant `Cs`: it identifies the hard Perron inversion residual as the sole
uncontrolled component. -/
theorem
    tendsto_normalized_structural_allHeights_budget_of_perronResidual_exp_atTop
    (Cp : ℝ → ℝ) (Ch Cg Cp0 κ lam β : ℝ)
    (hCh : 0 ≤ Ch) (hCg : 0 ≤ Cg) (hCp0 : 0 ≤ Cp0)
    (hkappa : 2 ≤ κ) (hlam : 0 < lam) (hrate : κ < lam + β)
    (hCp :
      ∀ᶠ y : ℝ in Filter.atTop,
        0 ≤ Cp y ∧ Cp y ≤ Cp0 * Real.exp (κ * y)) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-β * y) *
          movingHeightApproximationBudget
            (Ch * (Real.exp y) ^ (2 : ℝ) +
                2 * Real.pi * Cp y + 2 +
              4 * Cg * Real.exp y)
            (Real.exp (lam * y)))
      Filter.atTop (nhds 0) := by
  have hCs0 :
      0 ≤ Ch + 2 * Real.pi * Cp0 + 2 := by positivity
  apply
    tendsto_normalized_structural_allHeights_budget_exp_atTop
      (fun y =>
        Ch * (Real.exp y) ^ (2 : ℝ) +
          2 * Real.pi * Cp y + 2)
      Cg (Ch + 2 * Real.pi * Cp0 + 2) κ lam β
      hCg hCs0 (by linarith) hlam hrate
  filter_upwards [hCp, Filter.eventually_ge_atTop (0 : ℝ)] with y hCpy hy
  have hyκ : 0 ≤ κ * y := mul_nonneg (by linarith) hy
  have htwoκ : 2 * y ≤ κ * y := by
    have : 0 ≤ (κ - 2) * y := mul_nonneg (sub_nonneg.mpr hkappa) hy
    linarith
  have hexpTwo :
      (Real.exp y) ^ (2 : ℝ) ≤ Real.exp (κ * y) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp]
    exact Real.exp_le_exp.mpr (by linarith)
  have honeExp : 1 ≤ Real.exp (κ * y) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hyκ
  constructor
  · have hpow : 0 ≤ (Real.exp y) ^ (2 : ℝ) :=
      Real.rpow_nonneg (Real.exp_nonneg y) _
    exact add_nonneg
      (add_nonneg (mul_nonneg hCh hpow)
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hCpy.1))
      (by norm_num)
  · calc
      Ch * (Real.exp y) ^ (2 : ℝ) +
            2 * Real.pi * Cp y + 2 ≤
          Ch * Real.exp (κ * y) +
            2 * Real.pi * (Cp0 * Real.exp (κ * y)) + 2 := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left hexpTwo hCh)
            (mul_le_mul_of_nonneg_left hCpy.2
              (mul_nonneg (by norm_num) Real.pi_pos.le)))
          le_rfl
      _ ≤ Ch * Real.exp (κ * y) +
            2 * Real.pi * (Cp0 * Real.exp (κ * y)) +
              2 * Real.exp (κ * y) := by
        exact add_le_add le_rfl (by nlinarith)
      _ = (Ch + 2 * Real.pi * Cp0 + 2) *
          Real.exp (κ * y) := by ring

/-- End-to-end family form of the residual split.  A family of genuine Perron
certificates gives the actual all-heights explicit-formula bound eventually
along `x = exp y`; a growth bound only for those residual constants then makes
the normalized structural budget tend to zero.

No uniform Perron estimate is asserted: both the certificate family and its
rate remain explicit hypotheses. -/
theorem
    exists_uniform_contour_gap_constants_eventually_allHeights_and_tendsto_of_perronResidual
    (Cp : ℝ → ℝ) (Cp0 κ lam β : ℝ)
    (hCp0 : 0 ≤ Cp0) (hkappa : 2 ≤ κ)
    (hlam : 0 < lam) (hrate : κ < lam + β)
    (hcertificate :
      ∀ᶠ y : ℝ in Filter.atTop,
        PerronResidualCertificate (Real.exp y) (Cp y))
    (hCpBound :
      ∀ᶠ y : ℝ in Filter.atTop,
        Cp y ≤ Cp0 * Real.exp (κ * y)) :
    ∃ Ch Cg : ℝ, 0 ≤ Ch ∧ 0 ≤ Cg ∧
      (∀ᶠ y : ℝ in Filter.atTop,
        ∀ T : ℝ, 8 ≤ T →
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
            movingHeightApproximationBudget
              (Ch * (Real.exp y) ^ (2 : ℝ) +
                  2 * Real.pi * Cp y + 2 +
                4 * Cg * Real.exp y) T) ∧
      Filter.Tendsto
        (fun y : ℝ =>
          Real.exp (-β * y) *
            movingHeightApproximationBudget
              (Ch * (Real.exp y) ^ (2 : ℝ) +
                  2 * Real.pi * Cp y + 2 +
                4 * Cg * Real.exp y)
              (Real.exp (lam * y)))
        Filter.atTop (nhds 0) := by
  rcases
      exists_uniform_contour_gap_constants_structural_allHeights_of_perronResidual
    with ⟨Ch, Cg, hCh, hCg, hstructural⟩
  refine ⟨Ch, Cg, hCh, hCg, ?_, ?_⟩
  · filter_upwards
      [hcertificate,
        Filter.eventually_ge_atTop (Real.log 2)] with y hcert hy
    have hx : (2 : ℝ) ≤ Real.exp y := by
      calc
        (2 : ℝ) = Real.exp (Real.log 2) :=
          (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp y := Real.exp_le_exp.mpr hy
    exact (hstructural hx hcert).2
  · apply
      tendsto_normalized_structural_allHeights_budget_of_perronResidual_exp_atTop
        Cp Ch Cg Cp0 κ lam β hCh hCg hCp0 hkappa hlam hrate
    filter_upwards [hcertificate, hCpBound] with y hcert hbound
    exact ⟨hcert.nonneg, hbound⟩

/-- The pointwise Perron residual obstruction is removed on the upper natural
logarithmic mesh. A single global constant gives `Cp(m) = O(m^5)`, the actual
all-heights explicit-formula estimate holds at every sufficiently large mesh
point, and its normalized budget tends to zero whenever `5 < lam + β`.

This theorem deliberately makes no assertion for arbitrary real samples. Its
mesh is compatible with the fixed-height detector by
`exists_uniform_nat_perronResidualCertificate_and_eventually_visible`. -/
theorem
    exists_uniform_contour_gap_constants_eventually_natLogSamples_and_tendsto
    (lam β : ℝ) (hlam : 0 < lam) (hrate : 5 < lam + β) :
    ∃ Cp0 Ch Cg : ℝ, 0 ≤ Cp0 ∧ 0 ≤ Ch ∧ 0 ≤ Cg ∧
      (∀ᶠ y : ℝ in Filter.atTop,
        let m := upperNaturalLogSampleNat y
        PerronResidualCertificate (m : ℝ) (Cp0 * (m : ℝ) ^ 5) ∧
          ∀ T : ℝ, 8 ≤ T →
            ‖explicitFormulaApproxWithMultiplicity (m : ℝ) T -
                (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
              movingHeightApproximationBudget
                (Ch * (m : ℝ) ^ (2 : ℝ) +
                    2 * Real.pi * (Cp0 * (m : ℝ) ^ 5) + 2 +
                  4 * Cg * (m : ℝ)) T) ∧
      Filter.Tendsto
        (fun y : ℝ =>
          let m := upperNaturalLogSampleNat y
          Real.exp (-β * Real.log (m : ℝ)) *
            movingHeightApproximationBudget
              (Ch * (m : ℝ) ^ (2 : ℝ) +
                  2 * Real.pi * (Cp0 * (m : ℝ) ^ 5) + 2 +
                4 * Cg * (m : ℝ))
              (Real.exp (lam * Real.log (m : ℝ))))
        Filter.atTop (nhds 0) := by
  rcases exists_uniform_nat_perronResidualCertificate with
    ⟨Cp0, hCp0, hcertificate⟩
  rcases
      exists_uniform_contour_gap_constants_structural_allHeights_of_perronResidual
    with ⟨Ch, Cg, hCh, hCg, hstructural⟩
  refine ⟨Cp0, Ch, Cg, hCp0, hCh, hCg, ?_, ?_⟩
  · filter_upwards
      [Filter.eventually_ge_atTop (Real.log 2)] with y hy
    let m : ℕ := upperNaturalLogSampleNat y
    have hm : 2 ≤ m := two_le_upperNaturalLogSampleNat hy
    have hcert := hcertificate m hm
    have hx : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    exact ⟨hcert, (hstructural hx hcert).2⟩
  · have hcontinuous :
        Filter.Tendsto
          (fun z : ℝ =>
            Real.exp (-β * z) *
              movingHeightApproximationBudget
                (Ch * (Real.exp z) ^ (2 : ℝ) +
                    2 * Real.pi * (Cp0 * Real.exp (5 * z)) + 2 +
                  4 * Cg * Real.exp z)
                (Real.exp (lam * z)))
          Filter.atTop (nhds 0) := by
      apply
        tendsto_normalized_structural_allHeights_budget_of_perronResidual_exp_atTop
          (fun z : ℝ => Cp0 * Real.exp (5 * z))
          Ch Cg Cp0 5 lam β hCh hCg hCp0 (by norm_num) hlam hrate
      filter_upwards with z
      exact ⟨mul_nonneg hCp0 (Real.exp_nonneg _), le_rfl⟩
    have hsampled :=
      hcontinuous.comp tendsto_upperNaturalLogSample_atTop
    apply hsampled.congr'
    filter_upwards with y
    let m : ℕ := upperNaturalLogSampleNat y
    have hmpos : 0 < (m : ℝ) := by
      dsimp [m, upperNaturalLogSampleNat]
      exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos y)
    have hlogm :
        upperNaturalLogSample y = Real.log (m : ℝ) := rfl
    have hexpm :
        Real.exp (upperNaturalLogSample y) = (m : ℝ) := by
      simpa [m] using exp_upperNaturalLogSample y
    have hexpFive :
        Real.exp (5 * upperNaturalLogSample y) = (m : ℝ) ^ 5 := by
      rw [show (5 : ℝ) * upperNaturalLogSample y =
          (5 : ℕ) * upperNaturalLogSample y by norm_num,
        Real.exp_nat_mul, hexpm]
    simp only [Function.comp_apply]
    rw [hexpm, hexpFive, hlogm]

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

/-- Combining the global zero-count estimate with eventual nonemptiness
removes the opaque package cardinality from the canonical interval bound.
The actual minimum imaginary spacing `Δ_T` remains explicit. -/
theorem
    exists_C_T0_forall_maximalZeroPackageCanonicalIntervalLength_le_mul_log_div_spacing :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      maximalZeroPackageCanonicalIntervalLength T ≤
        2 * (C * T * (1 + Real.log (T + 6))) /
            maximalZeroPackageMinimumImaginarySpacing T + 1 := by
  rcases exists_card_maximalRealPartZeroPackage_le_mul_log with
    ⟨C, hC, hcard⟩
  rcases exists_eventually_maximalRealPartZeroPackage_nonempty with
    ⟨T0, hT0, hpackage⟩
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T hT
  have hT4 : 4 ≤ T := by linarith
  have hbase :=
    maximalZeroPackageCanonicalIntervalLength_le_card_sub_one_div_spacing
      T (hpackage T hT)
  have hsub :
      ((((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ)) ≤
        ((maximalRealPartZeroPackage T).card : ℝ) := by
    exact_mod_cast Nat.sub_le (maximalRealPartZeroPackage T).card 1
  have hnumerator :
      ((((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ)) ≤
        C * T * (1 + Real.log (T + 6)) :=
    hsub.trans (hcard T hT4)
  have hspacing := maximalZeroPackageMinimumImaginarySpacing_pos T
  have hfrac :
      2 * ((((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ)) /
          maximalZeroPackageMinimumImaginarySpacing T ≤
        2 * (C * T * (1 + Real.log (T + 6))) /
          maximalZeroPackageMinimumImaginarySpacing T := by
    gcongr
  linarith

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

/-!
## Cardinality-free Hilbert visibility

The following finite-package estimates use the concrete
Hilbert--Montgomery--Vaughan inequality. They retain analytic multiplicity and
combine the exact pairwise threshold with the cardinality-free Hilbert
threshold. No uniform spacing bound or explicit-formula remainder estimate is
asserted here.
-/

/-- The concrete Carneiro--Littmann Hilbert certificate controls both endpoint
Hilbert forms in the exact mean-square identity. -/
theorem abs_finiteExponentialMeanSquare_sub_diagonal_le_localSeparation
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    |(∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2) -
        (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2| ≤
      4 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n := by
  let L : ℝ := ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2
  let D : ℝ := (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2
  let W : ℝ :=
    ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n
  have heq :=
    finiteExponentialMeanSquare_cast_eq_diagonal_add_hilbert
      (S := S) (c := c) (omega := omega) (a := a) (b := b) homega
  have hcast : ((L - D : ℝ) : ℂ) =
      -Complex.I *
        (hilbertForm S (phaseTwist c omega b) omega -
          hilbertForm S (phaseTwist c omega a) omega) := by
    dsimp [L, D]
    rw [ofReal_sub]
    push_cast
    rw [heq]
    ring
  have hphase (t : ℝ) :
      (∑ n ∈ S,
          ‖phaseTwist c omega t n‖ ^ 2 /
            localFrequencySeparation S omega n) = W := by
    dsimp [W]
    apply Finset.sum_congr rfl
    intro n hn
    simp [phaseTwist, Complex.norm_exp]
  have hHb :=
    hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann
      S (phaseTwist c omega b) omega hS homega
  have hHa :=
    hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann
      S (phaseTwist c omega a) omega hS homega
  rw [hphase] at hHb hHa
  calc
    |L - D| = ‖((L - D : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖-Complex.I *
        (hilbertForm S (phaseTwist c omega b) omega -
          hilbertForm S (phaseTwist c omega a) omega)‖ :=
      congrArg norm hcast
    _ = ‖hilbertForm S (phaseTwist c omega b) omega -
          hilbertForm S (phaseTwist c omega a) omega‖ := by
      rw [norm_mul, norm_neg, norm_I, one_mul]
    _ ≤ ‖hilbertForm S (phaseTwist c omega b) omega‖ +
          ‖hilbertForm S (phaseTwist c omega a) omega‖ :=
      norm_sub_le _ _
    _ ≤ 4 * Real.pi * W := by linarith
    _ = 4 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 /
          localFrequencySeparation S omega n := rfl

/-- The global minimum spacing is no larger than every local separation in a
nontrivial finite family. -/
theorem minimumPositiveFrequencySpacing_le_localFrequencySeparation
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {n : ι}
    (hS : S.Nontrivial) (hn : n ∈ S) :
    minimumPositiveFrequencySpacing S omega ≤
      localFrequencySeparation S omega n := by
  have hErase : (S.erase n).Nonempty := hS.erase_nonempty
  rw [localFrequencySeparation, dif_pos hErase, Finset.le_inf'_iff]
  intro m hm
  have hmS : m ∈ S := Finset.mem_of_mem_erase hm
  have hmn : m ≠ n := (Finset.mem_erase.mp hm).1
  exact minimumPositiveFrequencySpacing_le_abs_sub S omega hmS hn hmn

/-- Summing the local bounds loses no cardinality factor: the weighted local
energy is at most total energy divided by the global minimum spacing. -/
theorem sum_sqNorm_div_localFrequencySeparation_le_div_minimumSpacing
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    (∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n) ≤
      (∑ n ∈ S, ‖c n‖ ^ 2) /
        minimumPositiveFrequencySpacing S omega := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  have hmin := minimumPositiveFrequencySpacing_pos S omega homega
  have hlocal := localFrequencySeparation_pos hS hn homega
  exact div_le_div_of_nonneg_left (sq_nonneg _)
    hmin (minimumPositiveFrequencySpacing_le_localFrequencySeparation hS hn)

/-- Cardinality-free `4π / Δ` mean-square error for a nontrivial finite
frequency family. -/
theorem abs_finiteExponentialMeanSquare_sub_diagonal_le_minimumSpacing
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    |(∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2) -
        (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2| ≤
      4 * Real.pi * (∑ n ∈ S, ‖c n‖ ^ 2) /
        minimumPositiveFrequencySpacing S omega := by
  calc
    _ ≤ 4 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 /
          localFrequencySeparation S omega n :=
      abs_finiteExponentialMeanSquare_sub_diagonal_le_localSeparation
        hS homega
    _ ≤ 4 * Real.pi *
        ((∑ n ∈ S, ‖c n‖ ^ 2) /
          minimumPositiveFrequencySpacing S omega) := by
      gcongr
      exact
        sum_sqNorm_div_localFrequencySeparation_le_div_minimumSpacing
          hS homega
    _ = _ := by ring

/-- The cardinality-free mean-square error specialized to the maximal
real-part package of zeta zeros. Analytic multiplicity is retained in the
coefficient energy. -/
theorem abs_maximalZeroPackageFiniteExponentialMeanSquare_sub_diagonal_le
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ} :
    |(∫ y in a..b,
        ‖finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y‖ ^ 2) -
        (b - a) * maximalZeroPackageEnergy T| ≤
      4 * Real.pi * maximalZeroPackageEnergy T /
        maximalZeroPackageMinimumImaginarySpacing T := by
  have him :
      Set.InjOn Complex.im (maximalRealPartZeroPackage T : Set ℂ) := by
    apply im_injOn_of_re_eq _ (maximalZeroRealPart T)
    intro ρ hρ
    exact (mem_maximalRealPartZeroPackage.mp hρ).2.2
  simpa [maximalZeroPackageEnergy,
    maximalZeroPackageMinimumImaginarySpacing] using
    (abs_finiteExponentialMeanSquare_sub_diagonal_le_minimumSpacing
      (S := maximalRealPartZeroPackage T)
      (c := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
      (omega := Complex.im) (a := a) (b := b) hpackage him)

/-- On every nondegenerate interval, the Hilbert mean-square bound supplies an
interior point attaining the diagonal energy minus `4π E / (Δ L)`. -/
theorem exists_mem_Ioo_sqNorm_finiteExponentialSum_ge_hilbert
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {a b : ℝ}
    (hS : S.Nontrivial) (hab : a < b)
    (homega : Set.InjOn omega (S : Set ι)) :
    ∃ t ∈ Set.Ioo a b,
      (∑ n ∈ S, ‖c n‖ ^ 2) -
          (4 * Real.pi * (∑ n ∈ S, ‖c n‖ ^ 2) /
            minimumPositiveFrequencySpacing S omega) / (b - a) ≤
        ‖finiteExponentialSum S c omega t‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => ‖finiteExponentialSum S c omega t‖ ^ 2
  let D : ℝ := ∑ n ∈ S, ‖c n‖ ^ 2
  let B : ℝ :=
    4 * Real.pi * D / minimumPositiveFrequencySpacing S omega
  let A : ℝ := D - B / (b - a)
  have hf : Continuous f := by
    dsimp [f, finiteExponentialSum]
    fun_prop
  have haggregate :=
    abs_finiteExponentialMeanSquare_sub_diagonal_le_minimumSpacing
      (S := S) (c := c) (omega := omega) (a := a) (b := b) hS homega
  have hlower : (b - a) * D - B ≤ ∫ t in a..b, f t := by
    have hleft := (abs_le.mp haggregate).1
    dsimp [f, D, B] at hleft ⊢
    linarith
  have hlength : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hscale : (b - a) * A = (b - a) * D - B := by
    dsimp [A]
    field_simp
  by_contra! hnone
  have hdiff : IntervalIntegrable (fun t => A - f t)
      MeasureTheory.volume a b :=
    Continuous.intervalIntegrable (continuous_const.sub hf) a b
  have hpositive : 0 < ∫ t in a..b, A - f t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      hdiff (fun t ht => sub_pos.mpr (hnone t ht)) hab
  rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable continuous_const a b)
      (Continuous.intervalIntegrable hf a b),
    intervalIntegral.integral_const] at hpositive
  change 0 < (b - a) * A - ∫ t in a..b, f t at hpositive
  rw [hscale] at hpositive
  linarith

/-- Quantitative specialization to the maximal zeta-zero package. The lower
bound retains the growth exponent, analytic multiplicities, total coefficient
energy, actual minimum spacing, and interval length. -/
theorem
    exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_ge_hilbert
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Set.Ioo a b,
      Real.exp (maximalZeroRealPart T * y) ^ 2 *
          (maximalZeroPackageEnergy T -
            (4 * Real.pi * maximalZeroPackageEnergy T /
              maximalZeroPackageMinimumImaginarySpacing T) / (b - a)) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ^ 2 := by
  have him :
      Set.InjOn Complex.im (maximalRealPartZeroPackage T : Set ℂ) := by
    apply im_injOn_of_re_eq _ (maximalZeroRealPart T)
    intro ρ hρ
    exact (mem_maximalRealPartZeroPackage.mp hρ).2.2
  rcases exists_mem_Ioo_sqNorm_finiteExponentialSum_ge_hilbert
      (S := maximalRealPartZeroPackage T)
      (c := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
      (omega := Complex.im) hpackage hab him with ⟨y, hy, hpoint⟩
  refine ⟨y, hy, ?_⟩
  rw [equalRealPartZeroPackageContribution_exp_eq_exponentialPolynomial,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  have hpoly :
      multiplicityWeightedExponentialPolynomial
          (maximalRealPartZeroPackage T)
          (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y =
        finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y := by
    rfl
  change Real.exp (maximalZeroRealPart T * y) ^ 2 *
      (maximalZeroPackageEnergy T -
        (4 * Real.pi * maximalZeroPackageEnergy T /
          maximalZeroPackageMinimumImaginarySpacing T) / (b - a)) ≤
    Real.exp (maximalZeroRealPart T * y) ^ 2 *
      ‖multiplicityWeightedExponentialPolynomial
        (maximalRealPartZeroPackage T)
        (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y‖ ^ 2
  rw [hpoly]
  apply mul_le_mul_of_nonneg_left
  · simpa [maximalZeroPackageEnergy,
      maximalZeroPackageMinimumImaginarySpacing] using hpoint
  · exact sq_nonneg _

/-- The cardinality-free Hilbert lower main for the maximal zero package.
Analytic multiplicity is retained in `maximalZeroPackageEnergy`, while the
actual minimum imaginary spacing and interval length remain explicit. -/
def maximalZeroPackageHilbertMeanSquareMain (T L y : ℝ) : ℝ :=
  Real.exp (maximalZeroRealPart T * y) ^ 2 *
    (maximalZeroPackageEnergy T -
      (4 * Real.pi * maximalZeroPackageEnergy T /
        maximalZeroPackageMinimumImaginarySpacing T) / L)

/-- The Hilbert lower main is strictly positive for a nontrivial maximal
package on every interval longer than `4π / Δ_T`. -/
theorem maximalZeroPackageHilbertMeanSquareMain_pos (T y : ℝ)
    (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ}
    (hlength :
      4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T < b - a) :
    0 < maximalZeroPackageHilbertMeanSquareMain T (b - a) y := by
  have henergy : 0 < maximalZeroPackageEnergy T :=
    maximalZeroPackageEnergy_pos T hpackage.nonempty
  have hspacing := maximalZeroPackageMinimumImaginarySpacing_pos T
  have hthreshold :
      0 < 4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T :=
    div_pos (by positivity) hspacing
  have hinterval : 0 < b - a := lt_trans hthreshold hlength
  have hmul :
      4 * Real.pi * maximalZeroPackageEnergy T /
          maximalZeroPackageMinimumImaginarySpacing T <
        (b - a) * maximalZeroPackageEnergy T := by
    calc
      4 * Real.pi * maximalZeroPackageEnergy T /
          maximalZeroPackageMinimumImaginarySpacing T =
          (4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T) *
            maximalZeroPackageEnergy T := by ring
      _ < (b - a) * maximalZeroPackageEnergy T :=
        mul_lt_mul_of_pos_right hlength henergy
  have hratio :
      (4 * Real.pi * maximalZeroPackageEnergy T /
          maximalZeroPackageMinimumImaginarySpacing T) / (b - a) <
        maximalZeroPackageEnergy T := by
    exact (div_lt_iff₀ hinterval).mpr (by simpa [mul_comm] using hmul)
  unfold maximalZeroPackageHilbertMeanSquareMain
  exact mul_pos (sq_pos_of_pos (Real.exp_pos _)) (sub_pos.mpr hratio)

/-- If the maximal zero package has at least two members, every logarithmic
interval longer than `4π / Δ_T` contains a point where its actual
multiplicity-aware contribution is strictly nonzero. This statement concerns
only the selected finite package, not the explicit-formula remainder. -/
theorem
    exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_hilbert
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nontrivial)
    {a b : ℝ}
    (hlength :
      4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T < b - a) :
    ∃ y ∈ Set.Ioo a b,
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 := by
  have hab : a < b := by
    have hspacing := maximalZeroPackageMinimumImaginarySpacing_pos T
    have hpi : 0 < 4 * Real.pi := by positivity
    have hpositive :
        0 < 4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T :=
      div_pos hpi hspacing
    linarith
  have him :
      Set.InjOn Complex.im (maximalRealPartZeroPackage T : Set ℂ) := by
    apply im_injOn_of_re_eq _ (maximalZeroRealPart T)
    intro ρ hρ
    exact (mem_maximalRealPartZeroPackage.mp hρ).2.2
  rcases exists_mem_Ioo_sqNorm_finiteExponentialSum_ge_hilbert
      (S := maximalRealPartZeroPackage T)
      (c := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
      (omega := Complex.im) hpackage hab him with ⟨y, hy, hpoint⟩
  have henergy : 0 < maximalZeroPackageEnergy T :=
    maximalZeroPackageEnergy_pos T hpackage.nonempty
  have hinterval : 0 < b - a := sub_pos.mpr hab
  have hbracket :
      0 < maximalZeroPackageEnergy T -
        (4 * Real.pi * maximalZeroPackageEnergy T /
          maximalZeroPackageMinimumImaginarySpacing T) / (b - a) := by
    have hmul :
        4 * Real.pi * maximalZeroPackageEnergy T /
            maximalZeroPackageMinimumImaginarySpacing T <
          (b - a) * maximalZeroPackageEnergy T := by
      calc
        4 * Real.pi * maximalZeroPackageEnergy T /
            maximalZeroPackageMinimumImaginarySpacing T =
            (4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T) *
              maximalZeroPackageEnergy T := by ring
        _ < (b - a) * maximalZeroPackageEnergy T :=
          mul_lt_mul_of_pos_right hlength henergy
    have hratio :
        (4 * Real.pi * maximalZeroPackageEnergy T /
            maximalZeroPackageMinimumImaginarySpacing T) / (b - a) <
          maximalZeroPackageEnergy T := by
      exact (div_lt_iff₀ hinterval).mpr (by simpa [mul_comm] using hmul)
    linarith
  have hfinite :
      0 < ‖finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y‖ ^ 2 := by
    have hpoint' :
        maximalZeroPackageEnergy T -
            (4 * Real.pi * maximalZeroPackageEnergy T /
              maximalZeroPackageMinimumImaginarySpacing T) / (b - a) ≤
          ‖finiteExponentialSum (maximalRealPartZeroPackage T)
            (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
            Complex.im y‖ ^ 2 := by
      simpa [maximalZeroPackageEnergy,
        maximalZeroPackageMinimumImaginarySpacing] using hpoint
    exact lt_of_lt_of_le hbracket hpoint'
  refine ⟨y, hy, ?_⟩
  rw [equalRealPartZeroPackageContribution_exp_eq_exponentialPolynomial]
  change 0 <
    ‖((Real.exp (maximalZeroRealPart T * y) : ℝ) : ℂ) *
      multiplicityWeightedExponentialPolynomial
        (maximalRealPartZeroPackage T)
        (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y‖ ^ 2
  rw [norm_mul, mul_pow]
  have hgrowth :
      0 < ‖((Real.exp (maximalZeroRealPart T * y) : ℝ) : ℂ)‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact sq_pos_of_pos (Real.exp_pos _)
  have hpoly :
      multiplicityWeightedExponentialPolynomial
          (maximalRealPartZeroPackage T)
          (analyticOrderNatAt riemannZeta) (fun ρ => ρ⁻¹) Complex.im y =
        finiteExponentialSum (maximalRealPartZeroPackage T)
          (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * ρ⁻¹)
          Complex.im y := by
    rfl
  rw [hpoly]
  exact mul_pos hgrowth hfinite

/-- A nontrivial maximal zero package transfers the cardinality-free Hilbert
lower main to the actual `ψ₀(exp y) - exp y` detector on every logarithmic
interval longer than `4π / Δ_T`.

The conclusion retains analytic multiplicity through the energy, the actual
minimum spacing, the complementary package budget, the genuine finite-height
explicit-formula approximation norm, and the elementary closed terms. It does
not assert that the final displayed lower bound is positive after subtracting
those budgets. -/
theorem
    exists_C_forall_fixedHeight_maximalZeroPackage_hilbert_lower_bound
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      (maximalRealPartZeroPackage T).Nontrivial → ∀ {a b : ℝ},
        0 < a →
        4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T < b - a →
          ∃ y ∈ Set.Ioo a b,
            0 < maximalZeroPackageHilbertMeanSquareMain T (b - a) y ∧
            0 < Real.sqrt
              (maximalZeroPackageHilbertMeanSquareMain T (b - a) y) ∧
            Real.sqrt
                  (maximalZeroPackageHilbertMeanSquareMain T (b - a) y) -
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
  intro T hT hpackage a b ha hlength
  have hthreshold :
      0 < 4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T :=
    div_pos (by positivity) (maximalZeroPackageMinimumImaginarySpacing_pos T)
  have hab : a < b := sub_pos.mp (lt_trans hthreshold hlength)
  rcases exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_ge_hilbert
      T hpackage hab with ⟨y, hy, hmean⟩
  have hypos : 0 < y := lt_trans ha hy.1
  have hynonneg : 0 ≤ y := hypos.le
  have hmain_pos :
      0 < maximalZeroPackageHilbertMeanSquareMain T (b - a) y :=
    maximalZeroPackageHilbertMeanSquareMain_pos T y hpackage hlength
  have hmean' :
      maximalZeroPackageHilbertMeanSquareMain T (b - a) y ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ^ 2 := by
    simpa only [maximalZeroPackageHilbertMeanSquareMain] using hmean
  have hsqrt_le :
      Real.sqrt (maximalZeroPackageHilbertMeanSquareMain T (b - a) y) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ := by
    calc
      Real.sqrt (maximalZeroPackageHilbertMeanSquareMain T (b - a) y) ≤
          Real.sqrt
            (‖equalRealPartZeroPackageContribution (Real.exp y) T
                (maximalZeroRealPart T)‖ ^ 2) :=
        Real.sqrt_le_sqrt hmean'
      _ = ‖equalRealPartZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ :=
        Real.sqrt_sq (norm_nonneg _)
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
  refine ⟨y, hy, hmain_pos, Real.sqrt_pos.mpr hmain_pos, ?_⟩
  linarith

/-- The cardinality-free Hilbert interval threshold for the maximal package.
Its strict-visibility use requires a nontrivial package; the totalized spacing
definition alone does not make the Hilbert argument valid for a singleton. -/
def maximalZeroPackageHilbertIntervalLengthThreshold (T : ℝ) : ℝ :=
  4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T

/-- The honest unified threshold. A nontrivial package uses the better of the
exact pairwise threshold and `4π / Δ_T`; an empty or singleton package retains
the exact threshold. -/
def maximalZeroPackageUnifiedIntervalLengthThreshold (T : ℝ) : ℝ :=
  if (maximalRealPartZeroPackage T).Nontrivial then
    min (maximalZeroPackageIntervalLengthThreshold T)
      (maximalZeroPackageHilbertIntervalLengthThreshold T)
  else
    maximalZeroPackageIntervalLengthThreshold T

/-- A canonical interval length strictly exceeding the selected unified
threshold. No uniform control in `T` is asserted. -/
def maximalZeroPackageUnifiedCanonicalIntervalLength (T : ℝ) : ℝ :=
  maximalZeroPackageUnifiedIntervalLengthThreshold T + 1

/-- The lower main selected by the honest unified threshold. A nontrivial
package uses the exact main when its threshold is smaller and the Hilbert main
otherwise; an empty or singleton package always uses the exact main. -/
def maximalZeroPackageUnifiedMeanSquareMain (T L y : ℝ) : ℝ :=
  if (maximalRealPartZeroPackage T).Nontrivial then
    if maximalZeroPackageIntervalLengthThreshold T ≤
        maximalZeroPackageHilbertIntervalLengthThreshold T then
      maximalZeroPackageMeanSquareMain T L y
    else
      maximalZeroPackageHilbertMeanSquareMain T L y
  else
    maximalZeroPackageMeanSquareMain T L y

/-- Outside the nontrivial case, in particular for a singleton, the unified
canonical length is exactly the original exact-pairwise canonical length. -/
theorem maximalZeroPackageUnifiedCanonical_eq_exact_of_not_nontrivial
    (T : ℝ) (hpackage : ¬(maximalRealPartZeroPackage T).Nontrivial) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T =
      maximalZeroPackageCanonicalIntervalLength T := by
  simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
    maximalZeroPackageUnifiedIntervalLengthThreshold, if_neg hpackage,
    maximalZeroPackageCanonicalIntervalLength]

/-- Explicit singleton specialization of the unified canonical length. -/
theorem maximalZeroPackageUnifiedCanonical_eq_exact_of_card_eq_one
    (T : ℝ) (hcard : (maximalRealPartZeroPackage T).card = 1) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T =
      maximalZeroPackageCanonicalIntervalLength T := by
  apply maximalZeroPackageUnifiedCanonical_eq_exact_of_not_nontrivial
  intro hnontrivial
  have hsubsingleton :
      (maximalRealPartZeroPackage T : Set ℂ).Subsingleton :=
    Finset.card_le_one_iff_subsingleton.mp hcard.le
  exact hsubsingleton.not_nontrivial hnontrivial

/-- The unified canonical length is bounded by the minimum of the old
cardinality/spacing estimate and the cardinality-free Hilbert estimate. The
exact threshold remains inside the definition and can be strictly better than
both displayed coarse bounds. -/
theorem
    maximalZeroPackageUnifiedCanonicalIntervalLength_le_min_pairwise_hilbert
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (hnontrivial : (maximalRealPartZeroPackage T).Nontrivial) :
    maximalZeroPackageUnifiedCanonicalIntervalLength T ≤
      min
        (2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T)
        (maximalZeroPackageHilbertIntervalLengthThreshold T) + 1 := by
  simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
    maximalZeroPackageUnifiedIntervalLengthThreshold, if_pos hnontrivial]
  have hmin := min_le_min
    (maximalZeroPackageIntervalLengthThreshold_le_card_sub_one_div_spacing
      T hpackage)
    (le_refl (maximalZeroPackageHilbertIntervalLengthThreshold T))
  linarith

/-- Exact cardinality criterion for the Hilbert threshold to improve strictly
on the old `2 * (card - 1) / Δ_T` bound. Since `6 < 2π < 7`, this happens
exactly when the maximal package has at least eight distinct zeros. -/
theorem
    maximalZeroPackageHilbertIntervalLengthThreshold_lt_pairwise_iff
    (T : ℝ) :
    maximalZeroPackageHilbertIntervalLengthThreshold T <
        2 * (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) /
          maximalZeroPackageMinimumImaginarySpacing T ↔
      8 ≤ (maximalRealPartZeroPackage T).card := by
  have hspacing := maximalZeroPackageMinimumImaginarySpacing_pos T
  simp only [maximalZeroPackageHilbertIntervalLengthThreshold]
  rw [div_lt_div_iff_of_pos_right hspacing]
  constructor
  · intro h
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hcast :
        (6 : ℝ) < (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) := by
      nlinarith
    have hnat : 6 < (maximalRealPartZeroPackage T).card - 1 := by
      exact_mod_cast hcast
    omega
  · intro hcard
    have hnat : 7 ≤ (maximalRealPartZeroPackage T).card - 1 := by
      omega
    have hcast :
        (7 : ℝ) ≤ (((maximalRealPartZeroPackage T).card - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    nlinarith [Real.pi_lt_d2]

/-- The exact pairwise threshold supplies a strictly visible package point for
every nonempty maximal package, including a singleton. -/
theorem
    exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_exact
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    {a b : ℝ}
    (hlength : maximalZeroPackageIntervalLengthThreshold T < b - a) :
    ∃ y ∈ Set.Ioo a b,
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 := by
  have hinterval : 0 < b - a :=
    lt_of_le_of_lt
      (maximalZeroPackageIntervalLengthThreshold_nonneg T) hlength
  have hab : a < b := sub_pos.mp hinterval
  rcases exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge
      T (maximalZeroRealPart T) hab with ⟨y, hy, hmean⟩
  have hmean' :
      maximalZeroPackageMeanSquareMain T (b - a) y ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ^ 2 := by
    simpa only [maximalZeroPackageMeanSquareMain, maximalZeroPackageEnergy,
      maximalZeroPackageOffDiagonalBound, maximalRealPartZeroPackage] using
      hmean
  exact
    ⟨y, hy,
      lt_of_lt_of_le
        (maximalZeroPackageMeanSquareMain_pos T y hpackage hlength) hmean'⟩

/-- Every nonempty maximal package has an interior point with strictly positive
actual multiplicity-aware contribution on the unified canonical interval.
Singletons use the exact mean square; nontrivial packages use whichever of the
exact and Hilbert thresholds is smaller. -/
theorem
    exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_on_unified_canonical
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty)
    (a : ℝ) :
    ∃ y ∈ Set.Ioo a
        (a + maximalZeroPackageUnifiedCanonicalIntervalLength T),
      0 < ‖equalRealPartZeroPackageContribution (Real.exp y) T
        (maximalZeroRealPart T)‖ ^ 2 := by
  by_cases hnontrivial : (maximalRealPartZeroPackage T).Nontrivial
  · by_cases hexact :
        maximalZeroPackageIntervalLengthThreshold T ≤
          maximalZeroPackageHilbertIntervalLengthThreshold T
    · have hlength :
          maximalZeroPackageIntervalLengthThreshold T <
            (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a := by
        simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
          maximalZeroPackageUnifiedIntervalLengthThreshold,
          if_pos hnontrivial, min_eq_left hexact, add_sub_cancel_left]
        exact lt_add_one _
      exact
        exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_exact
          T hpackage hlength
    · have hhilbert :
          maximalZeroPackageHilbertIntervalLengthThreshold T ≤
            maximalZeroPackageIntervalLengthThreshold T :=
        le_of_not_ge hexact
      have hlength :
          4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T <
            (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a := by
        rw [maximalZeroPackageUnifiedCanonicalIntervalLength,
          maximalZeroPackageUnifiedIntervalLengthThreshold,
          if_pos hnontrivial, add_sub_cancel_left, min_eq_right hhilbert]
        exact lt_add_one
          (4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T)
      exact
        exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_hilbert
          T hnontrivial hlength
  · have hlength :
        maximalZeroPackageIntervalLengthThreshold T <
          (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a := by
      simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
        maximalZeroPackageUnifiedIntervalLengthThreshold,
        if_neg hnontrivial, add_sub_cancel_left]
      exact lt_add_one _
    exact
      exists_mem_Ioo_sqNorm_maximalZeroPackageContribution_pos_of_exact
        T hpackage hlength

/-- Unified canonical fixed-height transfer to the actual `ψ₀` detector.
Nontrivial packages branch on which of the exact and Hilbert thresholds is
smaller; empty or singleton packages use only the exact theorem. Thus no
argument treats a bound by the minimum threshold as if both threshold
inequalities held.

The selected lower main remains strictly positive before the complementary,
finite-height approximation, and closed-term budgets are subtracted. No
uniform spacing estimate or unconditional `Omega` conclusion is asserted. -/
theorem
    exists_C_forall_fixedHeight_maximalZeroPackage_unified_lower_bound_on_canonical_interval
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      (maximalRealPartZeroPackage T).Nonempty → ∀ {a : ℝ}, 0 < a →
        ∃ y ∈ Set.Ioo a
            (a + maximalZeroPackageUnifiedCanonicalIntervalLength T),
          0 < maximalZeroPackageUnifiedMeanSquareMain T
              (maximalZeroPackageUnifiedCanonicalIntervalLength T) y ∧
          0 < Real.sqrt (maximalZeroPackageUnifiedMeanSquareMain T
                (maximalZeroPackageUnifiedCanonicalIntervalLength T) y) ∧
          Real.sqrt (maximalZeroPackageUnifiedMeanSquareMain T
                  (maximalZeroPackageUnifiedCanonicalIntervalLength T) y) -
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
    ⟨Cexact, hCexact, hexact⟩
  rcases
      exists_C_forall_fixedHeight_maximalZeroPackage_hilbert_lower_bound with
    ⟨Chilbert, hChilbert, hhilbert⟩
  refine ⟨max Cexact Chilbert, hCexact.trans (le_max_left _ _), ?_⟩
  intro T hT hpackage a ha
  have hbudget_exact (y : ℝ) :
      Real.exp ((maximalZeroRealPart T -
            maximalComplementaryRealPartGap T) * y) *
          (Cexact * (1 + Real.log (T + 6)) ^ 2) ≤
        Real.exp ((maximalZeroRealPart T -
            maximalComplementaryRealPartGap T) * y) *
          (max Cexact Chilbert * (1 + Real.log (T + 6)) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have hbudget_hilbert (y : ℝ) :
      Real.exp ((maximalZeroRealPart T -
            maximalComplementaryRealPartGap T) * y) *
          (Chilbert * (1 + Real.log (T + 6)) ^ 2) ≤
        Real.exp ((maximalZeroRealPart T -
            maximalComplementaryRealPartGap T) * y) *
          (max Cexact Chilbert * (1 + Real.log (T + 6)) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  have hcanonical_sub :
      (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a =
        maximalZeroPackageUnifiedCanonicalIntervalLength T := by
    ring
  by_cases hnontrivial : (maximalRealPartZeroPackage T).Nontrivial
  · by_cases hexact_le :
        maximalZeroPackageIntervalLengthThreshold T ≤
          maximalZeroPackageHilbertIntervalLengthThreshold T
    · have hlength :
          maximalZeroPackageIntervalLengthThreshold T <
            (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a := by
        simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
          maximalZeroPackageUnifiedIntervalLengthThreshold,
          if_pos hnontrivial, min_eq_left hexact_le, add_sub_cancel_left]
        exact lt_add_one _
      rcases hexact T hT hpackage ha hlength with
        ⟨y, hy, hmain, hsqrt, hpsi⟩
      rw [hcanonical_sub] at hmain hsqrt hpsi
      have hunified :
          maximalZeroPackageUnifiedMeanSquareMain T
              (maximalZeroPackageUnifiedCanonicalIntervalLength T) y =
            maximalZeroPackageMeanSquareMain T
              (maximalZeroPackageUnifiedCanonicalIntervalLength T) y := by
        simp only [maximalZeroPackageUnifiedMeanSquareMain,
          if_pos hnontrivial, if_pos hexact_le]
      refine ⟨y, hy, ?_, ?_, ?_⟩
      · rw [hunified]
        exact hmain
      · rw [hunified]
        exact hsqrt
      · rw [hunified]
        linarith [hbudget_exact y]
    · have hhilbert_le :
          maximalZeroPackageHilbertIntervalLengthThreshold T ≤
            maximalZeroPackageIntervalLengthThreshold T :=
        le_of_not_ge hexact_le
      have hlength :
          4 * Real.pi / maximalZeroPackageMinimumImaginarySpacing T <
            (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a := by
        rw [maximalZeroPackageUnifiedCanonicalIntervalLength,
          maximalZeroPackageUnifiedIntervalLengthThreshold,
          if_pos hnontrivial, min_eq_right hhilbert_le,
          maximalZeroPackageHilbertIntervalLengthThreshold,
          add_sub_cancel_left]
        exact lt_add_one _
      rcases hhilbert T hT hnontrivial ha hlength with
        ⟨y, hy, hmain, hsqrt, hpsi⟩
      rw [hcanonical_sub] at hmain hsqrt hpsi
      have hunified :
          maximalZeroPackageUnifiedMeanSquareMain T
              (maximalZeroPackageUnifiedCanonicalIntervalLength T) y =
            maximalZeroPackageHilbertMeanSquareMain T
              (maximalZeroPackageUnifiedCanonicalIntervalLength T) y := by
        simp only [maximalZeroPackageUnifiedMeanSquareMain,
          if_pos hnontrivial, if_neg hexact_le]
      refine ⟨y, hy, ?_, ?_, ?_⟩
      · rw [hunified]
        exact hmain
      · rw [hunified]
        exact hsqrt
      · rw [hunified]
        linarith [hbudget_hilbert y]
  · have hlength :
        maximalZeroPackageIntervalLengthThreshold T <
          (a + maximalZeroPackageUnifiedCanonicalIntervalLength T) - a := by
      simp only [maximalZeroPackageUnifiedCanonicalIntervalLength,
        maximalZeroPackageUnifiedIntervalLengthThreshold,
        if_neg hnontrivial, add_sub_cancel_left]
      exact lt_add_one _
    rcases hexact T hT hpackage ha hlength with
      ⟨y, hy, hmain, hsqrt, hpsi⟩
    rw [hcanonical_sub] at hmain hsqrt hpsi
    have hunified :
        maximalZeroPackageUnifiedMeanSquareMain T
            (maximalZeroPackageUnifiedCanonicalIntervalLength T) y =
          maximalZeroPackageMeanSquareMain T
            (maximalZeroPackageUnifiedCanonicalIntervalLength T) y := by
      simp only [maximalZeroPackageUnifiedMeanSquareMain,
        if_neg hnontrivial]
    refine ⟨y, hy, ?_, ?_, ?_⟩
    · rw [hunified]
      exact hmain
    · rw [hunified]
      exact hsqrt
    · rw [hunified]
      linarith [hbudget_exact y]

/-!
## Fixed-height asymptotic reduction to the approximation norm

For a fixed height, nonemptiness of the maximal package already forces its
real part `β_T` to be positive. The strict complementary gap then makes the
complementary package negligible on the `exp (β_T y)` scale. The elementary
closed terms are bounded as `y → +∞`, hence are negligible on the same scale.

The final theorem in this section uses the exact canonical interval, which is
valid for every nonempty package including a singleton. Its only remaining
analytic input is a uniform normalized bound for the genuine finite-height
explicit-formula approximation norm on the translated interval. No assertion
about that input as `y → +∞` is made here.
-/

/-- A nonempty maximal package has strictly positive selected real part. This
is not an extra zero-location hypothesis: it follows from the defining
`0 < re ρ` condition for every nontrivial zero in the package. -/
theorem maximalZeroRealPart_pos_of_maximalRealPartZeroPackage_nonempty
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    0 < maximalZeroRealPart T := by
  rcases hpackage with ⟨ρ, hρ⟩
  have hdata := mem_maximalRealPartZeroPackage.mp hρ
  rw [← hdata.2.2]
  exact hdata.1.2.1

/-- For every positive scale exponent `β`, the elementary closed terms are
negligible after normalization by `exp (β y)`. The proof uses the explicit
closed-term bound, including its decaying logarithmic tail. -/
theorem tendsto_normalized_norm_zeroPackageClosedTerms_atTop
    (β : ℝ) (hβ : 0 < β) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-β * y) * ‖zeroPackageClosedTerms y‖)
      Filter.atTop (nhds 0) := by
  have hlinearβ :
      Filter.Tendsto (fun y : ℝ => -β * y)
        Filter.atTop Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hβ)
      Filter.tendsto_id
  have hdecayβ :
      Filter.Tendsto (fun y : ℝ => Real.exp (-β * y))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlinearβ
  have hlinearTwo :
      Filter.Tendsto (fun y : ℝ => (-2 : ℝ) * y)
        Filter.atTop Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by norm_num)
      Filter.tendsto_id
  have hq :
      Filter.Tendsto (fun y : ℝ => Real.exp (-2 * y))
        Filter.atTop (nhds 0) := by
    simpa only using Real.tendsto_exp_atBot.comp hlinearTwo
  have hden :
      Filter.Tendsto (fun y : ℝ => 1 - Real.exp (-2 * y))
        Filter.atTop (nhds 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hq)
  have hratio :
      Filter.Tendsto
        (fun y : ℝ =>
          Real.exp (-2 * y) / (1 - Real.exp (-2 * y)))
        Filter.atTop (nhds 0) := by
    simpa only [zero_div] using hq.div hden (by norm_num)
  have hclosedBudget :
      Filter.Tendsto
        (fun y : ℝ =>
          Real.log (2 * Real.pi) +
            (1 / 2 : ℝ) * Real.exp (-2 * y) /
              (1 - Real.exp (-2 * y)))
        Filter.atTop (nhds (Real.log (2 * Real.pi))) := by
    have hlog :
        Filter.Tendsto (fun _ : ℝ => Real.log (2 * Real.pi))
          Filter.atTop (nhds (Real.log (2 * Real.pi))) :=
      tendsto_const_nhds
    have hhalf :
        Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
          Filter.atTop (nhds (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    simpa only [mul_div_assoc, mul_zero, add_zero] using
      hlog.add (hhalf.mul hratio)
  have hupper :
      Filter.Tendsto
        (fun y : ℝ =>
          Real.exp (-β * y) *
            (Real.log (2 * Real.pi) +
              (1 / 2 : ℝ) * Real.exp (-2 * y) /
                (1 - Real.exp (-2 * y))))
        Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using hdecayβ.mul hclosedBudget
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun y =>
      mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) ?_ hupper
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy
  have hypos : 0 < y := zero_lt_one.trans_le hy
  exact
    mul_le_mul_of_nonneg_left
      (norm_zeroPackageClosedTerms_le_log_two_pi_add_exp_neg_div hypos)
      (Real.exp_nonneg _)

/-- At fixed height, the only non-approximation terms in the zero-package
remainder are negligible on the maximal-package scale. The complementary
gap is selected from the finite zero data and is strictly positive without an
additional hypothesis. -/
theorem
    tendsto_normalized_fixedHeight_complementary_add_closedTerms_atTop
    (T : ℝ) (hβ : 0 < maximalZeroRealPart T) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-maximalZeroRealPart T * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ +
            ‖zeroPackageClosedTerms y‖))
      Filter.atTop (nhds 0) := by
  have hcomplement :=
    tendsto_normalized_norm_complementaryZeroPackageContribution_atTop T
  have hclosed :=
    tendsto_normalized_norm_zeroPackageClosedTerms_atTop
      (maximalZeroRealPart T) hβ
  simpa only [mul_add, zero_add] using hcomplement.add hclosed

/-- Exact reverse-triangle transfer with the complementary package, genuine
finite-height approximation norm, and elementary closed terms separated.
Unlike the earlier coarse transfer, no global reciprocal-zero constant is
inserted. -/
theorem
    norm_zeroPackage_sub_complementary_sub_approximation_sub_closed_le_psi0
    (T y : ℝ) :
    ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ -
        ‖complementaryZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ -
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
          (chebyshevPsi0 (Real.exp y) : ℂ)‖ -
        ‖zeroPackageClosedTerms y‖ ≤
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  have huncontrolled :=
    norm_zeroPackageUncontrolledRemainder_le_complementary_add_approximation
      y T
  have hremainder :
      ‖zeroPackageExplicitFormulaRemainder y T
          (maximalZeroRealPart T)‖ ≤
        ‖complementaryZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ +
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ +
          ‖zeroPackageClosedTerms y‖ := by
    rw [zeroPackageExplicitFormulaRemainder_eq_uncontrolled_add_closed]
    calc
      ‖zeroPackageUncontrolledRemainder y T (maximalZeroRealPart T) +
          zeroPackageClosedTerms y‖ ≤
          ‖zeroPackageUncontrolledRemainder y T (maximalZeroRealPart T)‖ +
            ‖zeroPackageClosedTerms y‖ :=
        norm_add_le _ _
      _ ≤
          (‖complementaryZeroPackageContribution (Real.exp y) T
                (maximalZeroRealPart T)‖ +
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖) +
            ‖zeroPackageClosedTerms y‖ :=
        by linarith
  have htransfer :=
    norm_zeroPackage_sub_norm_remainder_le_norm_chebyshevPsi0_sub_exp
      T (maximalZeroRealPart T) y
  linarith

/-- The normalized positive amplitude supplied by the exact canonical
mean-square interval. This version is valid for a singleton package as well
as for larger packages. -/
def maximalZeroPackageCanonicalNormalizedAmplitude (T : ℝ) : ℝ :=
  Real.sqrt
    (maximalZeroPackageEnergy T -
      maximalZeroPackageOffDiagonalBound T /
        maximalZeroPackageCanonicalIntervalLength T)

/-- Nonemptiness makes the exact canonical normalized amplitude strictly
positive. -/
theorem maximalZeroPackageCanonicalNormalizedAmplitude_pos
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    0 < maximalZeroPackageCanonicalNormalizedAmplitude T := by
  apply Real.sqrt_pos.mpr
  have hlength :
      maximalZeroPackageIntervalLengthThreshold T <
        maximalZeroPackageCanonicalIntervalLength T :=
    maximalZeroPackageIntervalLengthThreshold_lt_canonical T
  simpa only [maximalZeroPackageCanonicalNormalizedAmplitude, sub_zero] using
    (maximalZeroPackageMeanSquareBracket_pos T hpackage
      (a := 0) (b := maximalZeroPackageCanonicalIntervalLength T)
      (by simpa only [sub_zero] using hlength))

/-- Every translated exact canonical interval contains a package-visible
point whose norm remains bounded below after normalization by the maximal
real-part scale. -/
theorem
    exists_mem_Ioo_normalized_maximalZeroPackageContribution_ge_canonicalAmplitude
    (T a : ℝ) :
    ∃ y ∈ Set.Ioo a
        (a + maximalZeroPackageCanonicalIntervalLength T),
      maximalZeroPackageCanonicalNormalizedAmplitude T ≤
        Real.exp (-maximalZeroRealPart T * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ := by
  have hlength :
      maximalZeroPackageIntervalLengthThreshold T <
        (a + maximalZeroPackageCanonicalIntervalLength T) - a := by
    simpa only [add_sub_cancel_left] using
      maximalZeroPackageIntervalLengthThreshold_lt_canonical T
  have hinterval :
      0 < (a + maximalZeroPackageCanonicalIntervalLength T) - a :=
    lt_of_le_of_lt
      (maximalZeroPackageIntervalLengthThreshold_nonneg T) hlength
  have hab : a < a + maximalZeroPackageCanonicalIntervalLength T :=
    sub_pos.mp hinterval
  rcases exists_mem_Ioo_sqNorm_equalRealPartZeroPackageContribution_ge
      T (maximalZeroRealPart T) hab with ⟨y, hy, hmean⟩
  have hmean' :
      maximalZeroPackageMeanSquareMain T
          (maximalZeroPackageCanonicalIntervalLength T) y ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ ^ 2 := by
    simpa only [maximalZeroPackageMeanSquareMain,
      maximalZeroPackageEnergy, maximalZeroPackageOffDiagonalBound,
      maximalRealPartZeroPackage, add_sub_cancel_left] using hmean
  have hsqrt :
      Real.sqrt
          (maximalZeroPackageMeanSquareMain T
            (maximalZeroPackageCanonicalIntervalLength T) y) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
          (maximalZeroRealPart T)‖ := by
    calc
      Real.sqrt
          (maximalZeroPackageMeanSquareMain T
            (maximalZeroPackageCanonicalIntervalLength T) y) ≤
          Real.sqrt
            (‖equalRealPartZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ ^ 2) :=
        Real.sqrt_le_sqrt hmean'
      _ =
          ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ :=
        Real.sqrt_sq (norm_nonneg _)
  have hsqrtScale :
      Real.sqrt
          (maximalZeroPackageMeanSquareMain T
            (maximalZeroPackageCanonicalIntervalLength T) y) =
        Real.exp (maximalZeroRealPart T * y) *
          maximalZeroPackageCanonicalNormalizedAmplitude T := by
    rw [maximalZeroPackageMeanSquareMain,
      maximalZeroPackageCanonicalNormalizedAmplitude,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hscaled :=
    mul_le_mul_of_nonneg_left hsqrt
      (Real.exp_nonneg (-maximalZeroRealPart T * y))
  rw [hsqrtScale] at hscaled
  have hinverse :
      Real.exp (-maximalZeroRealPart T * y) *
          Real.exp (maximalZeroRealPart T * y) = 1 := by
    calc
      Real.exp (-maximalZeroRealPart T * y) *
          Real.exp (maximalZeroRealPart T * y) =
          Real.exp
            (-maximalZeroRealPart T * y +
              maximalZeroRealPart T * y) := (Real.exp_add _ _).symm
      _ = Real.exp 0 := by ring_nf
      _ = 1 := Real.exp_zero
  refine ⟨y, hy, ?_⟩
  calc
    maximalZeroPackageCanonicalNormalizedAmplitude T =
        Real.exp (-maximalZeroRealPart T * y) *
          (Real.exp (maximalZeroRealPart T * y) *
            maximalZeroPackageCanonicalNormalizedAmplitude T) := by
      rw [← mul_assoc, hinverse, one_mul]
    _ ≤
        Real.exp (-maximalZeroRealPart T * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ :=
      hscaled

/-- Natural Perron samples are compatible with the actual fixed-height zero
detector. Far enough to the right, every translated canonical detector
interval contains a visible natural logarithmic sample after enlarging its
right endpoint by one. The normalized amplitude loses at most a factor two,
and the same sample carries the uniform `O(m^5 / W)` Perron certificate. -/
theorem exists_uniform_nat_perronResidualCertificate_and_eventually_visible
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    ∃ Cp0 A : ℝ, 0 ≤ Cp0 ∧ ∀ a : ℝ, A ≤ a →
      ∃ m : ℕ, 2 ≤ m ∧
        Real.log (m : ℝ) ∈
          Set.Ioo a (a + maximalZeroPackageCanonicalIntervalLength T + 1) ∧
        PerronResidualCertificate (m : ℝ) (Cp0 * (m : ℝ) ^ 5) ∧
        maximalZeroPackageCanonicalNormalizedAmplitude T / 2 ≤
          Real.exp (-maximalZeroRealPart T * Real.log (m : ℝ)) *
            ‖equalRealPartZeroPackageContribution (m : ℝ) T
              (maximalZeroRealPart T)‖ := by
  exact
    exists_uniform_nat_perronResidualCertificate_and_eventually_visible_of
      T (maximalZeroPackageCanonicalIntervalLength T)
      (maximalZeroPackageCanonicalNormalizedAmplitude T)
      (maximalZeroPackageCanonicalNormalizedAmplitude_pos T hpackage)
      (exists_mem_Ioo_normalized_maximalZeroPackageContribution_ge_canonicalAmplitude T)

/-- Strongest fixed-height asymptotic reduction currently available from this
module. For every nonempty maximal package, sufficiently far translated exact
canonical intervals contain a point with strictly positive `ψ₀` error,
provided only that the genuine explicit-formula approximation norm is
uniformly smaller than half the normalized canonical amplitude on that
interval.

The complementary zero package and elementary closed terms require no caller
bound: their normalized sum is proved to tend to zero. This theorem is fixed
in `T`; it is neither an `Omega` statement nor a moving-height result. -/
theorem
    exists_eventually_fixedHeight_psi0_error_pos_of_approximation_small
    (T : ℝ) (hpackage : (maximalRealPartZeroPackage T).Nonempty) :
    ∃ A : ℝ, ∀ a : ℝ, A ≤ a →
      (∀ y ∈ Set.Ioo a
          (a + maximalZeroPackageCanonicalIntervalLength T),
        Real.exp (-maximalZeroRealPart T * y) *
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖ <
          maximalZeroPackageCanonicalNormalizedAmplitude T / 2) →
      ∃ y ∈ Set.Ioo a
          (a + maximalZeroPackageCanonicalIntervalLength T),
        0 <
          ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  have hβ :
      0 < maximalZeroRealPart T :=
    maximalZeroRealPart_pos_of_maximalRealPartZeroPackage_nonempty T hpackage
  have hamplitude :
      0 < maximalZeroPackageCanonicalNormalizedAmplitude T :=
    maximalZeroPackageCanonicalNormalizedAmplitude_pos T hpackage
  have hnegligible :=
    tendsto_normalized_fixedHeight_complementary_add_closedTerms_atTop T hβ
  rcases
      (Metric.tendsto_atTop.mp hnegligible)
        (maximalZeroPackageCanonicalNormalizedAmplitude T / 2)
        (half_pos hamplitude) with
    ⟨A, hA⟩
  refine ⟨A, ?_⟩
  intro a ha happrox
  rcases
      exists_mem_Ioo_normalized_maximalZeroPackageContribution_ge_canonicalAmplitude
        T a with
    ⟨y, hy, hpackageLower⟩
  have hyA : A ≤ y := ha.trans hy.1.le
  have hbudgetDist := hA y hyA
  have hbudgetNonneg :
      0 ≤
        Real.exp (-maximalZeroRealPart T * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ +
            ‖zeroPackageClosedTerms y‖) :=
    mul_nonneg (Real.exp_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hbudget :
      Real.exp (-maximalZeroRealPart T * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ +
            ‖zeroPackageClosedTerms y‖) <
        maximalZeroPackageCanonicalNormalizedAmplitude T / 2 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hbudgetNonneg] using
      hbudgetDist
  have happroxY := happrox y hy
  have hnormalizedTotal :
      Real.exp (-maximalZeroRealPart T * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ +
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖ +
            ‖zeroPackageClosedTerms y‖) <
        maximalZeroPackageCanonicalNormalizedAmplitude T := by
    calc
      Real.exp (-maximalZeroRealPart T * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ +
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖ +
            ‖zeroPackageClosedTerms y‖) =
          Real.exp (-maximalZeroRealPart T * y) *
              (‖complementaryZeroPackageContribution (Real.exp y) T
                  (maximalZeroRealPart T)‖ +
                ‖zeroPackageClosedTerms y‖) +
            Real.exp (-maximalZeroRealPart T * y) *
              ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                (chebyshevPsi0 (Real.exp y) : ℂ)‖ := by
            ring
      _ <
          maximalZeroPackageCanonicalNormalizedAmplitude T / 2 +
            maximalZeroPackageCanonicalNormalizedAmplitude T / 2 :=
        add_lt_add hbudget happroxY
      _ = maximalZeroPackageCanonicalNormalizedAmplitude T := by ring
  have hpackageMinusRemaindersPos :
      0 <
        ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ -
          ‖complementaryZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ -
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ -
          ‖zeroPackageClosedTerms y‖ := by
    have hgrowthPos :
        0 < Real.exp (maximalZeroRealPart T * y) :=
      Real.exp_pos _
    have hscaledTotal :=
      mul_lt_mul_of_pos_left hnormalizedTotal hgrowthPos
    have hinverse :
        Real.exp (maximalZeroRealPart T * y) *
            Real.exp (-maximalZeroRealPart T * y) = 1 := by
      calc
        Real.exp (maximalZeroRealPart T * y) *
            Real.exp (-maximalZeroRealPart T * y) =
            Real.exp
              (maximalZeroRealPart T * y +
                -maximalZeroRealPart T * y) := (Real.exp_add _ _).symm
        _ = Real.exp 0 := by ring_nf
        _ = 1 := Real.exp_zero
    have htotal :
        ‖complementaryZeroPackageContribution (Real.exp y) T
              (maximalZeroRealPart T)‖ +
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖ +
            ‖zeroPackageClosedTerms y‖ <
          Real.exp (maximalZeroRealPart T * y) *
            maximalZeroPackageCanonicalNormalizedAmplitude T := by
      simpa only [← mul_assoc, hinverse, one_mul] using hscaledTotal
    have hpackageUnnormalized :
        Real.exp (maximalZeroRealPart T * y) *
            maximalZeroPackageCanonicalNormalizedAmplitude T ≤
          ‖equalRealPartZeroPackageContribution (Real.exp y) T
            (maximalZeroRealPart T)‖ := by
      have hscaledPackage :=
        mul_le_mul_of_nonneg_left hpackageLower
          (Real.exp_nonneg (maximalZeroRealPart T * y))
      simpa only [← mul_assoc, hinverse, one_mul] using hscaledPackage
    linarith
  have htransfer :=
    norm_zeroPackage_sub_complementary_sub_approximation_sub_closed_le_psi0
      T y
  exact ⟨y, hy, lt_of_lt_of_le hpackageMinusRemaindersPos htransfer⟩

/-!
## Moving-height pointwise positivity

The fixed-height asymptotic theorem above cannot simply be applied with a
height depending on `y`: its eventual threshold depends on the fixed zero
package. The next results instead work pointwise with the genuine height
`τ y`. They make no asymptotic assertion. A caller must exhibit a point where
the moving maximal package is visible and where the normalized complementary,
approximation, and closed-term budgets are jointly smaller than that visible
amplitude.

The final result in this section inserts the existing all-heights
explicit-formula estimate. Its constant still depends on the selected
`x = exp y`. Obtaining a rate for those constants along translated intervals,
while simultaneously selecting visible points and controlling the moving
complementary gap, remains the missing moving-height lemma.
-/

/-- At the genuine moving height `T = τ y`, package visibility and a strict
normalized budget inequality force a nonzero `ψ₀(exp y) - exp y` detector.
All three error terms are the actual terms appearing in the multiplicity-aware
explicit formula; no asymptotic or uniform-spacing hypothesis is hidden. -/
theorem psi0_error_pos_of_movingHeight_visible_point_and_exact_budget
    (τ : ℝ → ℝ) (y : ℝ)
    (hvisible :
      maximalZeroPackageCanonicalNormalizedAmplitude (τ y) ≤
        Real.exp (-maximalZeroRealPart (τ y) * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖)
    (hbudget :
      Real.exp (-maximalZeroRealPart (τ y) * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖ +
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) (τ y) -
                (chebyshevPsi0 (Real.exp y) : ℂ)‖ +
            ‖zeroPackageClosedTerms y‖) <
        maximalZeroPackageCanonicalNormalizedAmplitude (τ y)) :
    0 <
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  have hgrowthPos :
      0 < Real.exp (maximalZeroRealPart (τ y) * y) :=
    Real.exp_pos _
  have hscaledBudget :=
    mul_lt_mul_of_pos_left hbudget hgrowthPos
  have hinverse :
      Real.exp (maximalZeroRealPart (τ y) * y) *
          Real.exp (-maximalZeroRealPart (τ y) * y) = 1 := by
    calc
      Real.exp (maximalZeroRealPart (τ y) * y) *
          Real.exp (-maximalZeroRealPart (τ y) * y) =
          Real.exp
            (maximalZeroRealPart (τ y) * y +
              -maximalZeroRealPart (τ y) * y) := (Real.exp_add _ _).symm
      _ = Real.exp 0 := by ring_nf
      _ = 1 := Real.exp_zero
  have htotal :
      ‖complementaryZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖ +
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) (τ y) -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ +
          ‖zeroPackageClosedTerms y‖ <
        Real.exp (maximalZeroRealPart (τ y) * y) *
          maximalZeroPackageCanonicalNormalizedAmplitude (τ y) := by
    simpa only [← mul_assoc, hinverse, one_mul] using hscaledBudget
  have hscaledVisible :=
    mul_le_mul_of_nonneg_left hvisible
      (Real.exp_nonneg (maximalZeroRealPart (τ y) * y))
  have hpackage :
      Real.exp (maximalZeroRealPart (τ y) * y) *
          maximalZeroPackageCanonicalNormalizedAmplitude (τ y) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) (τ y)
          (maximalZeroRealPart (τ y))‖ := by
    simpa only [← mul_assoc, hinverse, one_mul] using hscaledVisible
  have hpositive :
      0 <
        ‖equalRealPartZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖ -
          ‖complementaryZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖ -
          ‖explicitFormulaApproxWithMultiplicity (Real.exp y) (τ y) -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ -
          ‖zeroPackageClosedTerms y‖ := by
    linarith
  exact
    lt_of_lt_of_le hpositive
      (norm_zeroPackage_sub_complementary_sub_approximation_sub_closed_le_psi0
        (τ y) y)

/-- Budgeted version of the moving-height pointwise transfer. The genuine
approximation norm is replaced by any certified upper budget at `T = τ y`. -/
theorem psi0_error_pos_of_movingHeight_visible_point_and_approximation_budget
    (τ : ℝ → ℝ) (y K : ℝ) (hheight : 8 ≤ τ y)
    (hvisible :
      maximalZeroPackageCanonicalNormalizedAmplitude (τ y) ≤
        Real.exp (-maximalZeroRealPart (τ y) * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖)
    (happrox :
      ∀ U : ℝ, 8 ≤ U →
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) U -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
          movingHeightApproximationBudget K U)
    (hbudget :
      Real.exp (-maximalZeroRealPart (τ y) * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖ +
            movingHeightApproximationBudget K (τ y) +
            ‖zeroPackageClosedTerms y‖) <
        maximalZeroPackageCanonicalNormalizedAmplitude (τ y)) :
    0 <
      ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖ := by
  have happroxAtHeight := happrox (τ y) hheight
  apply
    psi0_error_pos_of_movingHeight_visible_point_and_exact_budget
      τ y hvisible
  apply lt_of_le_of_lt _ hbudget
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  linarith

/-- Existing all-heights explicit-formula control supplies a point-dependent
constant `K` for the moving-height positivity test. The implication returned
here is the exact remaining numerical check at the visible point. Since `K`
depends on `y`, this theorem does not provide uniform decay on translated
moving intervals. -/
theorem
    exists_K_movingHeight_psi0_error_pos_of_visible_point_and_budget
    (τ : ℝ → ℝ) (y : ℝ) (hy : 0 < y) (hheight : 8 ≤ τ y)
    (hvisible :
      maximalZeroPackageCanonicalNormalizedAmplitude (τ y) ≤
        Real.exp (-maximalZeroRealPart (τ y) * y) *
          ‖equalRealPartZeroPackageContribution (Real.exp y) (τ y)
            (maximalZeroRealPart (τ y))‖) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ U : ℝ, 8 ≤ U →
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) U -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
          movingHeightApproximationBudget K U) ∧
      (Real.exp (-maximalZeroRealPart (τ y) * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖ +
            movingHeightApproximationBudget K (τ y) +
            ‖zeroPackageClosedTerms y‖) <
          maximalZeroPackageCanonicalNormalizedAmplitude (τ y) →
        0 <
          ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖) := by
  have hx : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
  rcases
      _root_.PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div
        hx with
    ⟨K, hK, happrox⟩
  refine ⟨K, hK, ?_, ?_⟩
  · intro U hU
    simpa only [movingHeightApproximationBudget] using happrox U hU
  · intro hbudget
    exact
      psi0_error_pos_of_movingHeight_visible_point_and_approximation_budget
        τ y K hheight hvisible
        (fun U hU => by
          simpa only [movingHeightApproximationBudget] using happrox U hU)
        hbudget

/-- Translated-interval contract for the moving-height reduction. Once a
package-visible point `y` has been selected inside the interval, the existing
explicit-formula theorem supplies a point-dependent approximation certificate
and reduces strict positivity to the displayed three-term budget inequality
at that same point. This does not select such points uniformly in the moving
height. -/
theorem
    exists_mem_Ioo_exists_K_movingHeight_psi0_error_pos_of_visible_and_budget
    (τ : ℝ → ℝ) (a b : ℝ)
    (hvisible :
      ∃ y ∈ Set.Ioo a b,
        0 < y ∧ 8 ≤ τ y ∧
          maximalZeroPackageCanonicalNormalizedAmplitude (τ y) ≤
            Real.exp (-maximalZeroRealPart (τ y) * y) *
              ‖equalRealPartZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖) :
    ∃ y ∈ Set.Ioo a b, ∃ K : ℝ, 0 ≤ K ∧
      (∀ U : ℝ, 8 ≤ U →
        ‖explicitFormulaApproxWithMultiplicity (Real.exp y) U -
            (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
          movingHeightApproximationBudget K U) ∧
      (Real.exp (-maximalZeroRealPart (τ y) * y) *
          (‖complementaryZeroPackageContribution (Real.exp y) (τ y)
                (maximalZeroRealPart (τ y))‖ +
            movingHeightApproximationBudget K (τ y) +
            ‖zeroPackageClosedTerms y‖) <
          maximalZeroPackageCanonicalNormalizedAmplitude (τ y) →
        0 <
          ‖(((chebyshevPsi0 (Real.exp y) - Real.exp y : ℝ) : ℂ))‖) := by
  rcases hvisible with ⟨y, hy, hypos, hheight, hpackage⟩
  rcases
      exists_K_movingHeight_psi0_error_pos_of_visible_point_and_budget
        τ y hypos hheight hpackage with
    ⟨K, hK, happrox, htransfer⟩
  exact ⟨y, hy, K, hK, happrox, htransfer⟩

end

end PrimeNumberTheorem.ZeroForcedOscillation
