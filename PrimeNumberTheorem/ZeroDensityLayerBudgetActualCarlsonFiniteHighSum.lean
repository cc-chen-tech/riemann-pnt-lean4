import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPositiveZeroCoverage
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonOutsideClusterKernelTail

/-!
# Finite high-strip zero sums inside the Carlson tail

This file turns shell coverage into the inequality needed by a truncated
explicit formula: every finite sum of actual high-strip positive-zero kernel
norms outside the main cluster is bounded by the complete Carlson `tsum`.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

def actualCarlsonPositiveZeroIndexEmbedding (sigma : ℝ) :
    ActualCarlsonHighPositiveZero sigma ↪
      ActualCarlsonPositiveZeroIndex sigma :=
  ⟨actualCarlsonPositiveZeroIndexOf,
    actualCarlsonPositiveZeroIndexOf_injective⟩

theorem pntPowerLayerToTargetRatio_nonneg
    (beta tau : ℝ) (m : ℕ) :
    0 ≤ pntPowerLayerToTargetRatio beta tau m :=
  (Real.exp_pos _).le

theorem pntPowerLayerToTargetRatio_le_one
    {beta tau : ℝ} {m : ℕ} (htau : tau < beta) (hm : 1 ≤ m) :
    pntPowerLayerToTargetRatio beta tau m ≤ 1 := by
  rw [pntPowerLayerToTargetRatio]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr htau.le)
    (Real.log_nonneg (by exact_mod_cast hm))

/-- The summand used by the actual outside-cluster normalized kernel tail. -/
def actualCarlsonOutsideClusterNormalizedKernelTerm
    {sigma : ℝ} (beta : ℝ) (S : Finset ℂ) (m : ℕ)
    (index : ActualCarlsonPositiveZeroIndex sigma) : ℝ :=
  if actualCarlsonPositiveZero index ∈ S then 0
  else
    ‖pntRelativeZeroContribution (m : ℝ)
      (actualCarlsonPositiveZero index)‖ / (m : ℝ) ^ (beta - 1)

theorem actualCarlsonOutsideClusterNormalizedKernelTerm_nonneg
    {sigma beta : ℝ} (S : Finset ℂ) (m : ℕ)
    (index : ActualCarlsonPositiveZeroIndex sigma) :
    0 ≤ actualCarlsonOutsideClusterNormalizedKernelTerm beta S m index := by
  by_cases hmem : actualCarlsonPositiveZero index ∈ S
  · simp [actualCarlsonOutsideClusterNormalizedKernelTerm, hmem]
  · exact by
      simp only [actualCarlsonOutsideClusterNormalizedKernelTerm,
        hmem, if_false]
      positivity

theorem summable_actualCarlsonOutsideClusterNormalizedKernelTerm
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hre : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index < beta)
    {m : ℕ} (hm : 1 ≤ m) :
    Summable
      (actualCarlsonOutsideClusterNormalizedKernelTerm
        (sigma := sigma) beta S m) := by
  let model : ActualCarlsonPositiveZeroIndex sigma → ℝ :=
    fun index =>
      actualCarlsonOutsideClusterWeight S index *
        pntPowerLayerToTargetRatio beta
          (actualCarlsonOutsideClusterRealPart beta S index) m
  have hmodel : Summable model := by
    refine Summable.of_nonneg_of_le ?_ ?_
      (summable_actualCarlsonOutsideClusterWeight S hhalf hone)
    · intro index
      exact mul_nonneg
        (actualCarlsonOutsideClusterWeight_nonneg S index)
        (pntPowerLayerToTargetRatio_nonneg _ _ _)
    · intro index
      exact mul_le_of_le_one_right
        (actualCarlsonOutsideClusterWeight_nonneg S index)
        (pntPowerLayerToTargetRatio_le_one
          (actualCarlsonOutsideClusterRealPart_lt S hre index) hm)
  apply hmodel.congr
  intro index
  by_cases hmem : actualCarlsonPositiveZero index ∈ S
  · simp [model, actualCarlsonOutsideClusterNormalizedKernelTerm,
      actualCarlsonOutsideClusterWeight,
      actualCarlsonOutsideClusterRealPart, hmem]
  · simp only [model, actualCarlsonOutsideClusterNormalizedKernelTerm,
      actualCarlsonOutsideClusterWeight,
      actualCarlsonOutsideClusterRealPart, hmem, if_false]
    exact
      (normalized_actualCarlsonPositiveZeroKernel_eq_weightedPower
        index (Nat.zero_lt_of_lt hm)).symm

theorem actualCarlsonOutsideClusterNormalizedKernelTail_eq_tsum_term
    {sigma beta : ℝ} (S : Finset ℂ) (m : ℕ) :
    actualCarlsonOutsideClusterNormalizedKernelTail
        (sigma := sigma) beta S m =
      ∑' index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonOutsideClusterNormalizedKernelTerm beta S m index :=
  rfl

/-- Any finite family of actual high-strip positive zeros outside `S` is
bounded by the complete normalized Carlson kernel tail. -/
theorem finite_actualHighPositiveZeroKernelSum_le_CarlsonTail
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hre : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index < beta)
    (s : Finset (ActualCarlsonHighPositiveZero sigma))
    (houtside : ∀ rho ∈ s, rho.1 ∉ S)
    {m : ℕ} (hm : 1 ≤ m) :
    (∑ rho ∈ s,
      ‖pntRelativeZeroContribution (m : ℝ) rho.1‖ /
        (m : ℝ) ^ (beta - 1)) ≤
      actualCarlsonOutsideClusterNormalizedKernelTail
        (sigma := sigma) beta S m := by
  let e := actualCarlsonPositiveZeroIndexEmbedding sigma
  let term :=
    actualCarlsonOutsideClusterNormalizedKernelTerm
      (sigma := sigma) beta S m
  have hsum :
      (∑ rho ∈ s,
        ‖pntRelativeZeroContribution (m : ℝ) rho.1‖ /
          (m : ℝ) ^ (beta - 1)) =
        ∑ index ∈ s.map e, term index := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro rho hrho
    change
      ‖pntRelativeZeroContribution (m : ℝ) rho.1‖ /
          (m : ℝ) ^ (beta - 1) =
        if actualCarlsonPositiveZero
            (actualCarlsonPositiveZeroIndexOf rho) ∈ S then 0
        else
          ‖pntRelativeZeroContribution (m : ℝ)
              (actualCarlsonPositiveZero
                (actualCarlsonPositiveZeroIndexOf rho))‖ /
            (m : ℝ) ^ (beta - 1)
    rw [actualCarlsonPositiveZero_indexOf]
    simp [houtside rho hrho]
  rw [hsum, actualCarlsonOutsideClusterNormalizedKernelTail_eq_tsum_term]
  exact
    (summable_actualCarlsonOutsideClusterNormalizedKernelTerm
      S hhalf hone hre hm).sum_le_tsum
        (s.map e)
        (fun index _ =>
          actualCarlsonOutsideClusterNormalizedKernelTerm_nonneg
            S m index)

end

end PrimeNumberTheorem
