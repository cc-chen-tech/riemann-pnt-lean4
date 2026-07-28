import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryPackage
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonOutsideClusterKernelTail

/-!
# Dominated convergence for an actual dynamic boundary package

Fix `sigma > 1 / 2`. Carlson summability gives a summable majorant

`multiplicity(rho) / |rho|`

for the positive nontrivial zeros with real part above `sigma`.  If every such
zero lies at or to the left of a target boundary `beta`, then:

* zeros strictly left of `beta` decay pointwise after target normalization;
* zeros on `re = beta` are eventually absorbed by the cofinal dynamic boundary
  package.

Tannery's theorem therefore makes the complete actual outside-package high
tail tend to zero without a uniform real-part gap.
-/

open scoped BigOperators Topology
open Filter Complex

namespace PrimeNumberTheorem

noncomputable section

/-- One weighted target-normalized zero term, deleted once it belongs to the
current dynamic boundary package. -/
def actualCarlsonDynamicBoundaryWeightedPowerTerm
    {sigma : ℝ} (H : ℝ → ℝ) (beta : ℝ)
    (index : ActualCarlsonPositiveZeroIndex sigma) (m : ℕ) : ℝ :=
  if actualCarlsonPositiveZero index ∈
      dynamicEqualRealPartZeroPackage H beta (m : ℝ) then
    0
  else
    actualCarlsonPositiveZeroWeight index *
      pntPowerLayerToTargetRatio beta
        (actualCarlsonPositiveZeroRealPart index) m

theorem actualCarlsonDynamicBoundaryWeightedPowerTerm_nonneg
    {sigma : ℝ} (H : ℝ → ℝ) (beta : ℝ)
    (index : ActualCarlsonPositiveZeroIndex sigma) (m : ℕ) :
    0 ≤
      actualCarlsonDynamicBoundaryWeightedPowerTerm
        H beta index m := by
  by_cases hmem :
      actualCarlsonPositiveZero index ∈
        dynamicEqualRealPartZeroPackage H beta (m : ℝ)
  · simp [actualCarlsonDynamicBoundaryWeightedPowerTerm, hmem]
  · simp only [actualCarlsonDynamicBoundaryWeightedPowerTerm, hmem, if_false]
    exact mul_nonneg
      (actualCarlsonPositiveZeroWeight_nonneg index)
      (Real.exp_pos _).le

/-- Every fixed indexed zero contributes a term tending to zero: strict-left
zeros decay by their power, while boundary zeros are eventually deleted. -/
theorem
    actualCarlsonDynamicBoundaryWeightedPowerTerm_tendsto_zero
    {sigma beta : ℝ} {H : ℝ → ℝ}
    (hH :
      Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (index : ActualCarlsonPositiveZeroIndex sigma)
    (hre : actualCarlsonPositiveZeroRealPart index ≤ beta) :
    Tendsto
      (actualCarlsonDynamicBoundaryWeightedPowerTerm H beta index)
      atTop (𝓝 0) := by
  by_cases heq :
      actualCarlsonPositiveZeroRealPart index = beta
  · have hspec := actualCarlsonPositiveZero_spec index
    have hheight :
        ∀ᶠ m : ℕ in atTop,
          |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ) :=
      (tendsto_atTop.1 hH)
        |(actualCarlsonPositiveZero index).im|
    have hmem :
        ∀ᶠ m : ℕ in atTop,
          actualCarlsonPositiveZero index ∈
            dynamicEqualRealPartZeroPackage H beta (m : ℝ) := by
      filter_upwards [hheight] with m hm
      rw [mem_dynamicEqualRealPartZeroPackage]
      exact ⟨hspec.1, hm, heq⟩
    apply
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [hmem] with m hm
    simp [actualCarlsonDynamicBoundaryWeightedPowerTerm, hm]
  · have hlt :
        actualCarlsonPositiveZeroRealPart index < beta :=
      lt_of_le_of_ne hre heq
    have hbase :
        Tendsto
          (fun m : ℕ =>
            actualCarlsonPositiveZeroWeight index *
              pntPowerLayerToTargetRatio beta
                (actualCarlsonPositiveZeroRealPart index) m)
          atTop (𝓝 0) := by
      simpa using
        (pntPowerLayerToTargetRatio_tendsto_zero_of_lt hlt).const_mul
          (actualCarlsonPositiveZeroWeight index)
    refine squeeze_zero' ?_ ?_ hbase
    · filter_upwards with m
      exact
        actualCarlsonDynamicBoundaryWeightedPowerTerm_nonneg
          H beta index m
    · filter_upwards with m
      by_cases hmem :
          actualCarlsonPositiveZero index ∈
            dynamicEqualRealPartZeroPackage H beta (m : ℝ)
      · simp only [actualCarlsonDynamicBoundaryWeightedPowerTerm,
          hmem, if_pos]
        exact mul_nonneg
          (actualCarlsonPositiveZeroWeight_nonneg index)
          (Real.exp_pos _).le
      · simp [actualCarlsonDynamicBoundaryWeightedPowerTerm, hmem]

/-- For natural scales at least one, every dynamic term is bounded in norm by
the summable Carlson reciprocal-norm weight. -/
theorem norm_actualCarlsonDynamicBoundaryWeightedPowerTerm_le
    {sigma beta : ℝ} (H : ℝ → ℝ)
    (index : ActualCarlsonPositiveZeroIndex sigma)
    {m : ℕ} (hm : 1 ≤ m)
    (hre : actualCarlsonPositiveZeroRealPart index ≤ beta) :
    ‖actualCarlsonDynamicBoundaryWeightedPowerTerm H beta index m‖ ≤
      actualCarlsonPositiveZeroWeight index := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (actualCarlsonDynamicBoundaryWeightedPowerTerm_nonneg
        H beta index m)]
  by_cases hmem :
      actualCarlsonPositiveZero index ∈
        dynamicEqualRealPartZeroPackage H beta (m : ℝ)
  · simp [actualCarlsonDynamicBoundaryWeightedPowerTerm, hmem,
      actualCarlsonPositiveZeroWeight_nonneg index]
  · simp only [actualCarlsonDynamicBoundaryWeightedPowerTerm, hmem, if_false]
    have hlog : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hm)
    have hexponent :
        (actualCarlsonPositiveZeroRealPart index - beta) *
            Real.log (m : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hre) hlog
    have hratio :
        pntPowerLayerToTargetRatio beta
            (actualCarlsonPositiveZeroRealPart index) m ≤ 1 := by
      unfold pntPowerLayerToTargetRatio
      exact Real.exp_le_one_iff.mpr hexponent
    simpa using
      mul_le_mul_of_nonneg_left hratio
        (actualCarlsonPositiveZeroWeight_nonneg index)

/-- The complete weighted positive-zero tail outside the cofinal dynamic
boundary package tends to zero. -/
theorem actualCarlsonDynamicBoundaryWeightedPowerTail_tendsto_zero
    {sigma beta : ℝ} {H : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hH :
      Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hright :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) :
    Tendsto
      (fun m : ℕ =>
        ∑' index : ActualCarlsonPositiveZeroIndex sigma,
          actualCarlsonDynamicBoundaryWeightedPowerTerm
            H beta index m)
      atTop (𝓝 0) := by
  have hpoint :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        Tendsto
          (actualCarlsonDynamicBoundaryWeightedPowerTerm
            H beta index)
          atTop (𝓝 0) := by
    intro index
    exact
      actualCarlsonDynamicBoundaryWeightedPowerTerm_tendsto_zero
        hH index (hright index)
  have hbound :
      ∀ᶠ m : ℕ in atTop,
        ∀ index : ActualCarlsonPositiveZeroIndex sigma,
          ‖actualCarlsonDynamicBoundaryWeightedPowerTerm
              H beta index m‖ ≤
            actualCarlsonPositiveZeroWeight index := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm index
    exact
      norm_actualCarlsonDynamicBoundaryWeightedPowerTerm_le
        H index hm (hright index)
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence
      (summable_actualCarlsonPositiveZeroWeight hhalf hone)
      hpoint hbound

/--
The sum of norms of the actual zeta kernels outside the dynamic boundary
package is negligible after normalization by `m^(beta - 1)`.
-/
theorem
    actualCarlsonDynamicBoundaryNormalizedKernelTail_tendsto_zero
    {sigma beta : ℝ} {H : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hH :
      Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hright :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) :
    Tendsto
      (fun m : ℕ =>
        actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta
          (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) m)
      atTop (𝓝 0) := by
  apply
    (actualCarlsonDynamicBoundaryWeightedPowerTail_tendsto_zero
      hhalf hone hH hright).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  apply tsum_congr
  intro index
  by_cases hmem :
      actualCarlsonPositiveZero index ∈
        dynamicEqualRealPartZeroPackage H beta (m : ℝ)
  · simp [actualCarlsonOutsideClusterNormalizedKernelTail,
      actualCarlsonDynamicBoundaryWeightedPowerTerm, hmem]
  · simp only [actualCarlsonOutsideClusterNormalizedKernelTail,
      actualCarlsonDynamicBoundaryWeightedPowerTerm, hmem, if_false]
    exact
      (normalized_actualCarlsonPositiveZeroKernel_eq_weightedPower
        index (Nat.zero_lt_of_lt hm)).symm

/-- A global right-edge hypothesis on positive nontrivial zeros supplies the
indexed right-edge condition used by the dominated-convergence theorem. -/
theorem
    actualCarlsonDynamicBoundaryNormalizedKernelTail_tendsto_zero_of_rightEdge
    {sigma beta : ℝ} {H : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hH :
      Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hright :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        0 < rho.im →
        rho.re ≤ beta) :
    Tendsto
      (fun m : ℕ =>
        actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta
          (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) m)
      atTop (𝓝 0) := by
  apply
    actualCarlsonDynamicBoundaryNormalizedKernelTail_tendsto_zero
      hhalf hone hH
  intro index
  have hspec := actualCarlsonPositiveZero_spec index
  exact hright _ hspec.1 hspec.2.1

end

end PrimeNumberTheorem
