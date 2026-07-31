import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryExponentTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryDominatedTail

/-!
# Visible Carlson tails at a variable boundary

For a moving finite-height right edge, zeros above the current explicit-formula
height must not be normalized against the current boundary.  This file deletes
such invisible zeros before applying Carlson summability.  Visible zeros are
bounded by the pointwise right edge, while each fixed zero is assumed to be
eventually absorbed by the boundary package or separated from it by one fixed
positive gap.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex ZeroForcedOscillation

noncomputable section

/-- Every indexed Carlson zero currently visible below `H m` lies at or left
of the selected boundary `beta m`. -/
def IsIndexedVariableBoundaryVisibleRightEdge
    {sigma : ℝ} (H beta : ℝ → ℝ) : Prop :=
  ∀ m : ℕ, ∀ index : ActualCarlsonPositiveZeroIndex sigma,
    |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ) →
      actualCarlsonPositiveZeroRealPart index ≤ beta (m : ℝ)

/-- Every fixed indexed zero is eventually either part of the current boundary
package or uniformly left of the moving boundary. -/
def VariableBoundaryAbsorptionOrGap
    {sigma : ℝ} (H beta : ℝ → ℝ) : Prop :=
  ∀ index : ActualCarlsonPositiveZeroIndex sigma,
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ m : ℕ in atTop,
        actualCarlsonPositiveZero index ∈
            variableBoundaryZeroPackage H beta (m : ℝ) ∨
          actualCarlsonPositiveZeroRealPart index ≤
            beta (m : ℝ) - delta

/-- One visible, outside-package, target-normalized Carlson zero term. -/
def variableBoundaryVisibleWeightedPowerTerm
    {sigma : ℝ} (H beta : ℝ → ℝ)
    (index : ActualCarlsonPositiveZeroIndex sigma) (m : ℕ) : ℝ :=
  if |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ) then
    if actualCarlsonPositiveZero index ∈
        variableBoundaryZeroPackage H beta (m : ℝ) then
      0
    else
      actualCarlsonPositiveZeroWeight index *
        pntPowerLayerToTargetRatio (beta (m : ℝ))
          (actualCarlsonPositiveZeroRealPart index) m
  else
    0

theorem variableBoundaryVisibleWeightedPowerTerm_nonneg
    {sigma : ℝ} (H beta : ℝ → ℝ)
    (index : ActualCarlsonPositiveZeroIndex sigma) (m : ℕ) :
    0 ≤ variableBoundaryVisibleWeightedPowerTerm H beta index m := by
  by_cases hvis :
      |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ)
  · by_cases hmem :
        actualCarlsonPositiveZero index ∈
          variableBoundaryZeroPackage H beta (m : ℝ)
    · simp [variableBoundaryVisibleWeightedPowerTerm, hvis, hmem]
    · simp only [variableBoundaryVisibleWeightedPowerTerm, hvis, hmem,
        if_true, if_false]
      exact mul_nonneg
        (actualCarlsonPositiveZeroWeight_nonneg index)
        (Real.exp_pos _).le
  · simp [variableBoundaryVisibleWeightedPowerTerm, hvis]

/-- Absorption-or-gap makes every fixed visible normalized term tend to zero. -/
theorem variableBoundaryVisibleWeightedPowerTerm_tendsto_zero
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta)
    (index : ActualCarlsonPositiveZeroIndex sigma) :
    Tendsto
      (variableBoundaryVisibleWeightedPowerTerm H beta index)
      atTop (nhds 0) := by
  rcases hgap index with ⟨delta, hdelta, heventual⟩
  have hbase :
      Tendsto
        (fun m : ℕ =>
          actualCarlsonPositiveZeroWeight index *
            pntPowerLayerToTargetRatio 0 (-delta) m)
        atTop (nhds 0) := by
    simpa using
      (pntPowerLayerToTargetRatio_tendsto_zero_of_lt
        (show -delta < (0 : ℝ) by linarith)).const_mul
          (actualCarlsonPositiveZeroWeight index)
  refine squeeze_zero' ?_ ?_ hbase
  · filter_upwards with m
    exact variableBoundaryVisibleWeightedPowerTerm_nonneg H beta index m
  · filter_upwards [heventual, eventually_ge_atTop (1 : ℕ)] with
      m hcase hm
    have hmajorantNonneg :
        0 ≤ actualCarlsonPositiveZeroWeight index *
          pntPowerLayerToTargetRatio 0 (-delta) m :=
      mul_nonneg (actualCarlsonPositiveZeroWeight_nonneg index)
        (Real.exp_pos _).le
    rcases hcase with hmem | hleft
    · simp [variableBoundaryVisibleWeightedPowerTerm, hmem,
        hmajorantNonneg]
    · by_cases hvis :
          |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ)
      · by_cases hmem :
            actualCarlsonPositiveZero index ∈
              variableBoundaryZeroPackage H beta (m : ℝ)
        · simp [variableBoundaryVisibleWeightedPowerTerm, hvis, hmem,
            hmajorantNonneg]
        · simp only [variableBoundaryVisibleWeightedPowerTerm, hvis, hmem,
            if_true, if_false]
          have hlog : 0 ≤ Real.log (m : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hm)
          have hexponent :
              (actualCarlsonPositiveZeroRealPart index - beta (m : ℝ)) *
                  Real.log (m : ℝ) ≤
                (-delta - 0) * Real.log (m : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hlog
            linarith
          have hratio :
              pntPowerLayerToTargetRatio (beta (m : ℝ))
                  (actualCarlsonPositiveZeroRealPart index) m ≤
                pntPowerLayerToTargetRatio 0 (-delta) m := by
            unfold pntPowerLayerToTargetRatio
            exact Real.exp_le_exp.mpr hexponent
          exact mul_le_mul_of_nonneg_left hratio
            (actualCarlsonPositiveZeroWeight_nonneg index)
      · simp [variableBoundaryVisibleWeightedPowerTerm, hvis,
          hmajorantNonneg]

/-- At positive natural scales, the pointwise visible right edge bounds every
variable normalized term by its summable Carlson weight. -/
theorem norm_variableBoundaryVisibleWeightedPowerTerm_le
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hright : IsIndexedVariableBoundaryVisibleRightEdge
      (sigma := sigma) H beta)
    (index : ActualCarlsonPositiveZeroIndex sigma)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖variableBoundaryVisibleWeightedPowerTerm H beta index m‖ ≤
      actualCarlsonPositiveZeroWeight index := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (variableBoundaryVisibleWeightedPowerTerm_nonneg H beta index m)]
  by_cases hvis :
      |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ)
  · by_cases hmem :
        actualCarlsonPositiveZero index ∈
          variableBoundaryZeroPackage H beta (m : ℝ)
    · simp [variableBoundaryVisibleWeightedPowerTerm, hvis, hmem,
        actualCarlsonPositiveZeroWeight_nonneg index]
    · simp only [variableBoundaryVisibleWeightedPowerTerm, hvis, hmem,
        if_true, if_false]
      have hre := hright m index hvis
      have hlog : 0 ≤ Real.log (m : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hm)
      have hexponent :
          (actualCarlsonPositiveZeroRealPart index - beta (m : ℝ)) *
              Real.log (m : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hre) hlog
      have hratio :
          pntPowerLayerToTargetRatio (beta (m : ℝ))
              (actualCarlsonPositiveZeroRealPart index) m ≤ 1 := by
        unfold pntPowerLayerToTargetRatio
        exact Real.exp_le_one_iff.mpr hexponent
      simpa using mul_le_mul_of_nonneg_left hratio
        (actualCarlsonPositiveZeroWeight_nonneg index)
  · simp [variableBoundaryVisibleWeightedPowerTerm, hvis,
      actualCarlsonPositiveZeroWeight_nonneg index]

/-- The complete visible weighted Carlson tail tends to zero at a moving
boundary under pointwise right-edge and absorption-or-gap. -/
theorem variableBoundaryVisibleWeightedPowerTail_tendsto_zero
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hright : IsIndexedVariableBoundaryVisibleRightEdge
      (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta) :
    Tendsto
      (fun m : ℕ =>
        ∑' index : ActualCarlsonPositiveZeroIndex sigma,
          variableBoundaryVisibleWeightedPowerTerm H beta index m)
      atTop (nhds 0) := by
  have hpoint :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        Tendsto
          (variableBoundaryVisibleWeightedPowerTerm H beta index)
          atTop (nhds 0) :=
    variableBoundaryVisibleWeightedPowerTerm_tendsto_zero hgap
  have hbound :
      ∀ᶠ m : ℕ in atTop,
        ∀ index : ActualCarlsonPositiveZeroIndex sigma,
          ‖variableBoundaryVisibleWeightedPowerTerm H beta index m‖ ≤
            actualCarlsonPositiveZeroWeight index := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm index
    exact norm_variableBoundaryVisibleWeightedPowerTerm_le hright index hm
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence
      (summable_actualCarlsonPositiveZeroWeight hhalf hone)
      hpoint hbound

/-- Sum of norms of currently visible actual zeta kernels outside the moving
boundary package, normalized by the variable target amplitude. -/
def variableBoundaryVisibleNormalizedKernelTail
    {sigma : ℝ} (H beta : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∑' index : ActualCarlsonPositiveZeroIndex sigma,
    if |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ) then
      if actualCarlsonPositiveZero index ∈
          variableBoundaryZeroPackage H beta (m : ℝ) then
        0
      else
        ‖pntRelativeZeroContribution (m : ℝ)
            (actualCarlsonPositiveZero index)‖ /
          variableBoundaryTargetAmplitude beta (m : ℝ)
    else
      0

/-- The actual visible zeta-kernel tail is negligible at the variable target
scale. -/
theorem variableBoundaryVisibleNormalizedKernelTail_tendsto_zero
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hright : IsIndexedVariableBoundaryVisibleRightEdge
      (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta) :
    Tendsto
      (variableBoundaryVisibleNormalizedKernelTail
        (sigma := sigma) H beta)
      atTop (nhds 0) := by
  apply
    (variableBoundaryVisibleWeightedPowerTail_tendsto_zero
      hhalf hone hright hgap).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  apply tsum_congr
  intro index
  by_cases hvis :
      |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ)
  · by_cases hmem :
        actualCarlsonPositiveZero index ∈
          variableBoundaryZeroPackage H beta (m : ℝ)
    · simp [variableBoundaryVisibleWeightedPowerTerm, hvis, hmem]
    · simp only [variableBoundaryVisibleWeightedPowerTerm, hvis, hmem,
        if_true, if_false]
      simpa [variableBoundaryTargetAmplitude] using
        (normalized_actualCarlsonPositiveZeroKernel_eq_weightedPower
          (beta := beta (m : ℝ)) index (Nat.zero_lt_of_lt hm)).symm
  · simp [variableBoundaryVisibleWeightedPowerTerm, hvis]

end
end PrimeNumberTheorem
