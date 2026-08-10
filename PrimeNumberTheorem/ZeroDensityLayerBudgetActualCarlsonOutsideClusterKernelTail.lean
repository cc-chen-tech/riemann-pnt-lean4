import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPositiveZeroTail
import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzKernelAutomatic

/-!
# Actual Carlson outside-cluster kernel tails

This file identifies the weighted Carlson power tail with the norm of the
actual multiplicity-weighted zeta zero kernel, after normalization by the
target relative amplitude `x^(beta - 1)`.

A finite main cluster is removed by assigning its members weight zero.  The
strict real-part hypothesis is imposed only outside that cluster.  Thus this
module does not assume that a target zero lies strictly to the left of itself,
and it does not hide same-real-part cancellation inside a density estimate.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

theorem pntPowerLayerToTargetRatio_eq_rpow {beta tau : ℝ} {m : ℕ}
    (hm : 0 < m) :
    pntPowerLayerToTargetRatio beta tau m =
      (m : ℝ) ^ (tau - beta) := by
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hm)]
  simp [pntPowerLayerToTargetRatio, mul_comm]

/-- Exact target-amplitude normalization of one actual zeta zero kernel. -/
theorem norm_pntRelativeZeroContribution_div_targetAmplitude_eq
    {x beta : ℝ} (hx : 0 < x) (rho : ℂ) :
    ‖pntRelativeZeroContribution x rho‖ / x ^ (beta - 1) =
      ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
        x ^ (rho.re - beta) := by
  rw [norm_pntRelativeZeroContribution_eq_multiplicity_mul_norm,
    norm_pntRelativeSimpleZeroKernel_eq hx]
  calc
    (analyticOrderNatAt riemannZeta rho : ℝ) *
          (x ^ (rho.re - 1) / ‖rho‖) / x ^ (beta - 1) =
        ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
          (x ^ (rho.re - 1) / x ^ (beta - 1)) := by ring
    _ = ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
          x ^ ((rho.re - 1) - (beta - 1)) := by
        rw [Real.rpow_sub hx (rho.re - 1) (beta - 1)]
    _ = ((analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) *
          x ^ (rho.re - beta) := by ring_nf

theorem normalized_actualCarlsonPositiveZeroKernel_eq_weightedPower
    {sigma beta : ℝ} (index : ActualCarlsonPositiveZeroIndex sigma)
    {m : ℕ} (hm : 0 < m) :
    ‖pntRelativeZeroContribution (m : ℝ)
        (actualCarlsonPositiveZero index)‖ /
          (m : ℝ) ^ (beta - 1) =
      actualCarlsonPositiveZeroWeight index *
        pntPowerLayerToTargetRatio beta
          (actualCarlsonPositiveZeroRealPart index) m := by
  rw [pntPowerLayerToTargetRatio_eq_rpow hm]
  rw [norm_pntRelativeZeroContribution_div_targetAmplitude_eq
    (Nat.cast_pos.mpr hm)]
  cases index <;>
    simp [actualCarlsonPositiveZeroWeight,
      actualCarlsonPositiveZeroRealPart, actualCarlsonPositiveZero,
      actualCarlsonDyadicZeroWeight, actualCarlsonDyadicZeroRealPart]

/-- The true coefficient weight after deleting a finite main cluster. -/
def actualCarlsonOutsideClusterWeight {sigma : ℝ} (S : Finset ℂ)
    (index : ActualCarlsonPositiveZeroIndex sigma) : ℝ :=
  if actualCarlsonPositiveZero index ∈ S then 0
  else actualCarlsonPositiveZeroWeight index

/-- The exponent used by dominated convergence.  Cluster members have zero
weight, so their harmless placeholder exponent is `beta - 1`. -/
def actualCarlsonOutsideClusterRealPart {sigma : ℝ} (beta : ℝ) (S : Finset ℂ)
    (index : ActualCarlsonPositiveZeroIndex sigma) : ℝ :=
  if actualCarlsonPositiveZero index ∈ S then beta - 1
  else actualCarlsonPositiveZeroRealPart index

theorem actualCarlsonOutsideClusterWeight_nonneg {sigma : ℝ}
    (S : Finset ℂ) (index : ActualCarlsonPositiveZeroIndex sigma) :
    0 ≤ actualCarlsonOutsideClusterWeight S index := by
  by_cases hmem : actualCarlsonPositiveZero index ∈ S
  · simp [actualCarlsonOutsideClusterWeight, hmem]
  · simp [actualCarlsonOutsideClusterWeight, hmem,
      actualCarlsonPositiveZeroWeight_nonneg index]

theorem summable_actualCarlsonOutsideClusterWeight {sigma : ℝ}
    (S : Finset ℂ) (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable (@actualCarlsonOutsideClusterWeight sigma S) := by
  refine Summable.of_nonneg_of_le
    (actualCarlsonOutsideClusterWeight_nonneg S) ?_
    (summable_actualCarlsonPositiveZeroWeight hhalf hone)
  intro index
  by_cases hmem : actualCarlsonPositiveZero index ∈ S
  · simp [actualCarlsonOutsideClusterWeight, hmem,
      actualCarlsonPositiveZeroWeight_nonneg index]
  · simp [actualCarlsonOutsideClusterWeight, hmem]

theorem actualCarlsonOutsideClusterRealPart_lt {sigma beta : ℝ}
    (S : Finset ℂ)
    (hre : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index < beta)
    (index : ActualCarlsonPositiveZeroIndex sigma) :
    actualCarlsonOutsideClusterRealPart beta S index < beta := by
  by_cases hmem : actualCarlsonPositiveZero index ∈ S
  · simp [actualCarlsonOutsideClusterRealPart, hmem]
  · simpa [actualCarlsonOutsideClusterRealPart, hmem] using hre index hmem

/-- The outside-cluster weighted model tail tends to zero with only pointwise
strict real-part separation. -/
theorem actualCarlsonOutsideClusterWeightedPowerTail_tendsto_zero
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hre : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index < beta) :
    Tendsto
      (fun m : ℕ =>
        ∑' index : ActualCarlsonPositiveZeroIndex sigma,
          actualCarlsonOutsideClusterWeight S index *
            pntPowerLayerToTargetRatio beta
              (actualCarlsonOutsideClusterRealPart beta S index) m)
      atTop (nhds 0) :=
  weightedPowerLayers_tendsto_zero_of_summable
    (summable_actualCarlsonOutsideClusterWeight S hhalf hone)
    (actualCarlsonOutsideClusterWeight_nonneg S)
    (actualCarlsonOutsideClusterRealPart_lt S hre)

/-- Sum of norms of the actual outside-cluster zeta kernels, normalized by the
target relative amplitude. -/
def actualCarlsonOutsideClusterNormalizedKernelTail
    {sigma : ℝ} (beta : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  ∑' index : ActualCarlsonPositiveZeroIndex sigma,
    if actualCarlsonPositiveZero index ∈ S then 0
    else
      ‖pntRelativeZeroContribution (m : ℝ)
        (actualCarlsonPositiveZero index)‖ / (m : ℝ) ^ (beta - 1)

theorem actualCarlsonOutsideClusterNormalizedKernelTail_tendsto_zero
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hre : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index < beta) :
    Tendsto
      (actualCarlsonOutsideClusterNormalizedKernelTail
        (sigma := sigma) beta S)
      atTop (nhds 0) := by
  apply
    (actualCarlsonOutsideClusterWeightedPowerTail_tendsto_zero
      S hhalf hone hre).congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hm
  apply tsum_congr
  intro index
  by_cases hmem : actualCarlsonPositiveZero index ∈ S
  · simp [actualCarlsonOutsideClusterNormalizedKernelTail,
      actualCarlsonOutsideClusterWeight,
      actualCarlsonOutsideClusterRealPart, hmem]
  · simp only [actualCarlsonOutsideClusterNormalizedKernelTail,
      actualCarlsonOutsideClusterWeight,
      actualCarlsonOutsideClusterRealPart, hmem, if_false]
    exact
      (normalized_actualCarlsonPositiveZeroKernel_eq_weightedPower
        index (Nat.zero_lt_of_lt hm)).symm

end

end PrimeNumberTheorem
