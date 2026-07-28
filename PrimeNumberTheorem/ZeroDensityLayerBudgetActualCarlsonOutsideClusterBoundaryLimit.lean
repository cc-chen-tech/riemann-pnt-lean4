import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonOutsideClusterKernelTail
import PrimeNumberTheorem.ZeroDensityLayerBudgetWeightedPowerBoundaryLimit

/-!
# Actual Carlson outside-cluster boundary limit

The actual multiplicity-weighted zeta kernel tail need not be negligible when
zeros on the target line `Re rho = beta` remain outside the finite cluster.
Under the weaker pointwise condition `Re rho <= beta`, its exact normalized
limit is the Carlson-summable coefficient mass on that boundary line.

This separates the decaying strict-left tail from the genuinely persistent
rightmost layer without imposing a uniform real-part gap.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

/-- Carlson coefficient mass outside `S` whose effective real part is exactly
the target exponent. -/
def actualCarlsonOutsideClusterBoundaryMass
    {sigma : ℝ} (beta : ℝ) (S : Finset ℂ) : ℝ :=
  weightedPowerBoundaryMass beta
    (@actualCarlsonOutsideClusterWeight sigma S)
    (actualCarlsonOutsideClusterRealPart beta S)

theorem actualCarlsonOutsideClusterRealPart_le
    {sigma beta : ℝ} (S : Finset ℂ)
    (hre :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (index : ActualCarlsonPositiveZeroIndex sigma) :
    actualCarlsonOutsideClusterRealPart beta S index ≤ beta := by
  by_cases hmem : actualCarlsonPositiveZero index ∈ S
  · simp [actualCarlsonOutsideClusterRealPart, hmem]
  · simpa [actualCarlsonOutsideClusterRealPart, hmem] using hre index hmem

/-- Exact normalized limit of the actual positive-zero Carlson kernel tail
when outside-cluster zeros may lie on, but not to the right of, `Re rho =
beta`. -/
theorem actualCarlsonOutsideClusterNormalizedKernelTail_tendsto_boundaryMass
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hre :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) :
    Tendsto
      (actualCarlsonOutsideClusterNormalizedKernelTail
        (sigma := sigma) beta S)
      atTop
      (𝓝 (actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S)) := by
  have hmodel :=
    weightedPowerLayers_tendsto_boundaryMass_of_summable
      (summable_actualCarlsonOutsideClusterWeight S hhalf hone)
      (actualCarlsonOutsideClusterWeight_nonneg S)
      (actualCarlsonOutsideClusterRealPart_le S hre)
  apply hmodel.congr'
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

/-- The previous strict-gap limit is recovered because its boundary mass
vanishes. -/
theorem actualCarlsonOutsideClusterBoundaryMass_eq_zero_of_lt
    {sigma beta : ℝ} (S : Finset ℂ)
    (hre :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index < beta) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S = 0 := by
  apply weightedPowerBoundaryMass_eq_zero_of_lt
  exact actualCarlsonOutsideClusterRealPart_lt S hre

end

end PrimeNumberTheorem
