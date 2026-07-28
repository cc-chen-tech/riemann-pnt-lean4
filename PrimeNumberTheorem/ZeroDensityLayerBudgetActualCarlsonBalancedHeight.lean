import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonCanonicalTwoStripAutomaticNorm

/-!
# Balanced selected height for the pointwise-gap Carlson transfer

The selected-height explicit formula imposes two competing strict conditions:

* contour decay: `1 - beta < alpha`;
* canonical low-strip decay: `alpha < beta - sigma`.

Their midpoint is

`alpha = (1 - sigma) / 2`,

and it maximizes the smaller of the two margins.  The interval is nonempty
exactly in the strict regime `(1 + sigma) / 2 < beta`.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Midpoint exponent balancing contour and low-strip decay. -/
noncomputable def actualCarlsonBalancedHeightExponent (sigma : ℝ) : ℝ :=
  (1 - sigma) / 2

/-- Half of the remaining balanced strict margin, used as the low-strip
epsilon loss. -/
noncomputable def actualCarlsonBalancedEpsilon (beta sigma : ℝ) : ℝ :=
  (2 * beta - 1 - sigma) / 4

/-- The smaller of the contour and low-strip margins at a candidate height
exponent. -/
def actualCarlsonHeightRobustMargin
    (beta sigma alpha : ℝ) : ℝ :=
  min (alpha - (1 - beta)) ((beta - sigma) - alpha)

theorem actualCarlsonBalancedHeightExponent_contour_margin
    {beta sigma : ℝ} (hbalance : (1 + sigma) / 2 < beta) :
    1 - beta < actualCarlsonBalancedHeightExponent sigma := by
  unfold actualCarlsonBalancedHeightExponent
  linarith

theorem actualCarlsonBalancedHeightExponent_low_margin
    {beta sigma : ℝ} (hbalance : (1 + sigma) / 2 < beta) :
    actualCarlsonBalancedHeightExponent sigma < beta - sigma := by
  unfold actualCarlsonBalancedHeightExponent
  linarith

theorem actualCarlsonBalancedEpsilon_pos
    {beta sigma : ℝ} (hbalance : (1 + sigma) / 2 < beta) :
    0 < actualCarlsonBalancedEpsilon beta sigma := by
  unfold actualCarlsonBalancedEpsilon
  linarith

theorem actualCarlsonBalancedHeight_low_margin_with_epsilon
    {beta sigma : ℝ} (hbalance : (1 + sigma) / 2 < beta) :
    sigma - beta + actualCarlsonBalancedHeightExponent sigma +
        actualCarlsonBalancedEpsilon beta sigma <
      0 := by
  unfold actualCarlsonBalancedHeightExponent actualCarlsonBalancedEpsilon
  linarith

/-- No candidate exponent has a larger minimum two-sided margin than the
midpoint exponent. -/
theorem actualCarlsonHeightRobustMargin_le_balanced
    (beta sigma alpha : ℝ) :
    actualCarlsonHeightRobustMargin beta sigma alpha ≤
      (2 * beta - 1 - sigma) / 2 := by
  unfold actualCarlsonHeightRobustMargin
  have hleft :=
    min_le_left (alpha - (1 - beta)) ((beta - sigma) - alpha)
  have hright :=
    min_le_right (alpha - (1 - beta)) ((beta - sigma) - alpha)
  linarith

theorem actualCarlsonHeightRobustMargin_balanced
    (beta sigma : ℝ) :
    actualCarlsonHeightRobustMargin beta sigma
        (actualCarlsonBalancedHeightExponent sigma) =
      (2 * beta - 1 - sigma) / 2 := by
  unfold actualCarlsonHeightRobustMargin
    actualCarlsonBalancedHeightExponent
  rw [min_eq_left]
  · ring
  · ring_nf
    exact le_rfl

/-- Fully automatic canonical two-strip PNT residual transfer at the balanced
height exponent.  Apart from the explicit feasibility inequality, only the
cluster symmetry and pointwise outside-cluster real-part gaps remain. -/
theorem selectedUniformGoodHeightActualCarlsonBalancedPNTClusterResidual_automatic
    {S : Finset ℂ} {sigma beta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ)) := by
  have hbeta : 0 < beta := by linarith
  have halpha : 0 < actualCarlsonBalancedHeightExponent sigma := by
    unfold actualCarlsonBalancedHeightExponent
    linarith
  have halphaOne : actualCarlsonBalancedHeightExponent sigma ≤ 1 := by
    unfold actualCarlsonBalancedHeightExponent
    linarith
  exact
    selectedUniformGoodHeightActualCarlsonCanonicalTwoStripPNTClusterResidual_automatic
      selection hS hbeta hhalf hone halpha halphaOne
      (actualCarlsonBalancedHeightExponent_contour_margin hbalance)
      (actualCarlsonBalancedEpsilon_pos hbalance)
      (actualCarlsonBalancedHeight_low_margin_with_epsilon hbalance)
      hreHigh hreReal

end PrimeNumberTheorem
