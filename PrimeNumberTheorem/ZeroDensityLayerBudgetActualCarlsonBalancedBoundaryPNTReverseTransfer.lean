import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedPNTReverseTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedPNTSignedReverseTransfer

/-!
# Reverse PNT transfer with Carlson boundary mass

An eventual actual-PNT bound excludes a nonempty visible cluster only after the
coefficient contributed by zeros on `Re rho = beta` is deducted.  The exact
strict range is `q < c - 2 * boundaryMass`.

The visible-cluster witnesses remain external hypotheses.
-/

open scoped Topology
open Filter

namespace PrimeNumberTheorem

open Complex

/-- An eventual two-sided actual-PNT bound excludes a nonempty visible cluster
whose witness coefficient dominates both the PNT bound and twice the Carlson
boundary mass. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTEventualUpper_forces_emptyCluster_automatic
    {S : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (_hq : 0 ≤ q)
    (hqNet :
      q <
        c -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S)
    (hupper :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| ≤
          q * targetZeroPowerAmplitude beta (m : ℝ))
    (hmain :
      S.Nonempty →
        HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    S = ∅ := by
  by_contra hEmpty
  have hNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  let boundary :=
    actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S
  let delta := (c - q - 2 * boundary) / 2
  have hdelta : 0 < delta := by
    dsimp [delta, boundary]
    linarith
  have happrox :=
    eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
      selection hS hhalf hone hbalance hreHigh hreReal hdelta
  have hwitness :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m =>
          (c - (2 * boundary + delta)) *
            targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmain hNonempty).transfer_eventually_sub_lt happrox
  have hqTransferred : q < c - (2 * boundary + delta) := by
    dsimp [delta, boundary]
    linarith
  exact
    (not_hasFarNaturalPoint_mul_of_eventually_abs_le_mul
      hupper
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      hqTransferred)
      hwitness

/-- An eventual one-sided actual-PNT upper bound excludes a nonempty visible
cluster with a sufficiently strong positive witness. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTEventualUpper_forces_emptyCluster_of_positiveWitness_automatic
    {S : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (_hq : 0 ≤ q)
    (hqNet :
      q <
        c -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S)
    (hupper :
      ∀ᶠ m : ℕ in atTop,
        relativeChebyshevPsi0Error (m : ℝ) ≤
          q * targetZeroPowerAmplitude beta (m : ℝ))
    (hmainPos :
      S.Nonempty →
        HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    S = ∅ := by
  by_contra hEmpty
  have hNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  let boundary :=
    actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S
  let delta := (c - q - 2 * boundary) / 2
  have hdelta : 0 < delta := by
    dsimp [delta, boundary]
    linarith
  have happrox :=
    eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
      selection hS hhalf hone hbalance hreHigh hreReal hdelta
  have hwitness :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m =>
          (c - (2 * boundary + delta)) *
            targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmainPos hNonempty).transfer_eventually_sub_lt happrox
  have hqTransferred : q < c - (2 * boundary + delta) := by
    dsimp [delta, boundary]
    linarith
  exact
    (not_hasFarNaturalPointPositive_mul_of_eventually_le_mul
      hupper
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      hqTransferred)
      hwitness

/-- An eventual one-sided actual-PNT lower bound excludes a nonempty visible
cluster with a sufficiently strong negative witness. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTEventualLower_forces_emptyCluster_of_negativeWitness_automatic
    {S : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (_hq : 0 ≤ q)
    (hqNet :
      q <
        c -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S)
    (hlower :
      ∀ᶠ m : ℕ in atTop,
        -(q * targetZeroPowerAmplitude beta (m : ℝ)) ≤
          relativeChebyshevPsi0Error (m : ℝ))
    (hmainNeg :
      S.Nonempty →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    S = ∅ := by
  by_contra hEmpty
  have hNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  let boundary :=
    actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S
  let delta := (c - q - 2 * boundary) / 2
  have hdelta : 0 < delta := by
    dsimp [delta, boundary]
    linarith
  have happrox :=
    eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
      selection hS hhalf hone hbalance hreHigh hreReal hdelta
  have hwitness :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m =>
          (c - (2 * boundary + delta)) *
            targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmainNeg hNonempty).transfer_eventually_sub_lt happrox
  have hqTransferred : q < c - (2 * boundary + delta) := by
    dsimp [delta, boundary]
    linarith
  exact
    (not_hasFarNaturalPointNegative_mul_of_eventually_neg_mul_le
      hlower
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      hqTransferred)
      hwitness

end PrimeNumberTheorem
