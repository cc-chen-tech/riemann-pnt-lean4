import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualLowLayerDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailExcludingClusterConjugation

/-!
# Finite hybrid global/Carlson control of the actual outside-cluster tail

The previous actual finite-strip transfer required every bucket threshold to
lie strictly right of `1 / 2`.  For a fixed finite main cluster and a cofinal
height, that requirement is inconsistent with critical-line reflection.

This file removes that structural obstruction.  Bucket indices are handled
according to their actual lower threshold:

* `sigma i <= 1 / 2`: use the global `O(T log T)` multiplicity bound and the
  low-layer exponent `tau i - beta + alpha`;
* `1 / 2 < sigma i`: use the multiplicity-weighted Carlson count.

Both classes retain the same actual endpoint zeta kernel, denominator guard,
target amplitude, and polynomial dynamic height.
-/

open scoped BigOperators
open Filter Topology

namespace PrimeNumberTheorem

/--
Every actual outside-cluster layer in a finite hybrid profile is negligible
at the target amplitude: low layers use global counting, high layers use
Carlson.
-/
theorem actualHybridFiniteStripsOutsideCluster_eachLayer_targetAmplitudeNegligible
    {n : ℕ} {S : Finset ℂ} {beta alpha : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma :
      ∀ i x, (input x).sigma i = sigma i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (halpha : 0 < alpha)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hepsilon : ∀ i, 0 < epsilon i)
    (hlowMargin :
      ∀ i ∈ pintzCarlsonLowDensityIndices sigma,
        tau i - beta + alpha + epsilon i < 0)
    (hhighMargin :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma,
        targetAmplitudeStripEndpointExponent beta (tau i)
              (carlsonClassicalPolynomialDensityExponent
                alpha (sigma i)) +
            epsilon i < 0)
    (i : Fin n) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTLayerNorm
        (carlsonPolynomialHeight alpha) S input i) := by
  by_cases hlow : sigma i ≤ 1 / 2
  · have hlowMem :
        i ∈ pintzCarlsonLowDensityIndices sigma :=
      mem_pintzCarlsonLowDensityIndices.mpr hlow
    have hlimit :=
      tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_of_hybrid
        input i (hkappa i) (hnorm i) (hre i) halpha
        (hepsilon i) (hlowMargin i hlowMem)
    unfold TargetAmplitudeNegligible
    convert hlimit using 1
  · have hhigh : 1 / 2 < sigma i :=
      lt_of_not_ge hlow
    have hhighMem :
        i ∈ pintzCarlsonHighDensityIndices sigma :=
      mem_pintzCarlsonHighDensityIndices.mpr hhigh
    exact
      PintzCarlsonTargetLayerBudget.targetAmplitudeNegligible
        (targetZeroPowerAmplitude_eventually_pos beta)
        (actualZetaOutsideClusterStrip_carlsonTargetLayerBudget
          input i (hfixedSigma i)
          hhigh (hsigmaOneHigh i hhighMem) halpha
          (hkappa i) (hnorm i) (hre i)
          (hepsilon i) (hhighMargin i hhighMem))

/-- The sum of all actual layer norms in a finite hybrid profile is negligible
at the target zero-power scale. -/
theorem actualHybridFiniteStripsOutsideCluster_layerNormSum_targetAmplitudeNegligible
    {n : ℕ} {S : Finset ℂ} {beta alpha : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma :
      ∀ i x, (input x).sigma i = sigma i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (halpha : 0 < alpha)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hepsilon : ∀ i, 0 < epsilon i)
    (hlowMargin :
      ∀ i ∈ pintzCarlsonLowDensityIndices sigma,
        tau i - beta + alpha + epsilon i < 0)
    (hhighMargin :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma,
        targetAmplitudeStripEndpointExponent beta (tau i)
              (carlsonClassicalPolynomialDensityExponent
                alpha (sigma i)) +
            epsilon i < 0) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        ∑ i : Fin n,
          dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) S input i x) := by
  simpa using
    targetAmplitudeNegligible_finset_sum
      (targetZeroPowerAmplitude_eventually_pos beta)
      (Finset.univ : Finset (Fin n))
      (fun i =>
        dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) S input i)
      (by
        intro i hi
        exact
          actualHybridFiniteStripsOutsideCluster_eachLayer_targetAmplitudeNegligible
            input sigma tau kappa epsilon hfixedSigma hsigmaOneHigh
            halpha hkappa hnorm hre hepsilon hlowMargin hhighMargin i)

/--
Finite hybrid global/Carlson layers control the complete positive-ordinate
outside-cluster tail.
-/
theorem actualHybridFiniteStripsOutsideCluster_positiveTail_targetAmplitudeNegligible
    {n : ℕ} {S : Finset ℂ} {beta alpha : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma :
      ∀ i x, (input x).sigma i = sigma i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (halpha : 0 < alpha)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hepsilon : ∀ i, 0 < epsilon i)
    (hlowMargin :
      ∀ i ∈ pintzCarlsonLowDensityIndices sigma,
        tau i - beta + alpha + epsilon i < 0)
    (hhighMargin :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma,
        targetAmplitudeStripEndpointExponent beta (tau i)
              (carlsonClassicalPolynomialDensityExponent
                alpha (sigma i)) +
            epsilon i < 0) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTTailNorm
        (carlsonPolynomialHeight alpha) S) := by
  have hsum :=
    actualHybridFiniteStripsOutsideCluster_layerNormSum_targetAmplitudeNegligible
      input sigma tau kappa epsilon hfixedSigma hsigmaOneHigh
      halpha hkappa hnorm hre hepsilon hlowMargin hhighMargin
  unfold TargetAmplitudeNegligible at hsum ⊢
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards
      [targetZeroPowerAmplitude_eventually_pos beta] with x hx
    exact div_nonneg (abs_nonneg _) hx.le
  · filter_upwards
      [targetZeroPowerAmplitude_eventually_pos beta] with x hx
    have htail :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms input x
    have htailNonneg :
        0 ≤ dynamicPositiveOutsideClusterPNTTailNorm
          (carlsonPolynomialHeight alpha) S x :=
      norm_nonneg _
    have hsumNonneg :
        0 ≤ ∑ i : Fin n,
          dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) S input i x :=
      Finset.sum_nonneg fun i hi => norm_nonneg _
    rw [abs_of_nonneg htailNonneg, abs_of_nonneg hsumNonneg]
    exact div_le_div_of_nonneg_right htail hx.le

/--
Finite hybrid layers plus the explicit real-ordinate residual control the
full outside-cluster finite zero tail.
-/
theorem actualHybridFiniteStripsOutsideCluster_fullTail_targetAmplitudeNegligible
    {n : ℕ} {S : Finset ℂ} {beta alpha : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma :
      ∀ i x, (input x).sigma i = sigma i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (halpha : 0 < alpha)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hepsilon : ∀ i, 0 < epsilon i)
    (hlowMargin :
      ∀ i ∈ pintzCarlsonLowDensityIndices sigma,
        tau i - beta + alpha + epsilon i < 0)
    (hhighMargin :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma,
        targetAmplitudeStripEndpointExponent beta (tau i)
              (carlsonClassicalPolynomialDensityExponent
                alpha (sigma i)) +
            epsilon i < 0)
    (hreal :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicRealOrdinateOutsideClusterPNTZeroTailNorm
          (carlsonPolynomialHeight alpha) S)) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (carlsonPolynomialHeight alpha) S) := by
  apply
    dynamicFullOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      hS (targetZeroPowerAmplitude_eventually_pos beta)
  · exact
      actualHybridFiniteStripsOutsideCluster_positiveTail_targetAmplitudeNegligible
        input sigma tau kappa epsilon hfixedSigma hsigmaOneHigh
        halpha hkappa hnorm hre hepsilon hlowMargin hhighMargin
  · exact hreal

end PrimeNumberTheorem
