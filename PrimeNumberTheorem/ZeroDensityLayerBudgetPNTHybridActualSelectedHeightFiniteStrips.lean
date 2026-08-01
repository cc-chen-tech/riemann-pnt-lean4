import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualSelectedHeightLowLayer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightCarlsonTransfer

/-!
# Actual hybrid finite strips at the optimized selected height

This file combines the two actual selected-height estimates at the mixed
global/Carlson minimax height:

* thresholds at most `1 / 2` use the global zero-counting theorem;
* thresholds greater than `1 / 2` use Carlson's density theorem.

The optimal mixed affine certificate supplies one common positive margin.
Half of that margin absorbs the logarithmic factors in both branches.  The
result is then aggregated from individual layers to the complete positive
tail and, given the real-ordinate residual, to the full finite zero tail.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace PrimeNumberTheorem

/-- The mixed affine certificate gives the required low-layer exponent
margin, with half of the optimal physical margin left for logarithms. -/
theorem pntHybridAffineSelectedHeight_lowLayer_margin
    {n : ℕ} {beta : ℝ}
    {sigma tau : Fin (n + 1) → ℝ}
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hdelta : 0 < pntHybridAffineOptimalMargin beta sigma tau)
    {i : Fin (n + 1)} (hlow : sigma i ≤ 1 / 2) :
    tau i - beta +
          pntHybridAffineBalancedExponent beta sigma tau +
          pntHybridAffineOptimalMargin beta sigma tau / 2 <
        0 := by
  have hlow' : sigma i ≤ (2 : ℝ)⁻¹ := by
    norm_num at hlow ⊢
    exact hlow
  have hstrip :=
    (pntHybridAffineBalancedExponent_marginCertificate
      beta sigma tau hsigmaOneHigh).strip i
  simp [pntHybridAffineDensityCeiling, pntHybridAffineDensitySlope, hlow'] at hstrip
  linarith

/-- The same mixed certificate gives the Carlson endpoint margin on every
high-threshold layer. -/
theorem pntHybridAffineSelectedHeight_highLayer_margin
    {n : ℕ} {beta : ℝ}
    {sigma tau : Fin (n + 1) → ℝ}
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hdelta : 0 < pntHybridAffineOptimalMargin beta sigma tau)
    {i : Fin (n + 1)} (hhigh : 1 / 2 < sigma i) :
    targetAmplitudeStripEndpointExponent beta (tau i)
          (carlsonClassicalPolynomialDensityExponent
            (pntHybridAffineBalancedExponent beta sigma tau) (sigma i)) +
        pntHybridAffineOptimalMargin beta sigma tau / 2 <
      0 := by
  have hnotLow : ¬ sigma i ≤ 1 / 2 :=
    not_le.mpr hhigh
  have hnotLow' : ¬ sigma i ≤ (2 : ℝ)⁻¹ := by
    norm_num at hnotLow ⊢
    exact hnotLow
  have hstrip :=
    (pntHybridAffineBalancedExponent_marginCertificate
      beta sigma tau hsigmaOneHigh).strip i
  simp [pntHybridAffineDensityCeiling, pntHybridAffineDensitySlope, hnotLow',
    carlsonAffineDensitySlope, actualSelectedHeightStripCarlsonSlope,
    targetAmplitudeStripEndpointExponent,
    carlsonClassicalPolynomialDensityExponent,
    carlsonPolynomialHeightDensityExponent] at hstrip ⊢
  ring_nf at hstrip ⊢
  linarith

/-- Every actual outside-cluster layer is negligible at the target amplitude
at the automatically optimized selected height. -/
theorem
    actualHybridFiniteStripsOutsideCluster_optimizedSelectedHeight_eachLayer_negligible
    {n : ℕ} {S : Finset ℂ} {beta : ℝ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (pntHybridAffineSelectedGoodHeight
            beta sigma tau selection x) S (n + 1))
    (hbetaOne : beta < 1)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (i : Fin (n + 1)) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTLayerNorm
        (pntHybridAffineSelectedGoodHeight beta sigma tau selection)
        S input i) := by
  let alpha := pntHybridAffineBalancedExponent beta sigma tau
  have halpha : 0 < alpha := by
    exact pntHybridAffineBalancedExponent_pos
      hbetaOne hsigmaOneHigh hbudget
  have hdelta :
      0 < pntHybridAffineOptimalMargin beta sigma tau :=
    pntHybridAffineOptimalMargin_pos hsigmaOneHigh hbudget
  have hheight :
      ∀ᶠ x : ℝ in atTop,
        pntHybridAffineSelectedGoodHeight beta sigma tau selection x ≤
          carlsonPolynomialHeight alpha x := by
    filter_upwards
      [eventually_selectedUniformGoodHeight_mem halpha selection] with x hx
    simpa [alpha, pntHybridAffineSelectedGoodHeight,
      carlsonPolynomialHeight] using hx.2
  have hheightTop :
      Tendsto
        (pntHybridAffineSelectedGoodHeight beta sigma tau selection)
        atTop atTop :=
    pntHybridAffineSelectedGoodHeight_tendsto_atTop
      sigma tau hbetaOne hsigmaOneHigh hbudget selection
  by_cases hlow : sigma i ≤ 1 / 2
  · exact
      actualHybridOutsideClusterLowLayer_selectedHeight_targetAmplitudeNegligible
        input i hheight hheightTop (hkappa i) (hnorm i) (hre i)
        halpha (half_pos hdelta)
        (pntHybridAffineSelectedHeight_lowLayer_margin
          hsigmaOneHigh hdelta hlow)
  · have hhigh : 1 / 2 < sigma i :=
      lt_of_not_ge hlow
    have hhighMem :
        i ∈ pintzCarlsonHighDensityIndices sigma :=
      mem_pintzCarlsonHighDensityIndices.mpr hhigh
    exact
      PintzCarlsonTargetLayerBudget.targetAmplitudeNegligible
        (targetZeroPowerAmplitude_eventually_pos beta)
        (actualZetaOutsideClusterStrip_selectedHeight_carlsonTargetLayerBudget
          input i (hfixedSigma i) hheight hhigh
          (hsigmaOneHigh i hhighMem) halpha
          (hkappa i) (hnorm i) (hre i)
          (half_pos hdelta)
          (pntHybridAffineSelectedHeight_highLayer_margin
            hsigmaOneHigh hdelta hhigh))

/-- The sum of all actual mixed-profile layer norms is negligible at the
target amplitude at the optimized selected height. -/
theorem
    actualHybridFiniteStripsOutsideCluster_optimizedSelectedHeight_layerSum_negligible
    {n : ℕ} {S : Finset ℂ} {beta : ℝ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (pntHybridAffineSelectedGoodHeight
            beta sigma tau selection x) S (n + 1))
    (hbetaOne : beta < 1)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        ∑ i : Fin (n + 1),
          dynamicPositiveOutsideClusterPNTLayerNorm
            (pntHybridAffineSelectedGoodHeight
              beta sigma tau selection) S input i x) := by
  simpa using
    targetAmplitudeNegligible_finset_sum
      (targetZeroPowerAmplitude_eventually_pos beta)
      (Finset.univ : Finset (Fin (n + 1)))
      (fun i =>
        dynamicPositiveOutsideClusterPNTLayerNorm
          (pntHybridAffineSelectedGoodHeight beta sigma tau selection)
          S input i)
      (by
        intro i hi
        exact
          actualHybridFiniteStripsOutsideCluster_optimizedSelectedHeight_eachLayer_negligible
            sigma tau kappa selection input hbetaOne hfixedSigma
            hsigmaOneHigh hbudget hkappa hnorm hre i)

/-- The actual positive-ordinate outside-cluster tail is negligible at the
target amplitude at the optimized selected height. -/
theorem
    actualHybridFiniteStripsOutsideCluster_optimizedSelectedHeight_positiveTail_negligible
    {n : ℕ} {S : Finset ℂ} {beta : ℝ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (pntHybridAffineSelectedGoodHeight
            beta sigma tau selection x) S (n + 1))
    (hbetaOne : beta < 1)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTTailNorm
        (pntHybridAffineSelectedGoodHeight beta sigma tau selection) S) := by
  have hsum :=
    actualHybridFiniteStripsOutsideCluster_optimizedSelectedHeight_layerSum_negligible
      sigma tau kappa selection input hbetaOne hfixedSigma
      hsigmaOneHigh hbudget hkappa hnorm hre
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
          (pntHybridAffineSelectedGoodHeight beta sigma tau selection) S x :=
      norm_nonneg _
    have hsumNonneg :
        0 ≤ ∑ i : Fin (n + 1),
          dynamicPositiveOutsideClusterPNTLayerNorm
            (pntHybridAffineSelectedGoodHeight
              beta sigma tau selection) S input i x :=
      Finset.sum_nonneg fun i hi => norm_nonneg _
    rw [abs_of_nonneg htailNonneg, abs_of_nonneg hsumNonneg]
    exact div_le_div_of_nonneg_right htail hx.le

/-- Mixed selected-height layers plus the real-ordinate residual control the
full actual outside-cluster finite zero tail. -/
theorem
    actualHybridFiniteStripsOutsideCluster_optimizedSelectedHeight_fullTail_negligible
    {n : ℕ} {S : Finset ℂ} {beta : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (pntHybridAffineSelectedGoodHeight
            beta sigma tau selection x) S (n + 1))
    (hbetaOne : beta < 1)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicRealOrdinateOutsideClusterPNTZeroTailNorm
          (pntHybridAffineSelectedGoodHeight
            beta sigma tau selection) S)) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (pntHybridAffineSelectedGoodHeight beta sigma tau selection) S) := by
  apply
    dynamicFullOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      hS (targetZeroPowerAmplitude_eventually_pos beta)
  · exact
      actualHybridFiniteStripsOutsideCluster_optimizedSelectedHeight_positiveTail_negligible
        sigma tau kappa selection input hbetaOne hfixedSigma
        hsigmaOneHigh hbudget hkappa hnorm hre
  · exact hreal

end PrimeNumberTheorem
