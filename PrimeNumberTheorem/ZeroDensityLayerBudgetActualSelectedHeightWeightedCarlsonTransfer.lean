import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedExponent
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStrips

/-!
# Actual Carlson transfer at the weighted balanced height

The slope-weighted optimizer supplies a positive physical margin `δ*` and
endpoint exponents at most `-δ*`.  Choosing the explicit slack `δ* / 2`
therefore discharges every strict Carlson strip hypothesis uniformly.
-/

namespace PrimeNumberTheorem

open Filter

noncomputable section

/-- Polynomial height schedule selected by the slope-weighted finite-strip
optimizer. -/
noncomputable def actualSelectedHeightFiniteStripWeightedBalancedHeight
    {n : ℕ}
    (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ)
    (x : ℝ) : ℝ :=
  carlsonPolynomialHeight
    (actualSelectedHeightFiniteStripWeightedBalancedExponent
      beta sigma tau)
    x

/-- A single actual zeta strip automatically receives a Carlson target-layer
budget at the weighted balanced height, with uniform slack `δ* / 2`. -/
theorem actualZetaStrip_weightedBalancedHeight_carlsonTargetLayerBudget
    {beta : ℝ}
    {n : ℕ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau x)
          (n + 1))
    (i : Fin (n + 1))
    (hfixedSigma : ∀ x, (input x).sigma i = sigma i)
    (hkappa : 0 < kappa i)
    (hnorm : ∀ x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre : ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    PintzCarlsonTargetLayerBudget
      (targetZeroPowerAmplitude beta)
      (dynamicPositivePNTLayerNorm
        (actualSelectedHeightFiniteStripWeightedBalancedHeight
          beta sigma tau)
        input i)
      (dynamicCarlsonLayerCount (sigma i)
        (actualSelectedHeightFiniteStripWeightedBalancedHeight
          beta sigma tau))
      (stripEndpointRelativeKernelBudget (kappa i) (tau i)) := by
  let delta :=
    actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have hdelta : 0 < delta := hspec.1
  have halpha : 0 < alpha := hspec.2.1
  have hendpoint :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_endpointExponent_le
      (beta := beta) sigma tau hsigma hsigmaOne i
  have hmargin :
      targetAmplitudeStripEndpointExponent beta (tau i)
          (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) +
          delta / 2 < 0 := by
    dsimp [alpha, delta] at hendpoint ⊢
    linarith
  simpa [actualSelectedHeightFiniteStripWeightedBalancedHeight, alpha] using
    (actualZetaStrip_carlsonTargetLayerBudget
      (beta := beta) (sigma := sigma i) (tau := tau i)
      (alpha := alpha) (kappa := kappa i) (epsilon := delta / 2)
      input i hfixedSigma (hsigma i) (hsigmaOne i) halpha hkappa
      hnorm hre (by linarith) hmargin)

/-- The actual outside-cluster finite strip norm sum is target-negligible at
the slope-weighted balanced height. -/
theorem
    actualZetaFiniteStripsOutsideCluster_weightedBalancedHeight_layerNormSum_negligible
    {beta : ℝ}
    {n : ℕ}
    {S : Finset ℂ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau x)
          S (n + 1))
    (hfixedSigma :
      ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm : ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre : ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        ∑ i,
          dynamicPositiveOutsideClusterPNTLayerNorm
            (actualSelectedHeightFiniteStripWeightedBalancedHeight
              beta sigma tau)
            S input i x) := by
  let delta :=
    actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have hdelta : 0 < delta := hspec.1
  have halpha : 0 < alpha := hspec.2.1
  have hheight :
      ∀ᶠ x in atTop,
        actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau x ≤
          carlsonPolynomialHeight alpha x := by
    filter_upwards with x
    simp [actualSelectedHeightFiniteStripWeightedBalancedHeight, alpha]
  have hepsilon : ∀ i : Fin (n + 1), 0 < delta / 2 := by
    intro i
    linarith
  have hmargin :
      ∀ i,
        targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) +
            delta / 2 < 0 := by
    intro i
    have hi :=
      actualSelectedHeightFiniteStripWeightedBalancedExponent_endpointExponent_le
        (beta := beta) sigma tau hsigma hsigmaOne i
    dsimp [alpha, delta] at hi ⊢
    linarith
  exact
    actualZetaFiniteStripsOutsideCluster_selectedHeight_layerNormSum_negligible
      input sigma tau kappa (fun _ => delta / 2) hfixedSigma hheight
      hsigma hsigmaOne halpha hkappa hnorm hre hepsilon hmargin

end

end PrimeNumberTheorem
