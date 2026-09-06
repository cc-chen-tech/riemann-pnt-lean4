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
  change
    PintzCarlsonTargetLayerBudget
      (targetZeroPowerAmplitude beta)
      (dynamicPositivePNTLayerNorm
        (carlsonPolynomialHeight alpha) input i)
      (dynamicCarlsonLayerCount (sigma i)
        (carlsonPolynomialHeight alpha))
      (stripEndpointRelativeKernelBudget (kappa i) (tau i))
  exact actualZetaStrip_carlsonTargetLayerBudget
    (beta := beta) (sigma := sigma i) (tau := tau i)
    (alpha := alpha) (kappa := kappa i) (epsilon := delta / 2)
    input i hfixedSigma (hsigma i) (hsigmaOne i) halpha hkappa
    hnorm hre (by linarith) hmargin

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


/-- At the slope-weighted balanced height, the whole positive-ordinate
outside-cluster PNT tail is negligible relative to the target zero amplitude. -/
theorem
    actualZetaFiniteStripsOutsideCluster_weightedBalancedHeight_positiveTail_negligible
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
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm : ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre : ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTTailNorm
        (actualSelectedHeightFiniteStripWeightedBalancedHeight beta sigma tau) S) := by
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
    actualZetaFiniteStripsOutsideCluster_selectedHeight_positiveTail_negligible
      input sigma tau kappa (fun _ => delta / 2) hfixedSigma hheight
      hsigma hsigmaOne halpha hkappa hnorm hre hepsilon hmargin

/-- Conjugation symmetry and a strict real-ordinate gap upgrade the positive
weighted tail estimate to the complete signed outside-cluster zero tail. -/
theorem
    actualZetaFiniteStripsOutsideCluster_weightedBalancedHeight_fullTail_negligible
    {beta : ℝ}
    {n : ℕ}
    {S : Finset ℂ}
    (hS : IsConjugationInvariantCluster S)
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
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm : ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre : ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (actualSelectedHeightFiniteStripWeightedBalancedHeight beta sigma tau) S) := by
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
  have hheightNonneg :
      ∀ᶠ x in atTop,
        0 ≤ actualSelectedHeightFiniteStripWeightedBalancedHeight
          beta sigma tau x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simpa [actualSelectedHeightFiniteStripWeightedBalancedHeight,
      carlsonPolynomialHeight] using (Real.rpow_nonneg hx alpha)
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
    actualZetaFiniteStripsOutsideCluster_selectedHeight_fullTail_negligible
      hS input sigma tau kappa (fun _ => delta / 2) hfixedSigma hheight
      hheightNonneg hsigma hsigmaOne halpha hkappa hnorm hre hepsilon hmargin hreal

/-- Auditable data showing that the slope-weighted balanced height controls
the complete actual zeta tail outside a conjugation-invariant main cluster. -/
structure ActualWeightedBalancedHeightOutsideClusterCertificate
    (beta : ℝ) (S : Finset ℂ) (n : ℕ)
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau x)
          S (n + 1)) : Type where
  beta_one : beta < 1
  sigma_half : ∀ i, 1 / 2 < sigma i
  sigma_one : ∀ i, sigma i < 1
  tau_nonneg : ∀ i, 0 ≤ tau i
  endpoint_threshold :
    ∀ i,
      carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta
  conjugation_invariant : IsConjugationInvariantCluster S
  fixed_sigma : ∀ i x, (input x).sigma i = sigma i
  kappa_pos : ∀ i, 0 < kappa i
  norm_lower :
    ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖
  re_upper :
    ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i
  real_re_lt_beta :
    ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta

/-- The weighted balanced-height certificate controls the complete
outside-cluster tail on the target-zero amplitude scale. -/
theorem
    ActualWeightedBalancedHeightOutsideClusterCertificate.fullTail_negligible
    {beta : ℝ} {S : Finset ℂ} {n : ℕ}
    {sigma tau kappa : Fin (n + 1) → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau x)
          S (n + 1)}
    (certificate :
      ActualWeightedBalancedHeightOutsideClusterCertificate
        beta S n sigma tau kappa input) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (actualSelectedHeightFiniteStripWeightedBalancedHeight
          beta sigma tau)
        S) :=
  actualZetaFiniteStripsOutsideCluster_weightedBalancedHeight_fullTail_negligible
    certificate.conjugation_invariant sigma tau kappa
    certificate.beta_one certificate.sigma_half certificate.sigma_one
    certificate.tau_nonneg certificate.endpoint_threshold input
    certificate.fixed_sigma certificate.kappa_pos certificate.norm_lower
    certificate.re_upper certificate.real_re_lt_beta

/-- Domination by the weighted complete tail converts any signed complement
into the certificate required by the common oscillation transfer. -/
theorem
    ActualWeightedBalancedHeightOutsideClusterCertificate.signedComplementCertificate
    {beta : ℝ} {S : Finset ℂ} {n : ℕ}
    {sigma tau kappa : Fin (n + 1) → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau x)
          S (n + 1)}
    (certificate :
      ActualWeightedBalancedHeightOutsideClusterCertificate
        beta S n sigma tau kappa input)
    (complement : ℝ → ℝ)
    (hdominated :
      ∀ᶠ x in atTop,
        |complement x| ≤
          dynamicFullOutsideClusterPNTZeroTailNorm
            (actualSelectedHeightFiniteStripWeightedBalancedHeight
              beta sigma tau)
            S x) :
    ClusterExcludedTargetComplementCertificate
      (targetZeroPowerAmplitude beta) complement
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (actualSelectedHeightFiniteStripWeightedBalancedHeight
          beta sigma tau)
        S) where
  amplitude_eventually_pos :=
    targetZeroPowerAmplitude_eventually_pos beta
  complement_dominated := hdominated
  excluded_tail_negligible := certificate.fullTail_negligible

/-- The real part of the actual outside-cluster zeta sum automatically
supplies the signed weighted complement certificate. -/
theorem
    ActualWeightedBalancedHeightOutsideClusterCertificate.actualSignedComplementCertificate
    {beta : ℝ} {S : Finset ℂ} {n : ℕ}
    {sigma tau kappa : Fin (n + 1) → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau x)
          S (n + 1)}
    (certificate :
      ActualWeightedBalancedHeightOutsideClusterCertificate
        beta S n sigma tau kappa input) :
    ClusterExcludedTargetComplementCertificate
      (targetZeroPowerAmplitude beta)
      (dynamicOutsideClusterPNTComplement
        (actualSelectedHeightFiniteStripWeightedBalancedHeight
          beta sigma tau)
        S)
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (actualSelectedHeightFiniteStripWeightedBalancedHeight
          beta sigma tau)
        S) := by
  apply certificate.signedComplementCertificate
  exact Filter.Eventually.of_forall fun x =>
    abs_dynamicOutsideClusterPNTComplement_le_tailNorm
      (actualSelectedHeightFiniteStripWeightedBalancedHeight
        beta sigma tau)
      S x

end

end PrimeNumberTheorem
