import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalLowLayer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryFullyAutomaticTransfer

/-!
# Dynamic-boundary transfer with a reciprocal low layer

This module propagates the reciprocal-mass low-layer improvement through the
actual explicit formula and the existing upper/witness transfer machinery.
The selected-height exponent remains necessary for the contour certificate,
but no longer appears in the low-layer decay margin.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/-- Complete signed zero complement under the reciprocal low-layer margin. -/
theorem actualDynamicBoundarySignedComplement_targetAmplitudeNegligible_reciprocal
    {H : ℝ → ℝ} {beta sigma alpha epsilon : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hrightPositive :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        dynamicOutsideClusterPNTComplement H
          (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  have hpositive :=
    actualDynamicBoundaryCanonicalPositiveNormalizedSum_tendsto_zero_reciprocal
      hhalf hone hHle hHtop halpha hepsilon hmargin hrightPositive
  have hreal :=
    actualDynamicBoundaryRealNormalizedSum_tendsto_zero
      hHtop hrightReal
  have hfull :=
    actualDynamicBoundaryFullNormalizedSum_tendsto_zero
      hpositive hreal
  have hcomplement :=
    abs_dynamicOutsideDynamicBoundaryPNTComplement_div_target_tendsto_zero
      hfull
  unfold NaturalPointTargetAmplitudeNegligible
  exact hcomplement

/-- Full actual explicit-formula residual under the reciprocal low-layer
margin. -/
theorem actualDynamicBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_reciprocal
    {H : ℝ → ℝ} {beta sigma alpha epsilon : ℝ}
    (hbeta : 0 < beta)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hrightPositive :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainder : ActualSelectedHeightNaturalPointRemainderCertificate beta H) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  have hamplitude :
      ∀ᶠ m : ℕ in atTop, 0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  have hclosed :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ => actualPNTClosedRealAxisRelativeTerm (m : ℝ)) :=
    (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta).naturalPoint
  have hcontour :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ => actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)) :=
    remainder.negligible
  have hcomplement :=
    actualDynamicBoundarySignedComplement_targetAmplitudeNegligible_reciprocal
      hhalf hone hHle hHtop halpha hepsilon hmargin
      hrightPositive hrightReal
  have hthree :=
    NaturalPointTargetAmplitudeNegligible.add hamplitude
      (NaturalPointTargetAmplitudeNegligible.add hamplitude hclosed hcontour)
      hcomplement
  unfold NaturalPointTargetAmplitudeNegligible at hthree ⊢
  apply hthree.congr'
  filter_upwards with m
  rw [relativeChebyshevPsi0Error_eq_dynamicBoundaryPackage_add_actualResiduals]
  ring_nf

/-- Automatic upper transfer with the reciprocal low-layer margin. -/
theorem actualDynamicBoundaryAutomaticPNTUpperTransfer_reciprocal
    {H : ℝ → ℝ} {beta sigma alpha epsilon C eta : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hheightUpper :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hheightTendsto : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainderCertificate : ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (heta : 0 < eta)
    (hcap : DynamicBoundaryPackageCoefficientCap beta H C) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (C + eta) * targetZeroPowerAmplitude beta (m : ℝ) := by
  apply eventually_abs_relativeChebyshevPsi0Error_lt_dynamicBoundaryCap_add
    heta hcap
  exact
    actualDynamicBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_reciprocal
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
      hmargin hpositiveRightEdge hrealRightEdge remainderCertificate

/-- Dynamic main witnesses survive the reciprocal explicit-formula residual. -/
theorem actualDynamicBoundaryAutomaticPNTWitnessTransfer_reciprocal
    {H : ℝ → ℝ} {beta sigma alpha epsilon c loss : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hheightUpper :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hheightTendsto : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainderCertificate : ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (hloss : 0 < loss) (hlossC : loss < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    0 < c - loss ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x : ℝ => (c - loss) * targetZeroPowerAmplitude beta x) := by
  have hresidual :=
    actualDynamicBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_reciprocal
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
      hmargin hpositiveRightEdge hrealRightEdge remainderCertificate
  exact actualDynamicBoundaryMainWitness_realTransfer
    hloss hlossC hresidual hmain

/-- Unified upper and lower transfer under the reciprocal low-layer margin. -/
theorem actualDynamicBoundaryAutomaticPNTBidirectionalTransfer_reciprocal
    {H : ℝ → ℝ} {beta sigma alpha epsilon C eta c loss : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hheightUpper :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hheightTendsto : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainderCertificate : ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (heta : 0 < eta)
    (hcap : DynamicBoundaryPackageCoefficientCap beta H C)
    (hloss : 0 < loss) (hlossC : loss < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (C + eta) * targetZeroPowerAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x : ℝ => (c - loss) * targetZeroPowerAmplitude beta x) ∧
      HasFarTargetAmplitudeWitness chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta) := by
  have hupper :=
    actualDynamicBoundaryAutomaticPNTUpperTransfer_reciprocal
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
      hmargin hpositiveRightEdge hrealRightEdge remainderCertificate heta hcap
  rcases actualDynamicBoundaryAutomaticPNTWitnessTransfer_reciprocal
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
      hmargin hpositiveRightEdge hrealRightEdge remainderCertificate
      hloss hlossC hmain with
    ⟨hcoefficient, hrelative⟩
  exact ⟨hupper, hcoefficient, hrelative,
    hrelative.relativeChebyshevPsi0Error_to_unnormalized⟩

/-- Fully automatic upper transfer after applying the Carlson package
coefficient cap. -/
theorem actualDynamicBoundaryFullyAutomaticPNTUpperTransfer_reciprocal
    {H : ℝ → ℝ} {beta sigma alpha epsilon eta : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hheightUpper :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hheightTendsto : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainderCertificate : ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (heta : 0 < eta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  have hsigmaBeta : sigma < beta := by
    linarith
  exact actualDynamicBoundaryAutomaticPNTUpperTransfer_reciprocal
    hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
    hmargin hpositiveRightEdge hrealRightEdge remainderCertificate heta
    (actualCarlsonDynamicBoundaryCoefficientCap
      hsigma hsigmaOne hsigmaBeta H)

/-- Fully automatic bidirectional transfer under the reciprocal low-layer
margin; the only package-side lower input is the far main witness. -/
theorem actualDynamicBoundaryFullyAutomaticPNTBidirectionalTransfer_reciprocal
    {H : ℝ → ℝ} {beta sigma alpha epsilon eta c loss : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hheightUpper :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hheightTendsto : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainderCertificate : ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (heta : 0 < eta)
    (hloss : 0 < loss) (hlossC : loss < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            targetZeroPowerAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x : ℝ => (c - loss) * targetZeroPowerAmplitude beta x) ∧
      HasFarTargetAmplitudeWitness chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta) := by
  have hsigmaBeta : sigma < beta := by
    linarith
  exact actualDynamicBoundaryAutomaticPNTBidirectionalTransfer_reciprocal
    hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
    hmargin hpositiveRightEdge hrealRightEdge remainderCertificate heta
    (actualCarlsonDynamicBoundaryCoefficientCap
      hsigma hsigmaOne hsigmaBeta H)
    hloss hlossC hmain

end PrimeNumberTheorem
