import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryGoodHeightTransfer

/-!
# Balanced canonical good-height dynamic-boundary transfer

The canonical good-height transfer requires a polynomial exponent `alpha`
strictly between the contour threshold `1 - beta` and the Carlson threshold
`beta - sigma`, together with a positive Carlson slack `epsilon`.

These simultaneous strict margins are feasible exactly when

`1 + sigma < 2 * beta`.

The midpoint

`alpha = (1 - sigma) / 2`

and half of the remaining margin

`epsilon = (2 * beta - sigma - 1) / 4`

give explicit parameters.  This module proves the exact arithmetic
feasibility criterion and removes `alpha` and `epsilon` from the canonical
dynamic-boundary transfer interface.
-/

namespace PrimeNumberTheorem

open Filter

/-- Midpoint exponent between the contour and Carlson thresholds. -/
noncomputable def actualDynamicBoundaryBalancedGoodHeightExponent
    (sigma : ℝ) : ℝ :=
  (1 - sigma) / 2

/-- Positive Carlson slack equal to half the strict balanced margin. -/
noncomputable def actualDynamicBoundaryBalancedGoodHeightEpsilon
    (beta sigma : ℝ) : ℝ :=
  (2 * beta - sigma - 1) / 4

/-- The explicit balanced parameters satisfy every contour and Carlson
condition required by the canonical good-height transfer. -/
theorem actualDynamicBoundaryBalancedGoodHeightParameters_spec
    {beta sigma : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hgap : 1 + sigma < 2 * beta) :
    0 < beta ∧
      0 < actualDynamicBoundaryBalancedGoodHeightExponent sigma ∧
      actualDynamicBoundaryBalancedGoodHeightExponent sigma ≤ 1 ∧
      1 - beta <
        actualDynamicBoundaryBalancedGoodHeightExponent sigma ∧
      0 < actualDynamicBoundaryBalancedGoodHeightEpsilon beta sigma ∧
      sigma - beta +
          actualDynamicBoundaryBalancedGoodHeightExponent sigma +
          actualDynamicBoundaryBalancedGoodHeightEpsilon beta sigma < 0 := by
  dsimp [actualDynamicBoundaryBalancedGoodHeightExponent,
    actualDynamicBoundaryBalancedGoodHeightEpsilon]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Exact feasibility criterion for simultaneous contour and Carlson strict
margins. -/
theorem actualDynamicBoundaryGoodHeightMargins_feasible_iff
    {beta sigma : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) :
    (∃ alpha epsilon : ℝ,
        0 < alpha ∧
          alpha ≤ 1 ∧
          1 - beta < alpha ∧
          0 < epsilon ∧
          sigma - beta + alpha + epsilon < 0) ↔
      1 + sigma < 2 * beta := by
  constructor
  · rintro ⟨alpha, epsilon, halpha, halphaOne, hcontour,
      hepsilon, hCarlson⟩
    linarith
  · intro hgap
    rcases
        actualDynamicBoundaryBalancedGoodHeightParameters_spec
          hsigma hsigmaOne hgap with
      ⟨_, halpha, halphaOne, hcontour, hepsilon, hCarlson⟩
    exact
      ⟨actualDynamicBoundaryBalancedGoodHeightExponent sigma,
        actualDynamicBoundaryBalancedGoodHeightEpsilon beta sigma,
        halpha, halphaOne, hcontour, hepsilon, hCarlson⟩

/-- Fully automatic upper transfer at the explicit balanced canonical good
height.  The sole numerical compatibility condition is the exact strict gap
`1 + sigma < 2 * beta`. -/
theorem actualDynamicBoundaryBalancedGoodHeightPNTUpperTransfer
    {beta sigma eta : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hgap : 1 + sigma < 2 * beta)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (heta : 0 < eta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  rcases
      actualDynamicBoundaryBalancedGoodHeightParameters_spec
        hsigma hsigmaOne hgap with
    ⟨hbeta, halpha, halphaOne, hcontour, hepsilon, hCarlson⟩
  exact
    actualDynamicBoundaryCanonicalGoodHeightPNTUpperTransfer
      hbeta hsigma hsigmaOne halpha halphaOne hcontour hepsilon hCarlson
        hpositiveRightEdge hrealRightEdge heta

/-- Balanced canonical bidirectional transfer.

All height, contour, density-slack, and package-coefficient inputs on the
upper side are now constructed from `beta` and `sigma`.  The moving-package
far witness remains the explicit anti-cancellation input on the lower side.
-/
theorem actualDynamicBoundaryBalancedGoodHeightPNTBidirectionalTransfer
    {beta sigma eta c loss : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hgap : 1 + sigma < 2 * beta)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight
              (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
            (dynamicEqualRealPartZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight
                (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
              beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            targetZeroPowerAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x => (c - loss) * targetZeroPowerAmplitude beta x) ∧
      HasFarTargetAmplitudeWitness chebyshevPsi0Error
        (fun x => (c - loss) * x ^ beta) := by
  rcases
      actualDynamicBoundaryBalancedGoodHeightParameters_spec
        hsigma hsigmaOne hgap with
    ⟨hbeta, halpha, halphaOne, hcontour, hepsilon, hCarlson⟩
  exact
    actualDynamicBoundaryCanonicalGoodHeightPNTBidirectionalTransfer
      hbeta hsigma hsigmaOne halpha halphaOne hcontour hepsilon hCarlson
        hpositiveRightEdge hrealRightEdge heta hloss hlossC hmain

end PrimeNumberTheorem
