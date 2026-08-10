import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryBalancedGoodHeightTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCanonicalBetaThresholdTransfer

/-!
# Beta-only canonical dynamic-boundary transfer

For `3 / 4 < beta < 1`, the existing canonical strip threshold

`sigma = beta - 1 / 4`

lies in `(1 / 2, 1)` and satisfies the exact balanced feasibility gap

`1 + sigma < 2 * beta`.

This module feeds that threshold into the actual dynamic-boundary transfer.
It removes the last freely chosen height/density parameter while retaining
the automatic Carlson coefficient cap and the actual explicit formula.
-/

namespace PrimeNumberTheorem

open Filter

/-- The canonical beta-dependent strip threshold satisfies every numerical
condition of the balanced dynamic-boundary transfer. -/
theorem actualDynamicBoundaryCanonicalBetaThreshold_spec
    {beta : ℝ}
    (hbeta : 3 / 4 < beta)
    (hbetaOne : beta < 1) :
    1 / 2 < pntHybridCanonicalBetaThreshold beta ∧
      pntHybridCanonicalBetaThreshold beta < 1 ∧
      1 + pntHybridCanonicalBetaThreshold beta < 2 * beta := by
  exact
    ⟨pntHybridCanonicalBetaThreshold_half_lt hbeta,
      pntHybridCanonicalBetaThreshold_lt_one hbetaOne,
      by
        have hlow := pntHybridCanonicalBetaThreshold_lowBudget hbeta
        linarith⟩

/-- Actual PNT upper transfer with both the strip boundary and selected
height fixed explicitly by `beta`. -/
theorem actualDynamicBoundaryCanonicalBetaPNTUpperTransfer
    {beta eta : ℝ}
    (hbeta : 3 / 4 < beta)
    (hbetaOne : beta < 1)
    (hpositiveRightEdge :
      ∀ index :
          ActualCarlsonPositiveZeroIndex
            (pntHybridCanonicalBetaThreshold beta),
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (heta : 0 < eta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant
            (pntHybridCanonicalBetaThreshold beta) + eta) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  rcases actualDynamicBoundaryCanonicalBetaThreshold_spec hbeta hbetaOne with
    ⟨hsigma, hsigmaOne, hgap⟩
  exact
    actualDynamicBoundaryBalancedGoodHeightPNTUpperTransfer
      hsigma hsigmaOne hgap hpositiveRightEdge hrealRightEdge heta

/-- Beta-only actual dynamic-boundary bidirectional transfer.

The upper side now has no free strip threshold, truncation exponent, density
slack, height schedule, contour certificate, or package coefficient cap.
The lower side deliberately retains the moving-package anti-cancellation
witness.
-/
theorem actualDynamicBoundaryCanonicalBetaPNTBidirectionalTransfer
    {beta eta c loss : ℝ}
    (hbeta : 3 / 4 < beta)
    (hbetaOne : beta < 1)
    (hpositiveRightEdge :
      ∀ index :
          ActualCarlsonPositiveZeroIndex
            (pntHybridCanonicalBetaThreshold beta),
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
              (actualDynamicBoundaryBalancedGoodHeightExponent
                (pntHybridCanonicalBetaThreshold beta)))
            (dynamicEqualRealPartZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight
                (actualDynamicBoundaryBalancedGoodHeightExponent
                  (pntHybridCanonicalBetaThreshold beta)))
              beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant
              (pntHybridCanonicalBetaThreshold beta) + eta) *
            targetZeroPowerAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x => (c - loss) * targetZeroPowerAmplitude beta x) ∧
      HasFarTargetAmplitudeWitness chebyshevPsi0Error
        (fun x => (c - loss) * x ^ beta) := by
  rcases actualDynamicBoundaryCanonicalBetaThreshold_spec hbeta hbetaOne with
    ⟨hsigma, hsigmaOne, hgap⟩
  exact
    actualDynamicBoundaryBalancedGoodHeightPNTBidirectionalTransfer
      hsigma hsigmaOne hgap hpositiveRightEdge hrealRightEdge
        heta hloss hlossC hmain

end PrimeNumberTheorem
