import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryMonotoneUnifiedUpperSignedOmega
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryGoodHeightTransfer

/-!
# Canonical-good-height moving upper and signed Omega transfer

The monotone variable-boundary transfer still accepted a polynomial height
majorization, cofinality, and an actual explicit-formula remainder certificate.
The repository's canonical selected good-height schedule supplies all three.

This specialization preserves the moving boundary and its exact
`x ^ beta(x)` scale.  The indexed visible right edge and the independent
positive and negative moving-package witnesses remain explicit inputs.
-/

namespace PrimeNumberTheorem

open Filter

/-- The canonical selected good-height schedule removes every height-side
certificate from the monotone variable-boundary upper/signed-Omega transfer.

The conclusion combines an automatic relative PNT upper bound at the moving
target scale with conditional positive and negative unnormalized witnesses at
the exact `x ^ beta(x)` scale. -/
theorem
    actualMonotoneVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega
    {sigma beta0 alpha epsilon eta c loss : ℝ}
    {beta : ℝ → ℝ}
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)))
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + alpha + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma)
        (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha) beta)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
            (variableBoundaryZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
            (variableBoundaryZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            variableBoundaryTargetAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta x) := by
  rcases
      actualDynamicBoundaryCanonicalSelectedGoodHeight_spec
        hbeta0 halpha halphaOne hcontourMargin with
    ⟨hHle, hHtop, remainder⟩
  exact
    actualMonotoneVariableBoundaryUnifiedUpperSignedOmega
      heta hloss hlossC hbeta0 hbetaLower hbetaMono hHle hHtop halpha
        hepsilon hmargin hrightReal hhalf hone hright remainder hmainPos
          hmainNeg

end PrimeNumberTheorem
