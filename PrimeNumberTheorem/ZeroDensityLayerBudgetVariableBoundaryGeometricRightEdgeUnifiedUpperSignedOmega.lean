import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega

/-!
# Geometric moving right edges for the unified transfer

The direct finite-zero right-edge predicate automatically controls every
currently visible Carlson-indexed positive zero.  This removes an indexing
artifact from the canonical-good-height moving upper/signed-Omega interface.
-/

namespace PrimeNumberTheorem

open Filter

/-- A geometric right edge for the visible positive-zero Finset automatically
induces the indexed visible right edge used by Carlson dominated convergence. -/
theorem IsVariableBoundaryRightEdge.toIndexedVisible
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hright : IsVariableBoundaryRightEdge H beta) :
    IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta := by
  intro m index hvisible
  rcases actualCarlsonPositiveZero_spec index with ⟨hzero, him, _⟩
  apply hright (m : ℝ) (actualCarlsonPositiveZero index)
  apply mem_positiveNontrivialZerosFinset.mpr
  exact ⟨hzero, him, by simpa [abs_of_pos him] using hvisible⟩

/-- Canonical-good-height moving upper and signed-Omega transfer stated using
only the direct geometric right edge of each visible finite zero set. -/
theorem
    actualMonotoneGeometricVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega
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
      IsVariableBoundaryRightEdge
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
  exact
    actualMonotoneVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega
      heta hloss hlossC hbeta0 hbetaLower hbetaMono halpha halphaOne
        hcontourMargin hepsilon hmargin hrightReal hhalf hone
          hright.toIndexedVisible hmainPos hmainNeg

end PrimeNumberTheorem
