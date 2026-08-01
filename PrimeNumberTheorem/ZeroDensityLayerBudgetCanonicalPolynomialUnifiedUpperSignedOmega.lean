import PrimeNumberTheorem.ZeroDensityLayerBudgetCanonicalPolynomialHeightWindow

/-!
# Canonical polynomial-height unified upper and signed transfer

The explicit trisection window automatically supplies every analytic height,
margin, and remainder input of the variable-boundary unified theorem. The only
remaining lower-side assumptions are moving right-edge geometry and the two
signed finite-package witnesses.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Canonical power-scale upper/signed transfer. The exact threshold
`beta0 > (1 + sigma) / 2` constructs the selected polynomial height and all
analytic residual certificates automatically. -/
theorem actualCanonicalPolynomialVariableBoundaryUnifiedUpperSignedOmega
    {sigma beta0 eta c loss : ℝ} {beta : ℝ → ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hhalf : 1 / 2 < sigma)
    (htarget : (1 + sigma) / 2 < beta0)
    (hbeta0One : beta0 < 1)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)))
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma)
        (selectedUniformGoodHeight
          (canonicalPolynomialHeightInnerExponent beta0 sigma) selection)
        beta)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (canonicalPolynomialHeightInnerExponent beta0 sigma) selection)
            (variableBoundaryZeroPackage
              (selectedUniformGoodHeight
                (canonicalPolynomialHeightInnerExponent beta0 sigma) selection)
              beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (canonicalPolynomialHeightInnerExponent beta0 sigma) selection)
            (variableBoundaryZeroPackage
              (selectedUniformGoodHeight
                (canonicalPolynomialHeightInnerExponent beta0 sigma) selection)
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
  have hone : sigma < 1 := by linarith
  have hbeta0 : 0 < beta0 := by linarith
  have hwindow :=
    canonicalPolynomialHeightWindow_spec hhalf htarget hbeta0One
  have hselected :=
    canonicalPolynomialSelectedHeight_spec
      hhalf htarget hbeta0One selection
  have houter :
      0 < canonicalPolynomialHeightOuterExponent beta0 sigma :=
    hwindow.2.1.trans hwindow.2.2.1
  exact
    actualMonotoneVariableBoundaryUnifiedUpperSignedOmega
      heta hloss hlossC hbeta0 hbetaLower hbetaMono
      hselected.1 hselected.2.1 houter hwindow.2.2.2.2.2.2.1
      hwindow.2.2.2.2.2.2.2
      hrightReal hhalf hone hright hselected.2.2 hmainPos hmainNeg

end PrimeNumberTheorem
