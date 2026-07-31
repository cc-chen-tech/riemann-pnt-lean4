import PrimeNumberTheorem.ZeroDensityLayerBudgetOptimalPolynomialHeightWindow

/-!
# Optimal polynomial sigma-only unified transfer

The minimax-optimal quarter-balanced height window is installed in the
sigma-only natural running-boundary transfer. All analytic, density, and
geometric inputs remain automatic; only signed visible-main witnesses remain.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Minimax-optimal selected height for the sigma-only automatic target. -/
noncomputable def optimalPolynomialSigmaOnlyRunningHeight
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection) :
    ℝ → ℝ :=
  selectedUniformGoodHeight
    (optimalPolynomialHeightInnerExponent
      (canonicalPolynomialSigmaOnlyBeta0 sigma) sigma)
    selection

/-- Natural running visible-zero boundary at the minimax-optimal height. -/
noncomputable def optimalPolynomialSigmaOnlyRunningBoundary
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection) :
    ℝ → ℝ :=
  naturalRunningVisibleZeroBoundaryReal
    (optimalPolynomialSigmaOnlyRunningHeight sigma selection)
    (canonicalPolynomialSigmaOnlyBeta0 sigma)

/-- Visible main term at the optimal sigma-only height and boundary. -/
noncomputable def optimalPolynomialSigmaOnlyVisibleMain
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (m : ℕ) : ℝ :=
  dynamicVisibleClusterPNTMain
    (optimalPolynomialSigmaOnlyRunningHeight sigma selection)
    (variableBoundaryZeroPackage
      (optimalPolynomialSigmaOnlyRunningHeight sigma selection)
      (optimalPolynomialSigmaOnlyRunningBoundary sigma selection) (m : ℝ))
    (m : ℝ)

/-- Target amplitude at the optimal sigma-only running boundary. -/
noncomputable def optimalPolynomialSigmaOnlyAmplitude
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  variableBoundaryTargetAmplitude
    (optimalPolynomialSigmaOnlyRunningBoundary sigma selection) x

/-- Complete sigma-only power-scale upper/signed transfer at the minimax
optimal polynomial-height allocation. -/
theorem actualOptimalPolynomialSigmaOnlyUnifiedUpperSignedOmega
    {sigma eta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (optimalPolynomialSigmaOnlyVisibleMain sigma selection)
        (fun m : ℕ =>
          c * optimalPolynomialSigmaOnlyAmplitude sigma selection (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (optimalPolynomialSigmaOnlyVisibleMain sigma selection)
        (fun m : ℕ =>
          c * optimalPolynomialSigmaOnlyAmplitude sigma selection (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
          optimalPolynomialSigmaOnlyAmplitude sigma selection (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * x ^
            optimalPolynomialSigmaOnlyRunningBoundary sigma selection x) := by
  let beta0 := canonicalPolynomialSigmaOnlyBeta0 sigma
  let H := optimalPolynomialSigmaOnlyRunningHeight sigma selection
  let beta := optimalPolynomialSigmaOnlyRunningBoundary sigma selection
  rcases canonicalPolynomialSigmaOnlyBeta0_spec hone with
    ⟨htarget, hbetaOne, hreal⟩
  have hbeta0 : 0 < beta0 := by
    dsimp [beta0]
    linarith
  have hwindow := optimalPolynomialHeightWindow_spec hhalf htarget hbetaOne
  have hselected :=
    optimalPolynomialSelectedHeight_spec hhalf htarget hbetaOne selection
  have houter :
      0 < optimalPolynomialHeightOuterExponent beta0 sigma :=
    hwindow.2.1.trans hwindow.2.2.1
  have hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ) := by
    filter_upwards with m
    exact beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast H beta0 m
  have hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)) :=
    naturalRunningVisibleZeroBoundaryReal_sampled_monotone H beta0
  have hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta :=
    naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge H beta0
  exact
    actualMonotoneVariableBoundaryUnifiedUpperSignedOmega
      heta hloss hlossC hbeta0 hbetaLower hbetaMono
      hselected.1 hselected.2.1 houter hwindow.2.2.2.2.2.2.1
      hwindow.2.2.2.2.2.2.2
      hreal hhalf hone hright hselected.2.2
      (by simpa [beta0, H, beta,
          optimalPolynomialSigmaOnlyVisibleMain,
          optimalPolynomialSigmaOnlyAmplitude,
          optimalPolynomialSigmaOnlyRunningHeight,
          optimalPolynomialSigmaOnlyRunningBoundary] using hmainPos)
      (by simpa [beta0, H, beta,
          optimalPolynomialSigmaOnlyVisibleMain,
          optimalPolynomialSigmaOnlyAmplitude,
          optimalPolynomialSigmaOnlyRunningHeight,
          optimalPolynomialSigmaOnlyRunningBoundary] using hmainNeg)

end PrimeNumberTheorem
