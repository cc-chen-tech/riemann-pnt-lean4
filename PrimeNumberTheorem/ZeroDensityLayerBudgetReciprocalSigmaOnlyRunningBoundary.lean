import PrimeNumberTheorem.ZeroDensityLayerBudgetReciprocalVariableBoundaryTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetOptimalPolynomialSigmaOnlyUnifiedUpperSignedOmega

/-!
# Sigma-only reciprocal running-boundary transfer

After reciprocal low-layer summation, the fixed anchor only needs to lie to
the right of `sigma` and the finite real-ordinate bottleneck.  This module
chooses that anchor automatically, constructs an admissible selected height,
and installs the natural running visible-zero boundary.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- Joint fixed obstruction from the density line and real-ordinate zeros. -/
noncomputable def reciprocalSigmaOnlyBottleneck (sigma : ℝ) : ℝ :=
  max realOrdinatePNTZeroBottleneck sigma

/-- Automatic fixed anchor halfway between the reciprocal obstruction and
one. -/
noncomputable def reciprocalSigmaOnlyBeta0 (sigma : ℝ) : ℝ :=
  (reciprocalSigmaOnlyBottleneck sigma + 1) / 2

/-- Selected-height exponent strictly above the contour threshold. -/
noncomputable def reciprocalSigmaOnlyInnerExponent (sigma : ℝ) : ℝ :=
  1 - reciprocalSigmaOnlyBeta0 sigma / 2

/-- A strictly larger polynomial ceiling for the selected height. -/
noncomputable def reciprocalSigmaOnlyOuterExponent (sigma : ℝ) : ℝ :=
  (reciprocalSigmaOnlyInnerExponent sigma + 1) / 2

/-- Fixed reciprocal low-layer slack. -/
noncomputable def reciprocalSigmaOnlyEpsilon (sigma : ℝ) : ℝ :=
  (reciprocalSigmaOnlyBeta0 sigma - sigma) / 2

noncomputable def reciprocalSigmaOnlyRunningHeight
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  selectedUniformGoodHeight (reciprocalSigmaOnlyInnerExponent sigma) selection

noncomputable def reciprocalSigmaOnlyRunningBoundary
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  naturalRunningVisibleZeroBoundaryReal
    (reciprocalSigmaOnlyRunningHeight sigma selection)
    (reciprocalSigmaOnlyBeta0 sigma)

noncomputable def reciprocalSigmaOnlyVisibleMain
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection) : ℕ → ℝ :=
  fun m =>
    dynamicVisibleClusterPNTMain
      (reciprocalSigmaOnlyRunningHeight sigma selection)
      (variableBoundaryZeroPackage
        (reciprocalSigmaOnlyRunningHeight sigma selection)
        (reciprocalSigmaOnlyRunningBoundary sigma selection) (m : ℝ))
      (m : ℝ)

noncomputable def reciprocalSigmaOnlyAmplitude
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  variableBoundaryTargetAmplitude
    (reciprocalSigmaOnlyRunningBoundary sigma selection)

/-- Arithmetic and finite-real-zero specification for the automatic anchor
and selected-height exponents. -/
theorem reciprocalSigmaOnlyParameters_spec
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    sigma < reciprocalSigmaOnlyBeta0 sigma ∧
      0 < reciprocalSigmaOnlyBeta0 sigma ∧
      reciprocalSigmaOnlyBeta0 sigma < 1 ∧
      (∀ rho ∈ realOrdinateNontrivialZerosFinset 0,
        rho.re < reciprocalSigmaOnlyBeta0 sigma) ∧
      0 < reciprocalSigmaOnlyInnerExponent sigma ∧
      reciprocalSigmaOnlyInnerExponent sigma ≤ 1 ∧
      1 - reciprocalSigmaOnlyBeta0 sigma <
        reciprocalSigmaOnlyInnerExponent sigma ∧
      reciprocalSigmaOnlyInnerExponent sigma <
        reciprocalSigmaOnlyOuterExponent sigma ∧
      0 < reciprocalSigmaOnlyOuterExponent sigma ∧
      0 < reciprocalSigmaOnlyEpsilon sigma ∧
      sigma - reciprocalSigmaOnlyBeta0 sigma +
          reciprocalSigmaOnlyEpsilon sigma < 0 := by
  have hsigmaPos : 0 < sigma := by linarith
  have hbottleneckOne : reciprocalSigmaOnlyBottleneck sigma < 1 := by
    exact max_lt realOrdinatePNTZeroBottleneck_lt_one hone
  have hsigmaBottleneck : sigma ≤ reciprocalSigmaOnlyBottleneck sigma := by
    exact le_max_right _ _
  have hbottleneckBeta :
      reciprocalSigmaOnlyBottleneck sigma < reciprocalSigmaOnlyBeta0 sigma := by
    unfold reciprocalSigmaOnlyBeta0
    linarith
  have hsigmaBeta : sigma < reciprocalSigmaOnlyBeta0 sigma :=
    hsigmaBottleneck.trans_lt hbottleneckBeta
  have hbetaPos : 0 < reciprocalSigmaOnlyBeta0 sigma :=
    hsigmaPos.trans hsigmaBeta
  have hbetaOne : reciprocalSigmaOnlyBeta0 sigma < 1 := by
    unfold reciprocalSigmaOnlyBeta0
    linarith
  have hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0,
        rho.re < reciprocalSigmaOnlyBeta0 sigma := by
    intro rho hrho
    exact
      (realOrdinateNontrivialZero_re_le_bottleneck hrho).trans_lt
        ((le_max_left realOrdinatePNTZeroBottleneck sigma).trans_lt
          hbottleneckBeta)
  have hinner : 0 < reciprocalSigmaOnlyInnerExponent sigma := by
    unfold reciprocalSigmaOnlyInnerExponent
    linarith
  have hinnerOne : reciprocalSigmaOnlyInnerExponent sigma ≤ 1 := by
    unfold reciprocalSigmaOnlyInnerExponent
    linarith
  have hcontour :
      1 - reciprocalSigmaOnlyBeta0 sigma <
        reciprocalSigmaOnlyInnerExponent sigma := by
    unfold reciprocalSigmaOnlyInnerExponent
    linarith
  have hinnerStrictOne : reciprocalSigmaOnlyInnerExponent sigma < 1 := by
    unfold reciprocalSigmaOnlyInnerExponent
    linarith
  have hinnerOuter :
      reciprocalSigmaOnlyInnerExponent sigma <
        reciprocalSigmaOnlyOuterExponent sigma := by
    unfold reciprocalSigmaOnlyOuterExponent
    linarith
  have houter : 0 < reciprocalSigmaOnlyOuterExponent sigma :=
    hinner.trans hinnerOuter
  have hepsilon : 0 < reciprocalSigmaOnlyEpsilon sigma := by
    unfold reciprocalSigmaOnlyEpsilon
    linarith
  have hmargin :
      sigma - reciprocalSigmaOnlyBeta0 sigma +
          reciprocalSigmaOnlyEpsilon sigma < 0 := by
    unfold reciprocalSigmaOnlyEpsilon
    linarith
  exact ⟨hsigmaBeta, hbetaPos, hbetaOne, hreal, hinner, hinnerOne,
    hcontour, hinnerOuter, houter, hepsilon, hmargin⟩

/-- The automatic exponents construct the selected-height ceiling,
cofinality, and actual natural-point contour remainder certificate. -/
theorem reciprocalSigmaOnlySelectedHeight_spec
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (∀ᶠ m : ℕ in atTop,
        reciprocalSigmaOnlyRunningHeight sigma selection (m : ℝ) ≤
          carlsonPolynomialHeight
            (reciprocalSigmaOnlyOuterExponent sigma) (m : ℝ)) ∧
      Tendsto
        (fun m : ℕ => reciprocalSigmaOnlyRunningHeight sigma selection (m : ℝ))
        atTop atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate
        (reciprocalSigmaOnlyBeta0 sigma)
        (reciprocalSigmaOnlyRunningHeight sigma selection) := by
  rcases reciprocalSigmaOnlyParameters_spec hhalf hone with
    ⟨_, hbeta, _, _, hinner, hinnerOne, hcontour, hinnerOuter, _, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · exact tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedUniformGoodHeight_le_polynomialHeight
        hinner hinnerOuter selection)
  · exact (selectedUniformGoodHeight_tendsto_atTop hinner selection).comp
      tendsto_natCast_atTop_atTop
  · exact selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta hinner hinnerOne hcontour selection

/-- Sigma-only running-boundary upper and conditional signed transfer with
all analytic and boundary parameters discharged automatically. -/
theorem actualReciprocalSigmaOnlyRunningBoundaryUnifiedUpperSignedOmega
    {sigma eta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (heta : 0 < eta) (hloss : 0 < loss) (hlossC : loss < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (reciprocalSigmaOnlyVisibleMain sigma selection)
        (fun m : ℕ =>
          c * reciprocalSigmaOnlyAmplitude sigma selection (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (reciprocalSigmaOnlyVisibleMain sigma selection)
        (fun m : ℕ =>
          c * reciprocalSigmaOnlyAmplitude sigma selection (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            reciprocalSigmaOnlyAmplitude sigma selection (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) *
            x ^ reciprocalSigmaOnlyRunningBoundary sigma selection x) := by
  rcases reciprocalSigmaOnlyParameters_spec hhalf hone with
    ⟨_, hbeta0, _, hreal, _, _, _, _, halpha, hepsilon, hmargin⟩
  rcases reciprocalSigmaOnlySelectedHeight_spec hhalf hone selection with
    ⟨hHle, hHtop, remainder⟩
  exact actualMonotoneVariableBoundaryUnifiedUpperSignedOmega_reciprocal
    heta hloss hlossC hbeta0
    (Filter.univ_mem' fun m =>
      beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast
        (reciprocalSigmaOnlyRunningHeight sigma selection)
        (reciprocalSigmaOnlyBeta0 sigma) m)
    (naturalRunningVisibleZeroBoundaryReal_sampled_monotone
      (reciprocalSigmaOnlyRunningHeight sigma selection)
      (reciprocalSigmaOnlyBeta0 sigma))
    hHle hHtop halpha hepsilon hmargin hreal hhalf hone
    (naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge
      (sigma := sigma)
      (reciprocalSigmaOnlyRunningHeight sigma selection)
      (reciprocalSigmaOnlyBeta0 sigma))
    remainder hmainPos hmainNeg

end

end PrimeNumberTheorem
