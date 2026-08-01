import PrimeNumberTheorem.ZeroDensityLayerBudgetNearOptimalSigmaOnlyTransfer

/-!
# Prescribed-height sigma-only reciprocal transfer

For every prescribed polynomial height exponent `0 < alpha < 1`, this module
chooses an automatic reciprocal anchor sufficiently close to one, constructs a
selected height below `x^alpha`, and installs that height in the unified PNT
upper and conditional signed transfer.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- The automatic anchor is at least the sigma-only midpoint anchor and at
least `1 - alpha / 2`. -/
noncomputable def prescribedHeightSigmaOnlyBeta0
    (sigma alpha : ℝ) : ℝ :=
  max (reciprocalSigmaOnlyBeta0 sigma) (1 - alpha / 2)

/-- Midpoint between the contour floor and the prescribed outer exponent. -/
noncomputable def prescribedHeightSigmaOnlyInnerExponent
    (sigma alpha : ℝ) : ℝ :=
  (1 - prescribedHeightSigmaOnlyBeta0 sigma alpha + alpha) / 2

noncomputable def prescribedHeightSigmaOnlyEpsilon
    (sigma alpha : ℝ) : ℝ :=
  (prescribedHeightSigmaOnlyBeta0 sigma alpha - sigma) / 2

noncomputable def prescribedHeightSigmaOnlyRunningHeight
    (sigma alpha : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  selectedUniformGoodHeight
    (prescribedHeightSigmaOnlyInnerExponent sigma alpha) selection

noncomputable def prescribedHeightSigmaOnlyRunningBoundary
    (sigma alpha : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  naturalRunningVisibleZeroBoundaryReal
    (prescribedHeightSigmaOnlyRunningHeight sigma alpha selection)
    (prescribedHeightSigmaOnlyBeta0 sigma alpha)

noncomputable def prescribedHeightSigmaOnlyVisibleMain
    (sigma alpha : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℕ → ℝ :=
  fun m =>
    dynamicVisibleClusterPNTMain
      (prescribedHeightSigmaOnlyRunningHeight sigma alpha selection)
      (variableBoundaryZeroPackage
        (prescribedHeightSigmaOnlyRunningHeight sigma alpha selection)
        (prescribedHeightSigmaOnlyRunningBoundary sigma alpha selection)
        (m : ℝ))
      (m : ℝ)

noncomputable def prescribedHeightSigmaOnlyAmplitude
    (sigma alpha : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  variableBoundaryTargetAmplitude
    (prescribedHeightSigmaOnlyRunningBoundary sigma alpha selection)

/-- The alpha-dependent anchor lies to the right of all fixed obstructions,
and its contour floor lies strictly below the prescribed exponent. -/
theorem prescribedHeightSigmaOnlyParameters_spec
    {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (halphaOne : alpha < 1) :
    sigma < prescribedHeightSigmaOnlyBeta0 sigma alpha ∧
      0 < prescribedHeightSigmaOnlyBeta0 sigma alpha ∧
      prescribedHeightSigmaOnlyBeta0 sigma alpha < 1 ∧
      (∀ rho ∈ realOrdinateNontrivialZerosFinset 0,
        rho.re < prescribedHeightSigmaOnlyBeta0 sigma alpha) ∧
      1 - alpha / 2 ≤ prescribedHeightSigmaOnlyBeta0 sigma alpha ∧
      1 - prescribedHeightSigmaOnlyBeta0 sigma alpha ≤ alpha / 2 ∧
      IsReciprocalContourHeightWindow
        (prescribedHeightSigmaOnlyBeta0 sigma alpha)
        (prescribedHeightSigmaOnlyInnerExponent sigma alpha) alpha ∧
      0 < prescribedHeightSigmaOnlyEpsilon sigma alpha ∧
      sigma - prescribedHeightSigmaOnlyBeta0 sigma alpha +
          prescribedHeightSigmaOnlyEpsilon sigma alpha < 0 := by
  rcases reciprocalSigmaOnlyParameters_spec hhalf hone with
    ⟨hsigmaOld, hbetaOld, hbetaOldOne, hrealOld, _, _, _, _, _, _, _⟩
  have hOldLe : reciprocalSigmaOnlyBeta0 sigma ≤
      prescribedHeightSigmaOnlyBeta0 sigma alpha := by
    exact le_max_left _ _
  have hTrade : 1 - alpha / 2 ≤
      prescribedHeightSigmaOnlyBeta0 sigma alpha := by
    exact le_max_right _ _
  have hsigmaBeta : sigma < prescribedHeightSigmaOnlyBeta0 sigma alpha :=
    hsigmaOld.trans_le hOldLe
  have hbeta : 0 < prescribedHeightSigmaOnlyBeta0 sigma alpha :=
    hbetaOld.trans_le hOldLe
  have hbetaOne : prescribedHeightSigmaOnlyBeta0 sigma alpha < 1 := by
    unfold prescribedHeightSigmaOnlyBeta0
    exact max_lt hbetaOldOne (by linarith)
  have hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0,
        rho.re < prescribedHeightSigmaOnlyBeta0 sigma alpha := by
    intro rho hrho
    exact (hrealOld rho hrho).trans_le hOldLe
  have hfloorHalf :
      1 - prescribedHeightSigmaOnlyBeta0 sigma alpha ≤ alpha / 2 := by
    linarith
  have hfloorAlpha :
      1 - prescribedHeightSigmaOnlyBeta0 sigma alpha < alpha := by
    linarith
  have hinner : 0 < prescribedHeightSigmaOnlyInnerExponent sigma alpha := by
    unfold prescribedHeightSigmaOnlyInnerExponent
    linarith
  have hinnerOne :
      prescribedHeightSigmaOnlyInnerExponent sigma alpha ≤ 1 := by
    unfold prescribedHeightSigmaOnlyInnerExponent
    linarith
  have hcontour :
      1 - prescribedHeightSigmaOnlyBeta0 sigma alpha <
        prescribedHeightSigmaOnlyInnerExponent sigma alpha := by
    unfold prescribedHeightSigmaOnlyInnerExponent
    linarith
  have hinnerAlpha :
      prescribedHeightSigmaOnlyInnerExponent sigma alpha < alpha := by
    unfold prescribedHeightSigmaOnlyInnerExponent
    linarith
  have hwindow :
      IsReciprocalContourHeightWindow
        (prescribedHeightSigmaOnlyBeta0 sigma alpha)
        (prescribedHeightSigmaOnlyInnerExponent sigma alpha) alpha :=
    ⟨hinner, hinnerOne, hcontour, hinnerAlpha⟩
  have hepsilon : 0 < prescribedHeightSigmaOnlyEpsilon sigma alpha := by
    unfold prescribedHeightSigmaOnlyEpsilon
    linarith
  have hmargin :
      sigma - prescribedHeightSigmaOnlyBeta0 sigma alpha +
          prescribedHeightSigmaOnlyEpsilon sigma alpha < 0 := by
    unfold prescribedHeightSigmaOnlyEpsilon
    linarith
  exact ⟨hsigmaBeta, hbeta, hbetaOne, hreal, hTrade, hfloorHalf,
    hwindow, hepsilon, hmargin⟩

/-- The automatic alpha-dependent anchor produces an actual cofinal selected
height eventually bounded by the prescribed polynomial height `x^alpha`. -/
theorem prescribedHeightSigmaOnlySelectedHeight_spec
    {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (halphaOne : alpha < 1)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (∀ᶠ m : ℕ in atTop,
        prescribedHeightSigmaOnlyRunningHeight sigma alpha selection (m : ℝ) ≤
          carlsonPolynomialHeight alpha (m : ℝ)) ∧
      Tendsto
        (fun m : ℕ =>
          prescribedHeightSigmaOnlyRunningHeight sigma alpha selection (m : ℝ))
        atTop atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate
        (prescribedHeightSigmaOnlyBeta0 sigma alpha)
        (prescribedHeightSigmaOnlyRunningHeight sigma alpha selection) := by
  rcases prescribedHeightSigmaOnlyParameters_spec
      hhalf hone halpha halphaOne with
    ⟨_, hbeta, _, _, _, _, hwindow, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · exact tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedUniformGoodHeight_le_polynomialHeight
        hwindow.1 hwindow.2.2.2 selection)
  · exact
      (selectedUniformGoodHeight_tendsto_atTop hwindow.1 selection).comp
        tendsto_natCast_atTop_atTop
  · exact selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta hwindow.1 hwindow.2.1 hwindow.2.2.1 selection

/-- Unified PNT upper and conditional signed transfer using an actual selected
height eventually bounded by the prescribed exponent `alpha`. -/
theorem actualPrescribedHeightSigmaOnlyUnifiedUpperSignedOmega
    {sigma alpha eta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (halphaOne : alpha < 1)
    (heta : 0 < eta) (hloss : 0 < loss) (hlossC : loss < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (prescribedHeightSigmaOnlyVisibleMain sigma alpha selection)
        (fun m : ℕ =>
          c * prescribedHeightSigmaOnlyAmplitude sigma alpha selection (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (prescribedHeightSigmaOnlyVisibleMain sigma alpha selection)
        (fun m : ℕ =>
          c * prescribedHeightSigmaOnlyAmplitude sigma alpha selection (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            prescribedHeightSigmaOnlyAmplitude sigma alpha selection (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) *
            x ^ prescribedHeightSigmaOnlyRunningBoundary sigma alpha selection x) := by
  rcases prescribedHeightSigmaOnlyParameters_spec
      hhalf hone halpha halphaOne with
    ⟨_, hbeta0, _, hreal, _, _, _, hepsilon, hmargin⟩
  rcases prescribedHeightSigmaOnlySelectedHeight_spec
      hhalf hone halpha halphaOne selection with
    ⟨hHle, hHtop, remainder⟩
  exact actualMonotoneVariableBoundaryUnifiedUpperSignedOmega_reciprocal
    heta hloss hlossC hbeta0
    (Filter.univ_mem' fun m =>
      beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast
        (prescribedHeightSigmaOnlyRunningHeight sigma alpha selection)
        (prescribedHeightSigmaOnlyBeta0 sigma alpha) m)
    (naturalRunningVisibleZeroBoundaryReal_sampled_monotone
      (prescribedHeightSigmaOnlyRunningHeight sigma alpha selection)
      (prescribedHeightSigmaOnlyBeta0 sigma alpha))
    hHle hHtop halpha hepsilon hmargin hreal hhalf hone
    (naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge
      (sigma := sigma)
      (prescribedHeightSigmaOnlyRunningHeight sigma alpha selection)
      (prescribedHeightSigmaOnlyBeta0 sigma alpha))
    remainder hmainPos hmainNeg

end

end PrimeNumberTheorem
