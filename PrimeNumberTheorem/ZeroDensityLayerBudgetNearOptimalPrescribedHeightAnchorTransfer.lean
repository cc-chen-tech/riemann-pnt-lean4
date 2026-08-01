import PrimeNumberTheorem.ZeroDensityLayerBudgetPrescribedHeightSigmaOnlyTransfer

/-!
# Near-optimal anchor for a prescribed height

For a fixed outer height exponent `alpha`, the contour window forces
`beta > 1 - alpha`.  Together with the automatic midpoint anchor, this gives
the anchor floor `max betaMid (1 - alpha)`.  This module realizes that floor
within every positive `delta` and installs the resulting anchor in the unified
PNT transfer.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

noncomputable def prescribedHeightAnchorFloor
    (sigma alpha : ℝ) : ℝ :=
  max (reciprocalSigmaOnlyBeta0 sigma) (1 - alpha)

noncomputable def nearOptimalPrescribedHeightBeta0
    (sigma alpha delta : ℝ) : ℝ :=
  max (reciprocalSigmaOnlyBeta0 sigma) (1 - alpha + delta)

noncomputable def nearOptimalPrescribedHeightInnerExponent
    (sigma alpha delta : ℝ) : ℝ :=
  (1 - nearOptimalPrescribedHeightBeta0 sigma alpha delta + alpha) / 2

noncomputable def nearOptimalPrescribedHeightEpsilon
    (sigma alpha delta : ℝ) : ℝ :=
  (nearOptimalPrescribedHeightBeta0 sigma alpha delta - sigma) / 2

noncomputable def nearOptimalPrescribedHeightRunningHeight
    (sigma alpha delta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  selectedUniformGoodHeight
    (nearOptimalPrescribedHeightInnerExponent sigma alpha delta) selection

noncomputable def nearOptimalPrescribedHeightRunningBoundary
    (sigma alpha delta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  naturalRunningVisibleZeroBoundaryReal
    (nearOptimalPrescribedHeightRunningHeight sigma alpha delta selection)
    (nearOptimalPrescribedHeightBeta0 sigma alpha delta)

noncomputable def nearOptimalPrescribedHeightVisibleMain
    (sigma alpha delta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℕ → ℝ :=
  fun m =>
    dynamicVisibleClusterPNTMain
      (nearOptimalPrescribedHeightRunningHeight sigma alpha delta selection)
      (variableBoundaryZeroPackage
        (nearOptimalPrescribedHeightRunningHeight sigma alpha delta selection)
        (nearOptimalPrescribedHeightRunningBoundary sigma alpha delta selection)
        (m : ℝ))
      (m : ℝ)

noncomputable def nearOptimalPrescribedHeightAmplitude
    (sigma alpha delta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  variableBoundaryTargetAmplitude
    (nearOptimalPrescribedHeightRunningBoundary sigma alpha delta selection)

/-- Every feasible prescribed-height contour window whose anchor is no smaller
than the sigma-only midpoint anchor lies above the fixed-height anchor floor. -/
theorem prescribedHeightAnchorFloor_le_of_window
    {sigma alpha beta inner : ℝ}
    (hbase : reciprocalSigmaOnlyBeta0 sigma ≤ beta)
    (hwindow : IsReciprocalContourHeightWindow beta inner alpha) :
    prescribedHeightAnchorFloor sigma alpha ≤ beta := by
  unfold prescribedHeightAnchorFloor
  exact max_le hbase (le_of_lt (by linarith [hwindow.2.2.1.trans hwindow.2.2.2]))

/-- The delta-dependent anchor realizes the fixed-height anchor floor from
above within additive error `delta`. -/
theorem nearOptimalPrescribedHeightBeta0_within
    {sigma alpha delta : ℝ} (hdelta : 0 < delta) :
    prescribedHeightAnchorFloor sigma alpha ≤
        nearOptimalPrescribedHeightBeta0 sigma alpha delta ∧
      nearOptimalPrescribedHeightBeta0 sigma alpha delta ≤
        prescribedHeightAnchorFloor sigma alpha + delta := by
  have hOldFloor : reciprocalSigmaOnlyBeta0 sigma ≤
      prescribedHeightAnchorFloor sigma alpha := le_max_left _ _
  have hBoundaryFloor : 1 - alpha ≤
      prescribedHeightAnchorFloor sigma alpha := le_max_right _ _
  have hOldCandidate : reciprocalSigmaOnlyBeta0 sigma ≤
      nearOptimalPrescribedHeightBeta0 sigma alpha delta := le_max_left _ _
  have hBoundaryCandidate : 1 - alpha + delta ≤
      nearOptimalPrescribedHeightBeta0 sigma alpha delta := le_max_right _ _
  constructor
  · unfold prescribedHeightAnchorFloor
    exact max_le hOldCandidate (by linarith)
  · unfold nearOptimalPrescribedHeightBeta0
    exact max_le (by linarith) (by linarith)

/-- Arithmetic, real-zero, optimality, contour-window, and reciprocal-margin
specification for the near-optimal prescribed-height anchor. -/
theorem nearOptimalPrescribedHeightParameters_spec
    {sigma alpha delta : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halphaOne : alpha < 1)
    (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha) :
    sigma < nearOptimalPrescribedHeightBeta0 sigma alpha delta ∧
      0 < nearOptimalPrescribedHeightBeta0 sigma alpha delta ∧
      nearOptimalPrescribedHeightBeta0 sigma alpha delta < 1 ∧
      (∀ rho ∈ realOrdinateNontrivialZerosFinset 0,
        rho.re < nearOptimalPrescribedHeightBeta0 sigma alpha delta) ∧
      prescribedHeightAnchorFloor sigma alpha ≤
        nearOptimalPrescribedHeightBeta0 sigma alpha delta ∧
      nearOptimalPrescribedHeightBeta0 sigma alpha delta ≤
        prescribedHeightAnchorFloor sigma alpha + delta ∧
      IsReciprocalContourHeightWindow
        (nearOptimalPrescribedHeightBeta0 sigma alpha delta)
        (nearOptimalPrescribedHeightInnerExponent sigma alpha delta) alpha ∧
      0 < nearOptimalPrescribedHeightEpsilon sigma alpha delta ∧
      sigma - nearOptimalPrescribedHeightBeta0 sigma alpha delta +
          nearOptimalPrescribedHeightEpsilon sigma alpha delta < 0 := by
  rcases reciprocalSigmaOnlyParameters_spec hhalf hone with
    ⟨hsigmaOld, hbetaOld, hbetaOldOne, hrealOld, _, _, _, _, _, _, _⟩
  have hOldLe : reciprocalSigmaOnlyBeta0 sigma ≤
      nearOptimalPrescribedHeightBeta0 sigma alpha delta := le_max_left _ _
  have hTrade : 1 - alpha + delta ≤
      nearOptimalPrescribedHeightBeta0 sigma alpha delta := le_max_right _ _
  have hsigmaBeta := hsigmaOld.trans_le hOldLe
  have hbeta : 0 < nearOptimalPrescribedHeightBeta0 sigma alpha delta :=
    hbetaOld.trans_le hOldLe
  have hbetaOne : nearOptimalPrescribedHeightBeta0 sigma alpha delta < 1 := by
    unfold nearOptimalPrescribedHeightBeta0
    exact max_lt hbetaOldOne (by linarith)
  have hreal : ∀ rho ∈ realOrdinateNontrivialZerosFinset 0,
      rho.re < nearOptimalPrescribedHeightBeta0 sigma alpha delta := by
    intro rho hrho
    exact (hrealOld rho hrho).trans_le hOldLe
  rcases nearOptimalPrescribedHeightBeta0_within hdelta with
    ⟨hfloor, hwithin⟩
  have hfloorAlpha :
      1 - nearOptimalPrescribedHeightBeta0 sigma alpha delta < alpha := by
    linarith
  have hinner :
      0 < nearOptimalPrescribedHeightInnerExponent sigma alpha delta := by
    unfold nearOptimalPrescribedHeightInnerExponent
    linarith
  have hinnerOne :
      nearOptimalPrescribedHeightInnerExponent sigma alpha delta ≤ 1 := by
    unfold nearOptimalPrescribedHeightInnerExponent
    linarith
  have hcontour :
      1 - nearOptimalPrescribedHeightBeta0 sigma alpha delta <
        nearOptimalPrescribedHeightInnerExponent sigma alpha delta := by
    unfold nearOptimalPrescribedHeightInnerExponent
    linarith
  have hinnerAlpha :
      nearOptimalPrescribedHeightInnerExponent sigma alpha delta < alpha := by
    unfold nearOptimalPrescribedHeightInnerExponent
    linarith
  have hwindow :
      IsReciprocalContourHeightWindow
        (nearOptimalPrescribedHeightBeta0 sigma alpha delta)
        (nearOptimalPrescribedHeightInnerExponent sigma alpha delta) alpha :=
    ⟨hinner, hinnerOne, hcontour, hinnerAlpha⟩
  have hepsilon :
      0 < nearOptimalPrescribedHeightEpsilon sigma alpha delta := by
    unfold nearOptimalPrescribedHeightEpsilon
    linarith
  have hmargin :
      sigma - nearOptimalPrescribedHeightBeta0 sigma alpha delta +
          nearOptimalPrescribedHeightEpsilon sigma alpha delta < 0 := by
    unfold nearOptimalPrescribedHeightEpsilon
    linarith
  exact ⟨hsigmaBeta, hbeta, hbetaOne, hreal, hfloor, hwithin,
    hwindow, hepsilon, hmargin⟩

theorem nearOptimalPrescribedHeightSelectedHeight_spec
    {sigma alpha delta : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halphaOne : alpha < 1)
    (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (∀ᶠ m : ℕ in atTop,
        nearOptimalPrescribedHeightRunningHeight sigma alpha delta selection
            (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ)) ∧
      Tendsto
        (fun m : ℕ =>
          nearOptimalPrescribedHeightRunningHeight sigma alpha delta selection
            (m : ℝ)) atTop atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate
        (nearOptimalPrescribedHeightBeta0 sigma alpha delta)
        (nearOptimalPrescribedHeightRunningHeight sigma alpha delta selection) := by
  rcases nearOptimalPrescribedHeightParameters_spec
      hhalf hone halphaOne hdelta hdeltaAlpha with
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

theorem actualNearOptimalPrescribedHeightUnifiedUpperSignedOmega
    {sigma alpha delta eta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (halphaOne : alpha < 1)
    (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha)
    (heta : 0 < eta) (hloss : 0 < loss) (hlossC : loss < c)
    (hmainPos : HasFarNaturalPointPositiveTargetAmplitudeWitness
      (nearOptimalPrescribedHeightVisibleMain sigma alpha delta selection)
      (fun m : ℕ => c * nearOptimalPrescribedHeightAmplitude
        sigma alpha delta selection (m : ℝ)))
    (hmainNeg : HasFarNaturalPointNegativeTargetAmplitudeWitness
      (nearOptimalPrescribedHeightVisibleMain sigma alpha delta selection)
      (fun m : ℕ => c * nearOptimalPrescribedHeightAmplitude
        sigma alpha delta selection (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            nearOptimalPrescribedHeightAmplitude
              sigma alpha delta selection (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ => (c - loss) *
          x ^ nearOptimalPrescribedHeightRunningBoundary
            sigma alpha delta selection x) := by
  rcases nearOptimalPrescribedHeightParameters_spec
      hhalf hone halphaOne hdelta hdeltaAlpha with
    ⟨_, hbeta0, _, hreal, _, _, _, hepsilon, hmargin⟩
  rcases nearOptimalPrescribedHeightSelectedHeight_spec
      hhalf hone halphaOne hdelta hdeltaAlpha selection with
    ⟨hHle, hHtop, remainder⟩
  exact actualMonotoneVariableBoundaryUnifiedUpperSignedOmega_reciprocal
    heta hloss hlossC hbeta0
    (Filter.univ_mem' fun m =>
      beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast
        (nearOptimalPrescribedHeightRunningHeight sigma alpha delta selection)
        (nearOptimalPrescribedHeightBeta0 sigma alpha delta) m)
    (naturalRunningVisibleZeroBoundaryReal_sampled_monotone
      (nearOptimalPrescribedHeightRunningHeight sigma alpha delta selection)
      (nearOptimalPrescribedHeightBeta0 sigma alpha delta))
    hHle hHtop halpha hepsilon hmargin hreal hhalf hone
    (naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge
      (sigma := sigma)
      (nearOptimalPrescribedHeightRunningHeight sigma alpha delta selection)
      (nearOptimalPrescribedHeightBeta0 sigma alpha delta))
    remainder hmainPos hmainNeg

end

end PrimeNumberTheorem
