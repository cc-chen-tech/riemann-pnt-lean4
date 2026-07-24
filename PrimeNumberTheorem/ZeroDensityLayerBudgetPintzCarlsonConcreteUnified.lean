import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonConcreteAdapter

/-!
# Concrete Pintz--Carlson unified transfer

These constructors feed the actual Carlson zero-count adapter directly into the
Pintz-grid unified transfer machine. They expose, rather than assume away, the
remaining analytic interfaces: optimizer-height identification, explicit
formula domination, truncation decay, and the main oscillatory witness.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- The aggregated layer specialized to the project's multiplicity-counted
zero-density function. -/
noncomputable def pintzCarlsonClassicalAggregatedDensityLayerTerm
    {ι : Type*} (layers : Finset ι) (sigma : ι → ℝ) :
    Unit → ℝ → ℝ → ℝ :=
  pintzCarlsonAggregatedDensityLayerTerm layers
    (fun i T => (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))

/-- Concrete absolute-omega transfer using the actual Carlson zero count. -/
noncomputable def constructAdaptiveClassicalCarlsonUnifiedDynamicZeroTransfer
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ}
    {zeroFree admissible : ℝ → ℝ → Prop}
    {slack : ℝ → ℝ}
    {truncation compact : ℝ → ℝ}
    {amplitude : ℝ}
    (layers : Finset ι) (sigma : ι → ℝ) (rates : Finset ℝ)
    (package : AdaptiveClassicalCarlsonDensityAdapterPackage layers sigma rates)
    (selectRate : ℝ → ℝ)
    (hselect : ∀ x, selectRate x ∈ rates)
    (hratesPos : ∀ k ∈ rates, 0 < k)
    (hratesGap : ∀ k ∈ rates, k < 2 * Real.sqrt package.c)
    (pintzInput : PintzEnvelopeDynamicGridInput zeroFree)
    (hheight : ∀ x,
      dynamicFiniteGridOptimalHeight cost pintzInput.toDynamicFiniteHeightGrid x =
        pintzCarlsonHeight (selectRate x) x)
    (hamplitude : 0 < amplitude)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree)
    (costCover :
      DynamicFiniteGridCostCover cost pintzInput.toDynamicFiniteHeightGrid
        admissible slack)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError ({()} : Finset Unit)
        (dynamicFiniteGridOptimalHeight cost pintzInput.toDynamicFiniteHeightGrid)
        (pintzCarlsonClassicalAggregatedDensityLayerTerm layers sigma)
        truncation compact)
    (htruncation : Tendsto truncation atTop (𝓝 0))
    (hcompact : Tendsto compact atTop (𝓝 0))
    (hmain : HasFarNormWitness main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder
        (dynamicFiniteGridOptimalHeight cost pintzInput.toDynamicFiniteHeightGrid)
        (finiteLayerBudget ({()} : Finset Unit)
          (pintzCarlsonClassicalAggregatedDensityLayerTerm layers sigma)))
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    EventuallyUnifiedDynamicZeroTransferResult upperError lowerError cost
      pintzInput.toDynamicFiniteHeightGrid admissible slack amplitude :=
  constructPintzCarlsonUnifiedDynamicZeroTransfer
    pintzInput hamplitude explicitFormula costCover upperCertificate
    htruncation hcompact hmain remainderCertificate
    (package.adapter selectRate hselect hratesPos hratesGap
      (dynamicFiniteGridOptimalHeight cost pintzInput.toDynamicFiniteHeightGrid)
      hheight)
    hdecomp

/-- Concrete signed-omega transfer using the actual Carlson zero count. -/
noncomputable def constructAdaptiveClassicalCarlsonUnifiedDynamicSignedZeroTransfer
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ}
    {zeroFree admissible : ℝ → ℝ → Prop}
    {slack : ℝ → ℝ}
    {truncation compact : ℝ → ℝ}
    {amplitude : ℝ}
    (layers : Finset ι) (sigma : ι → ℝ) (rates : Finset ℝ)
    (package : AdaptiveClassicalCarlsonDensityAdapterPackage layers sigma rates)
    (selectRate : ℝ → ℝ)
    (hselect : ∀ x, selectRate x ∈ rates)
    (hratesPos : ∀ k ∈ rates, 0 < k)
    (hratesGap : ∀ k ∈ rates, k < 2 * Real.sqrt package.c)
    (pintzInput : PintzEnvelopeDynamicGridInput zeroFree)
    (hheight : ∀ x,
      dynamicFiniteGridOptimalHeight cost pintzInput.toDynamicFiniteHeightGrid x =
        pintzCarlsonHeight (selectRate x) x)
    (hamplitude : 0 < amplitude)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree)
    (costCover :
      DynamicFiniteGridCostCover cost pintzInput.toDynamicFiniteHeightGrid
        admissible slack)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError ({()} : Finset Unit)
        (dynamicFiniteGridOptimalHeight cost pintzInput.toDynamicFiniteHeightGrid)
        (pintzCarlsonClassicalAggregatedDensityLayerTerm layers sigma)
        truncation compact)
    (htruncation : Tendsto truncation atTop (𝓝 0))
    (hcompact : Tendsto compact atTop (𝓝 0))
    (hmain : HasFarSignedWitnesses main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder
        (dynamicFiniteGridOptimalHeight cost pintzInput.toDynamicFiniteHeightGrid)
        (finiteLayerBudget ({()} : Finset Unit)
          (pintzCarlsonClassicalAggregatedDensityLayerTerm layers sigma)))
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    EventuallyUnifiedDynamicSignedZeroTransferResult upperError lowerError cost
      pintzInput.toDynamicFiniteHeightGrid admissible slack amplitude :=
  constructPintzCarlsonUnifiedDynamicZeroTransferSigned
    pintzInput hamplitude explicitFormula costCover upperCertificate
    htruncation hcompact hmain remainderCertificate
    (package.adapter selectRate hselect hratesPos hratesGap
      (dynamicFiniteGridOptimalHeight cost pintzInput.toDynamicFiniteHeightGrid)
      hheight)
    hdecomp

end PrimeNumberTheorem
