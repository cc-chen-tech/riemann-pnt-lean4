import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonRateGrid

/-!
# Concrete rate-grid Pintz--Carlson unified transfer

The constructors here automatically extract the optimizer's rate from the
finite adaptive grid, removing the manual optimizer-height equality required by
the lower-level concrete constructors.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Absolute-omega transfer with an automatically selected finite-grid rate. -/
noncomputable def constructRateGridClassicalCarlsonUnifiedDynamicZeroTransfer
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ}
    {zeroFree admissible : ℝ → ℝ → Prop}
    {slack truncation compact : ℝ → ℝ}
    {amplitude : ℝ}
    (layers : Finset ι) (sigma : ι → ℝ)
    (rateInput : PintzCarlsonRateGridInput zeroFree)
    (package :
      AdaptiveClassicalCarlsonDensityAdapterPackage
        layers sigma rateInput.rates)
    (hratesGap : ∀ k ∈ rateInput.rates,
      k < 2 * Real.sqrt package.c)
    (hamplitude : 0 < amplitude)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree)
    (costCover :
      DynamicFiniteGridCostCover cost
        rateInput.toPintzEnvelopeDynamicGridInput.toDynamicFiniteHeightGrid
        admissible slack)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError ({()} : Finset Unit)
        (dynamicFiniteGridOptimalHeight cost
          rateInput.toPintzEnvelopeDynamicGridInput.toDynamicFiniteHeightGrid)
        (pintzCarlsonClassicalAggregatedDensityLayerTerm layers sigma)
        truncation compact)
    (htruncation : Tendsto truncation atTop (𝓝 0))
    (hcompact : Tendsto compact atTop (𝓝 0))
    (hmain : HasFarNormWitness main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder
        (dynamicFiniteGridOptimalHeight cost
          rateInput.toPintzEnvelopeDynamicGridInput.toDynamicFiniteHeightGrid)
        (finiteLayerBudget ({()} : Finset Unit)
          (pintzCarlsonClassicalAggregatedDensityLayerTerm layers sigma)))
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    EventuallyUnifiedDynamicZeroTransferResult upperError lowerError cost
      rateInput.toPintzEnvelopeDynamicGridInput.toDynamicFiniteHeightGrid
      admissible slack amplitude :=
  constructAdaptiveClassicalCarlsonUnifiedDynamicZeroTransfer
    layers sigma rateInput.rates package
    (rateInput.optimalRate cost)
    (rateInput.optimalRate_mem cost)
    rateInput.rates_pos hratesGap
    rateInput.toPintzEnvelopeDynamicGridInput
    (rateInput.optimalHeight_eq cost)
    hamplitude explicitFormula costCover upperCertificate
    htruncation hcompact hmain remainderCertificate hdecomp

/-- Signed-omega transfer with an automatically selected finite-grid rate. -/
noncomputable def constructRateGridClassicalCarlsonUnifiedDynamicSignedZeroTransfer
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ}
    {zeroFree admissible : ℝ → ℝ → Prop}
    {slack truncation compact : ℝ → ℝ}
    {amplitude : ℝ}
    (layers : Finset ι) (sigma : ι → ℝ)
    (rateInput : PintzCarlsonRateGridInput zeroFree)
    (package :
      AdaptiveClassicalCarlsonDensityAdapterPackage
        layers sigma rateInput.rates)
    (hratesGap : ∀ k ∈ rateInput.rates,
      k < 2 * Real.sqrt package.c)
    (hamplitude : 0 < amplitude)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree)
    (costCover :
      DynamicFiniteGridCostCover cost
        rateInput.toPintzEnvelopeDynamicGridInput.toDynamicFiniteHeightGrid
        admissible slack)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError ({()} : Finset Unit)
        (dynamicFiniteGridOptimalHeight cost
          rateInput.toPintzEnvelopeDynamicGridInput.toDynamicFiniteHeightGrid)
        (pintzCarlsonClassicalAggregatedDensityLayerTerm layers sigma)
        truncation compact)
    (htruncation : Tendsto truncation atTop (𝓝 0))
    (hcompact : Tendsto compact atTop (𝓝 0))
    (hmain : HasFarSignedWitnesses main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder
        (dynamicFiniteGridOptimalHeight cost
          rateInput.toPintzEnvelopeDynamicGridInput.toDynamicFiniteHeightGrid)
        (finiteLayerBudget ({()} : Finset Unit)
          (pintzCarlsonClassicalAggregatedDensityLayerTerm layers sigma)))
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    EventuallyUnifiedDynamicSignedZeroTransferResult upperError lowerError cost
      rateInput.toPintzEnvelopeDynamicGridInput.toDynamicFiniteHeightGrid
      admissible slack amplitude :=
  constructAdaptiveClassicalCarlsonUnifiedDynamicSignedZeroTransfer
    layers sigma rateInput.rates package
    (rateInput.optimalRate cost)
    (rateInput.optimalRate_mem cost)
    rateInput.rates_pos hratesGap
    rateInput.toPintzEnvelopeDynamicGridInput
    (rateInput.optimalHeight_eq cost)
    hamplitude explicitFormula costCover upperCertificate
    htruncation hcompact hmain remainderCertificate hdecomp

end PrimeNumberTheorem
