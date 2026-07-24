import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzGrid

namespace PrimeNumberTheorem

/-!
# Pintz-Carlson unified dynamic transfer

A Pintz envelope supplies a diverging finite grid whose candidates are
eventually zero-free. Carlson layer adapters supply decay of every real-part
strip. The selected optimizer then carries both an explicit-formula upper
bound and an oscillation lower bound.

No concrete zero-density theorem is asserted here. The Carlson adapter remains
the interface at which quantitative density and kernel estimates are verified.
-/

/-- Construct the eventual absolute-value transfer result from a Pintz
envelope, eventual zero-freeness, Carlson strip decay, and a far witness. -/
noncomputable def constructPintzCarlsonUnifiedDynamicZeroTransfer
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ}
    {zeroFree admissible : ℝ → ℝ → Prop}
    {slack : ℝ → ℝ}
    {layers : Finset ι}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ}
    {amplitude : ℝ}
    (pintzInput : PintzEnvelopeDynamicGridInput zeroFree)
    (hamplitude : 0 < amplitude)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree)
    (costCover :
      DynamicFiniteGridCostCover cost pintzInput.toDynamicFiniteHeightGrid
        admissible slack)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError layers
        (dynamicFiniteGridOptimalHeight cost
          pintzInput.toDynamicFiniteHeightGrid)
        layerTerm truncation compact)
    (htruncation : Tendsto truncation atTop (nhds 0))
    (hcompact : Tendsto compact atTop (nhds 0))
    (hmain : HasFarNormWitness main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder
        (dynamicFiniteGridOptimalHeight cost
          pintzInput.toDynamicFiniteHeightGrid)
        (finiteLayerBudget layers layerTerm))
    (carlsonAdapter :
      CarlsonKernelMajorantLayerAdapter layers
        (dynamicFiniteGridOptimalHeight cost
          pintzInput.toDynamicFiniteHeightGrid)
        layerTerm)
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    EventuallyUnifiedDynamicZeroTransferResult upperError lowerError cost
      pintzInput.toDynamicFiniteHeightGrid admissible slack amplitude :=
  constructEventuallyZeroFreeCarlsonUnifiedDynamicZeroTransfer
    hamplitude
    pintzInput.toEventuallyZeroFreeHeightCertificate
    explicitFormula
    costCover
    upperCertificate
    htruncation
    hcompact
    hmain
    remainderCertificate
    carlsonAdapter
    hdecomp

/-- Signed version of `constructPintzCarlsonUnifiedDynamicZeroTransfer`,
yielding both positive and negative far witnesses. -/
noncomputable def constructPintzCarlsonUnifiedDynamicZeroTransferSigned
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ}
    {zeroFree admissible : ℝ → ℝ → Prop}
    {slack : ℝ → ℝ}
    {layers : Finset ι}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ}
    {amplitude : ℝ}
    (pintzInput : PintzEnvelopeDynamicGridInput zeroFree)
    (hamplitude : 0 < amplitude)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree)
    (costCover :
      DynamicFiniteGridCostCover cost pintzInput.toDynamicFiniteHeightGrid
        admissible slack)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError layers
        (dynamicFiniteGridOptimalHeight cost
          pintzInput.toDynamicFiniteHeightGrid)
        layerTerm truncation compact)
    (htruncation : Tendsto truncation atTop (nhds 0))
    (hcompact : Tendsto compact atTop (nhds 0))
    (hmain : HasFarSignedWitnesses main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder
        (dynamicFiniteGridOptimalHeight cost
          pintzInput.toDynamicFiniteHeightGrid)
        (finiteLayerBudget layers layerTerm))
    (carlsonAdapter :
      CarlsonKernelMajorantLayerAdapter layers
        (dynamicFiniteGridOptimalHeight cost
          pintzInput.toDynamicFiniteHeightGrid)
        layerTerm)
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    EventuallyUnifiedDynamicZeroTransferSignedResult upperError lowerError cost
      pintzInput.toDynamicFiniteHeightGrid admissible slack amplitude :=
  constructEventuallyZeroFreeCarlsonUnifiedDynamicZeroTransferSigned
    hamplitude
    pintzInput.toEventuallyZeroFreeHeightCertificate
    explicitFormula
    costCover
    upperCertificate
    htruncation
    hcompact
    hmain
    remainderCertificate
    carlsonAdapter
    hdecomp

end PrimeNumberTheorem
