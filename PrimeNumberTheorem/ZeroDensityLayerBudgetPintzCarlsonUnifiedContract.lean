import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonUnified

namespace PrimeNumberTheorem

/-!
# Contract for the Pintz-Carlson unified transfer

The example fixes the public theorem shape: a Pintz dynamic grid and eventual
zero-free input, an explicit-formula upper certificate, Carlson strip decay,
and a far oscillation witness produce one eventual bidirectional result.
-/

example
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
  constructPintzCarlsonUnifiedDynamicZeroTransfer
    pintzInput
    hamplitude
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
