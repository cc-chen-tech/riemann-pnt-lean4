import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonKernelAdapter

/-!
# One-step zero-free Carlson unified transfer

These constructors internalize the final adapter conversion.  The caller
supplies a zero-free dynamic candidate grid, a conditional explicit-formula
upper certificate, normalized Carlson majorants, and the finite-cluster lower
inputs.  The output carries the selected dynamic height together with upper
and oscillation conclusions.
-/

namespace PrimeNumberTheorem

/--
One-step absolute-Omega unified transfer from zero-free and Carlson-majorant
inputs.
-/
noncomputable def constructZeroFreeCarlsonUnifiedDynamicZeroTransfer
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ} {grid : DynamicFiniteHeightGrid}
    {zeroFree : ℝ → ℝ → Prop}
    {admissible : ℝ → ℝ → Prop} {slack : ℝ → ℝ}
    {layers : Finset ι} {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (zeroFreeHeights :
      DynamicZeroFreeHeightCertificate zeroFree grid)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree)
    (costCover :
      DynamicFiniteGridCostCover cost grid admissible slack)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError layers
        (dynamicFiniteGridOptimalHeight cost grid)
        layerTerm truncation compact)
    (htruncation :
      Filter.Tendsto truncation Filter.atTop (nhds 0))
    (hcompact :
      Filter.Tendsto compact Filter.atTop (nhds 0))
    (hmain : HasFarNormWitness main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder
        (dynamicFiniteGridOptimalHeight cost grid)
        (finiteLayerBudget layers layerTerm))
    (carlsonAdapter :
      CarlsonKernelMajorantLayerAdapter layers
        (dynamicFiniteGridOptimalHeight cost grid) layerTerm)
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    UnifiedDynamicZeroTransferResult upperError lowerError cost grid
      admissible slack amplitude :=
  constructZeroFreeUnifiedDynamicZeroTransfer
    hamplitude zeroFreeHeights explicitFormula costCover
      upperCertificate htruncation hcompact hmain
      remainderCertificate carlsonAdapter.toKernelDensityFactorization
      hdecomp

/--
One-step Omega-plus/minus unified transfer from the same zero-free and Carlson
inputs.
-/
noncomputable def constructZeroFreeCarlsonUnifiedDynamicSignedZeroTransfer
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ} {grid : DynamicFiniteHeightGrid}
    {zeroFree : ℝ → ℝ → Prop}
    {admissible : ℝ → ℝ → Prop} {slack : ℝ → ℝ}
    {layers : Finset ι} {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (zeroFreeHeights :
      DynamicZeroFreeHeightCertificate zeroFree grid)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree)
    (costCover :
      DynamicFiniteGridCostCover cost grid admissible slack)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError layers
        (dynamicFiniteGridOptimalHeight cost grid)
        layerTerm truncation compact)
    (htruncation :
      Filter.Tendsto truncation Filter.atTop (nhds 0))
    (hcompact :
      Filter.Tendsto compact Filter.atTop (nhds 0))
    (hmain : HasFarSignedWitnesses main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder
        (dynamicFiniteGridOptimalHeight cost grid)
        (finiteLayerBudget layers layerTerm))
    (carlsonAdapter :
      CarlsonKernelMajorantLayerAdapter layers
        (dynamicFiniteGridOptimalHeight cost grid) layerTerm)
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    UnifiedDynamicSignedZeroTransferResult upperError lowerError cost grid
      admissible slack amplitude :=
  constructZeroFreeUnifiedDynamicSignedZeroTransfer
    hamplitude zeroFreeHeights explicitFormula costCover
      upperCertificate htruncation hcompact hmain
      remainderCertificate carlsonAdapter.toKernelDensityFactorization
      hdecomp

end PrimeNumberTheorem
