import PrimeNumberTheorem.ZeroDensityLayerBudgetZeroFreeUnified

namespace PrimeNumberTheorem

example
    {upperError : ℝ → ℝ} {cost : ℝ → ℝ → ℝ}
    {zeroFree : ℝ → ℝ → Prop}
    {grid : DynamicFiniteHeightGrid}
    (zeroFreeHeights :
      DynamicZeroFreeHeightCertificate zeroFree grid)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree)
    (x : ℝ) :
    |upperError x| ≤
      cost x (dynamicFiniteGridOptimalHeight cost grid x) :=
  zeroFreeExplicitFormula_upper_at_dynamicOptimalHeight
    zeroFreeHeights explicitFormula x

noncomputable example
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
    (factorization :
      CarlsonKernelLayerFactorization layers
        (dynamicFiniteGridOptimalHeight cost grid) layerTerm)
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    UnifiedDynamicZeroTransferResult upperError lowerError cost grid
      admissible slack amplitude :=
  constructZeroFreeUnifiedDynamicZeroTransfer
    hamplitude zeroFreeHeights explicitFormula costCover
      upperCertificate htruncation hcompact hmain
      remainderCertificate factorization hdecomp

end PrimeNumberTheorem
