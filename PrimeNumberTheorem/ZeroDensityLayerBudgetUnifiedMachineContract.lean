import PrimeNumberTheorem.ZeroDensityLayerBudgetUnifiedMachine

namespace PrimeNumberTheorem

example
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ} {grid : DynamicFiniteHeightGrid}
    {admissible : ℝ → ℝ → Prop} {slack : ℝ → ℝ}
    {layers : Finset ι} {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hcostUpper :
      ∀ x T, 0 < T → |upperError x| ≤ cost x T)
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
  constructUnifiedDynamicZeroTransfer
    hamplitude hcostUpper costCover upperCertificate
      htruncation hcompact hmain remainderCertificate factorization hdecomp

end PrimeNumberTheorem
