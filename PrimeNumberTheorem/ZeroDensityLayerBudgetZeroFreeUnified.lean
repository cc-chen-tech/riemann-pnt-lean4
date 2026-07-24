import PrimeNumberTheorem.ZeroDensityLayerBudgetUnifiedMachine

/-!
# Zero-free-region input for the unified dynamic transfer

The first unified constructor accepted an upper explicit-formula estimate at
every positive height.  That is stronger than the intended analytic input.
This module makes the zero-free region explicit:

* every candidate height in the dynamic finite grid is certified zero-free;
* the explicit-formula kernel gives an upper estimate only under that
  zero-free predicate;
* membership of the selected pointwise optimizer supplies the predicate
  automatically.

The Carlson layer factorization, dynamic optimization, and oscillation transfer
are unchanged.
-/

namespace PrimeNumberTheorem

/--
Every candidate height in a dynamic finite grid lies in the supplied zero-free
region at its scale.
-/
structure DynamicZeroFreeHeightCertificate
    (zeroFree : ℝ → ℝ → Prop)
    (grid : DynamicFiniteHeightGrid) : Prop where
  candidate_zeroFree :
    ∀ x T, T ∈ (grid.grid x).heights → zeroFree x T

/--
The explicit-formula kernel bounds the upper error whenever the selected scale
and height lie in the zero-free region.
-/
structure ZeroFreeExplicitFormulaUpperCertificate
    (upperError : ℝ → ℝ) (cost : ℝ → ℝ → ℝ)
    (zeroFree : ℝ → ℝ → Prop) : Prop where
  upper_of_zeroFree :
    ∀ x T, 0 < T → zeroFree x T →
      |upperError x| ≤ cost x T

/--
The pointwise finite-grid optimizer inherits the zero-free predicate from grid
membership.
-/
theorem dynamicFiniteGridOptimalHeight_zeroFree
    {zeroFree : ℝ → ℝ → Prop}
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    (certificate : DynamicZeroFreeHeightCertificate zeroFree grid)
    (x : ℝ) :
    zeroFree x (dynamicFiniteGridOptimalHeight cost grid x) :=
  certificate.candidate_zeroFree x _
    (dynamicFiniteGridOptimalHeight_mem cost grid x)

/--
The zero-free explicit formula applies automatically at the selected dynamic
height.
-/
theorem zeroFreeExplicitFormula_upper_at_dynamicOptimalHeight
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
  explicitFormula.upper_of_zeroFree x _
    (dynamicFiniteGridOptimalHeight_pos cost grid x)
    (dynamicFiniteGridOptimalHeight_zeroFree
      cost grid zeroFreeHeights x)

/--
Unified dynamic zero transfer with an explicit zero-free-region input.
-/
noncomputable def constructZeroFreeUnifiedDynamicZeroTransfer
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
      admissible slack amplitude where
  height := dynamicFiniteGridOptimalHeight cost grid
  height_tendsto_atTop :=
    dynamicFiniteGridOptimalHeight_tendsto_atTop cost grid
  height_positive :=
    dynamicFiniteGridOptimalHeight_pos cost grid
  height_mem :=
    dynamicFiniteGridOptimalHeight_mem cost grid
  height_grid_optimal := by
    intro x T hT
    exact dynamicFiniteGridOptimalHeight_le_of_mem cost grid hT
  explicitFormula_upper :=
    zeroFreeExplicitFormula_upper_at_dynamicOptimalHeight
      zeroFreeHeights explicitFormula
  height_nearOptimal := by
    intro x T hT
    exact dynamicFiniteGridOptimalHeight_le_add
      cost grid admissible slack costCover hT
  upper_tendsto_zero :=
    dynamicExplicitFormulaUpper_tendsto_zero_of_kernelDensityFactorization
      upperCertificate factorization htruncation hcompact
  lower_omega :=
    hasFarNormWitness_add_of_kernelDensityFactorization
      hamplitude hmain remainderCertificate factorization hdecomp

/--
Signed version of the zero-free unified transfer.
-/
noncomputable def constructZeroFreeUnifiedDynamicSignedZeroTransfer
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
    (factorization :
      CarlsonKernelLayerFactorization layers
        (dynamicFiniteGridOptimalHeight cost grid) layerTerm)
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    UnifiedDynamicSignedZeroTransferResult upperError lowerError cost grid
      admissible slack amplitude where
  height := dynamicFiniteGridOptimalHeight cost grid
  height_tendsto_atTop :=
    dynamicFiniteGridOptimalHeight_tendsto_atTop cost grid
  height_positive :=
    dynamicFiniteGridOptimalHeight_pos cost grid
  height_mem :=
    dynamicFiniteGridOptimalHeight_mem cost grid
  height_grid_optimal := by
    intro x T hT
    exact dynamicFiniteGridOptimalHeight_le_of_mem cost grid hT
  explicitFormula_upper :=
    zeroFreeExplicitFormula_upper_at_dynamicOptimalHeight
      zeroFreeHeights explicitFormula
  height_nearOptimal := by
    intro x T hT
    exact dynamicFiniteGridOptimalHeight_le_add
      cost grid admissible slack costCover hT
  upper_tendsto_zero :=
    dynamicExplicitFormulaUpper_tendsto_zero_of_kernelDensityFactorization
      upperCertificate factorization htruncation hcompact
  lower_omegaPlusMinus :=
    hasFarSignedWitnesses_add_of_kernelDensityFactorization
      hamplitude hmain remainderCertificate factorization hdecomp

end PrimeNumberTheorem
