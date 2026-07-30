import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicOptimization

/-!
# Constructed unified dynamic zero transfer

This is the outer certificate promised by the dynamic Pintz--Carlson explicit
formula architecture.  A single constructed result carries:

* the pointwise finite-grid optimizer `T(x)`;
* positivity and divergence of `T(x)`;
* exact grid optimality and additive-slack admissible optimality;
* the explicit-formula upper estimate at `T(x)`;
* decay of the normalized upper PNT error;
* an absolute Omega, or signed Omega-plus/minus, lower conclusion.

The concrete analytic inputs remain separate certificates, so zero-free
regions, Carlson density estimates, and explicit-formula kernels can be
replaced without changing the transfer machine.
-/

namespace PrimeNumberTheorem

/-- Constructed absolute-Omega form of the unified dynamic transfer. -/
structure UnifiedDynamicZeroTransferResult
    (upperError lowerError : ℝ → ℝ)
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    (admissible : ℝ → ℝ → Prop) (slack : ℝ → ℝ)
    (amplitude : ℝ) where
  height : ℝ → ℝ
  height_tendsto_atTop :
    Filter.Tendsto height Filter.atTop Filter.atTop
  height_positive :
    ∀ x, 0 < height x
  height_mem :
    ∀ x, height x ∈ (grid.grid x).heights
  height_grid_optimal :
    ∀ x T, T ∈ (grid.grid x).heights →
      cost x (height x) ≤ cost x T
  explicitFormula_upper :
    ∀ x, |upperError x| ≤ cost x (height x)
  height_nearOptimal :
    ∀ x T, admissible x T →
      cost x (height x) ≤ cost x T + slack x
  upper_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  lower_omega :
    HasFarNormWitness lowerError (amplitude / 2)

/--
Build the unified result using the pointwise finite-grid optimizer as the
dynamic height.
-/
noncomputable def constructUnifiedDynamicZeroTransfer
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
    dynamicExplicitFormula_upper_at_dynamicFiniteGridOptimalHeight
      upperError cost grid hcostUpper
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

/-- Constructed signed-Omega form of the unified dynamic transfer. -/
structure UnifiedDynamicSignedZeroTransferResult
    (upperError lowerError : ℝ → ℝ)
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    (admissible : ℝ → ℝ → Prop) (slack : ℝ → ℝ)
    (amplitude : ℝ) where
  height : ℝ → ℝ
  height_tendsto_atTop :
    Filter.Tendsto height Filter.atTop Filter.atTop
  height_positive :
    ∀ x, 0 < height x
  height_mem :
    ∀ x, height x ∈ (grid.grid x).heights
  height_grid_optimal :
    ∀ x T, T ∈ (grid.grid x).heights →
      cost x (height x) ≤ cost x T
  explicitFormula_upper :
    ∀ x, |upperError x| ≤ cost x (height x)
  height_nearOptimal :
    ∀ x T, admissible x T →
      cost x (height x) ≤ cost x T + slack x
  upper_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  lower_omegaPlusMinus :
    HasFarSignedWitnesses lowerError (amplitude / 2)

/-- Build the signed unified result from recurrent witnesses of both signs. -/
noncomputable def constructUnifiedDynamicSignedZeroTransfer
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
    dynamicExplicitFormula_upper_at_dynamicFiniteGridOptimalHeight
      upperError cost grid hcostUpper
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
