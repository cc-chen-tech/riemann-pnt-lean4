import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonUnified

/-!
# Eventually zero-free unified dynamic transfer

Pintz envelope admissibility is naturally eventual in the scale variable.
This file provides the matching unified result: the selected dynamic height is
eventually zero-free and the conditional explicit formula applies eventually,
while height divergence, finite-grid optimality, normalized upper decay, and
oscillation conclusions retain their original quantifiers.
-/

namespace PrimeNumberTheorem

/--
Eventually, every candidate height in the dynamic grid lies in the supplied
zero-free region.
-/
structure EventuallyDynamicZeroFreeHeightCertificate
    (zeroFree : ℝ → ℝ → Prop)
    (grid : DynamicFiniteHeightGrid) : Prop where
  eventually_candidate_zeroFree :
    ∀ᶠ x in Filter.atTop,
      ∀ T, T ∈ (grid.grid x).heights → zeroFree x T

/-- A globally zero-free candidate grid is eventually zero-free. -/
def DynamicZeroFreeHeightCertificate.toEventually
    {zeroFree : ℝ → ℝ → Prop} {grid : DynamicFiniteHeightGrid}
    (certificate : DynamicZeroFreeHeightCertificate zeroFree grid) :
    EventuallyDynamicZeroFreeHeightCertificate zeroFree grid where
  eventually_candidate_zeroFree :=
    Filter.Eventually.of_forall certificate.candidate_zeroFree

/-- The selected dynamic optimizer is eventually zero-free. -/
theorem eventually_dynamicFiniteGridOptimalHeight_zeroFree
    {zeroFree : ℝ → ℝ → Prop}
    (cost : ℝ → ℝ → ℝ) (grid : DynamicFiniteHeightGrid)
    (certificate :
      EventuallyDynamicZeroFreeHeightCertificate zeroFree grid) :
    ∀ᶠ x in Filter.atTop,
      zeroFree x (dynamicFiniteGridOptimalHeight cost grid x) := by
  filter_upwards [certificate.eventually_candidate_zeroFree] with x hx
  exact hx _ (dynamicFiniteGridOptimalHeight_mem cost grid x)

/--
The zero-free conditional explicit formula applies eventually at the selected
dynamic optimizer.
-/
theorem eventually_zeroFreeExplicitFormula_upper_at_dynamicOptimalHeight
    {upperError : ℝ → ℝ} {cost : ℝ → ℝ → ℝ}
    {zeroFree : ℝ → ℝ → Prop}
    {grid : DynamicFiniteHeightGrid}
    (zeroFreeHeights :
      EventuallyDynamicZeroFreeHeightCertificate zeroFree grid)
    (explicitFormula :
      ZeroFreeExplicitFormulaUpperCertificate upperError cost zeroFree) :
    ∀ᶠ x in Filter.atTop,
      |upperError x| ≤
        cost x (dynamicFiniteGridOptimalHeight cost grid x) := by
  filter_upwards [
    eventually_dynamicFiniteGridOptimalHeight_zeroFree
      cost grid zeroFreeHeights] with x hx
  exact explicitFormula.upper_of_zeroFree x _
    (dynamicFiniteGridOptimalHeight_pos cost grid x) hx

/-- Eventual-zero-free form of the absolute unified result. -/
structure EventuallyUnifiedDynamicZeroTransferResult
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
  explicitFormula_upper_eventually :
    ∀ᶠ x in Filter.atTop,
      |upperError x| ≤ cost x (height x)
  height_nearOptimal :
    ∀ x T, admissible x T →
      cost x (height x) ≤ cost x T + slack x
  upper_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  lower_omega :
    HasFarNormWitness lowerError (amplitude / 2)

/-- Eventual-zero-free form of the signed unified result. -/
structure EventuallyUnifiedDynamicSignedZeroTransferResult
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
  explicitFormula_upper_eventually :
    ∀ᶠ x in Filter.atTop,
      |upperError x| ≤ cost x (height x)
  height_nearOptimal :
    ∀ x T, admissible x T →
      cost x (height x) ≤ cost x T + slack x
  upper_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  lower_omegaPlusMinus :
    HasFarSignedWitnesses lowerError (amplitude / 2)

/--
One-step eventual-zero-free Carlson transfer with an absolute-Omega
conclusion.
-/
noncomputable def constructEventuallyZeroFreeCarlsonUnifiedDynamicZeroTransfer
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ} {grid : DynamicFiniteHeightGrid}
    {zeroFree : ℝ → ℝ → Prop}
    {admissible : ℝ → ℝ → Prop} {slack : ℝ → ℝ}
    {layers : Finset ι} {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (zeroFreeHeights :
      EventuallyDynamicZeroFreeHeightCertificate zeroFree grid)
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
    EventuallyUnifiedDynamicZeroTransferResult
      upperError lowerError cost grid admissible slack amplitude where
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
  explicitFormula_upper_eventually :=
    eventually_zeroFreeExplicitFormula_upper_at_dynamicOptimalHeight
      zeroFreeHeights explicitFormula
  height_nearOptimal := by
    intro x T hT
    exact dynamicFiniteGridOptimalHeight_le_add
      cost grid admissible slack costCover hT
  upper_tendsto_zero :=
    dynamicExplicitFormulaUpper_tendsto_zero_of_carlsonMajorant
      upperCertificate carlsonAdapter htruncation hcompact
  lower_omega :=
    hasFarNormWitness_add_of_carlsonMajorant
      hamplitude hmain remainderCertificate carlsonAdapter hdecomp

/--
One-step eventual-zero-free Carlson transfer with an Omega-plus/minus
conclusion.
-/
noncomputable def constructEventuallyZeroFreeCarlsonUnifiedDynamicSignedZeroTransfer
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder : ℝ → ℝ}
    {cost : ℝ → ℝ → ℝ} {grid : DynamicFiniteHeightGrid}
    {zeroFree : ℝ → ℝ → Prop}
    {admissible : ℝ → ℝ → Prop} {slack : ℝ → ℝ}
    {layers : Finset ι} {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (zeroFreeHeights :
      EventuallyDynamicZeroFreeHeightCertificate zeroFree grid)
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
    EventuallyUnifiedDynamicSignedZeroTransferResult
      upperError lowerError cost grid admissible slack amplitude where
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
  explicitFormula_upper_eventually :=
    eventually_zeroFreeExplicitFormula_upper_at_dynamicOptimalHeight
      zeroFreeHeights explicitFormula
  height_nearOptimal := by
    intro x T hT
    exact dynamicFiniteGridOptimalHeight_le_add
      cost grid admissible slack costCover hT
  upper_tendsto_zero :=
    dynamicExplicitFormulaUpper_tendsto_zero_of_carlsonMajorant
      upperCertificate carlsonAdapter htruncation hcompact
  lower_omegaPlusMinus :=
    hasFarSignedWitnesses_add_of_carlsonMajorant
      hamplitude hmain remainderCertificate carlsonAdapter hdecomp

end PrimeNumberTheorem
