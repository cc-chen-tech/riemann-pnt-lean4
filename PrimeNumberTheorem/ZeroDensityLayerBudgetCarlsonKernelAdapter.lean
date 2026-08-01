import PrimeNumberTheorem.ZeroDensityLayerBudgetZeroFreeUnified

/-!
# Carlson majorants as kernel-density factorizations

For every real-part strip, a Carlson estimate naturally produces a majorant
for the zero count.  Divide the actual density contribution by that majorant:
the normalized factor is eventually bounded by one.  The remaining factor is
the explicit-formula kernel multiplied by the Carlson majorant.

This module packages exactly that input and converts it to the generic
`CarlsonKernelLayerFactorization` used by both upper and oscillation transfers.
It does not assert a new concrete Carlson exponent.
-/

namespace PrimeNumberTheorem

/--
Finite stripwise Carlson-majorant data along a dynamic height schedule.

`majorant` and `kernelWeight` are already evaluated along the schedule.  The
factorization equation records the analytic normalization of the actual layer
term.
-/
structure CarlsonKernelMajorantLayerAdapter
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (height : ℝ → ℝ)
    (layerTerm : ι → ℝ → ℝ → ℝ) where
  majorant : ι → ℝ → ℝ
  kernelWeight : ι → ℝ → ℝ
  normalizedDensity : ι → ℝ → ℝ
  factorization :
    ∀ i ∈ layers, ∀ x,
      layerTerm i x (height x) =
        (kernelWeight i x * majorant i x) *
          normalizedDensity i x
  weightedKernel_tendsto_zero :
    ∀ i ∈ layers,
      Filter.Tendsto
        (fun x => kernelWeight i x * majorant i x)
        Filter.atTop (nhds 0)
  normalizedDensity_eventually_le_one :
    ∀ i ∈ layers,
      ∀ᶠ x in Filter.atTop,
        |normalizedDensity i x| ≤ 1

/--
Convert normalized Carlson-majorant data to the generic finite kernel-density
factorization.
-/
def CarlsonKernelMajorantLayerAdapter.toKernelDensityFactorization
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι} {height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    (adapter :
      CarlsonKernelMajorantLayerAdapter layers height layerTerm) :
    CarlsonKernelLayerFactorization layers height layerTerm where
  kernelFactor :=
    fun i x => adapter.kernelWeight i x * adapter.majorant i x
  densityRatio := adapter.normalizedDensity
  densityBound := fun _ => 1
  densityBound_nonneg := by
    intro i hi
    norm_num
  factorization := adapter.factorization
  kernel_tendsto_zero := adapter.weightedKernel_tendsto_zero
  densityRatio_eventually_bounded :=
    adapter.normalizedDensity_eventually_le_one

/-- The Carlson-majorant adapter automatically gives finite layer decay. -/
def CarlsonKernelMajorantLayerAdapter.toFiniteDynamicLayerDecay
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι} {height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    (adapter :
      CarlsonKernelMajorantLayerAdapter layers height layerTerm) :
    FiniteDynamicLayerDecay layers height layerTerm :=
  adapter.toKernelDensityFactorization.toFiniteDynamicLayerDecay

/--
Direct dynamic explicit-formula upper transfer from normalized Carlson
majorants.
-/
theorem dynamicExplicitFormulaUpper_tendsto_zero_of_carlsonMajorant
    {ι : Type*} [DecidableEq ι]
    {error : ℝ → ℝ} {layers : Finset ι} {height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ}
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate error layers height
        layerTerm truncation compact)
    (adapter :
      CarlsonKernelMajorantLayerAdapter layers height layerTerm)
    (htruncation :
      Filter.Tendsto truncation Filter.atTop (nhds 0))
    (hcompact :
      Filter.Tendsto compact Filter.atTop (nhds 0)) :
    Filter.Tendsto error Filter.atTop (nhds 0) :=
  dynamicExplicitFormulaUpper_tendsto_zero_of_kernelDensityFactorization
    upperCertificate adapter.toKernelDensityFactorization
      htruncation hcompact

/--
Direct absolute-Omega transfer from normalized Carlson majorants.
-/
theorem hasFarNormWitness_add_of_carlsonMajorant
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι}
    {error main remainder height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hmain : HasFarNormWitness main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder height
        (finiteLayerBudget layers layerTerm))
    (adapter :
      CarlsonKernelMajorantLayerAdapter layers height layerTerm)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarNormWitness error (amplitude / 2) :=
  hasFarNormWitness_add_of_kernelDensityFactorization
    hamplitude hmain remainderCertificate
      adapter.toKernelDensityFactorization hdecomp

/--
Direct Omega-plus/minus transfer from normalized Carlson majorants.
-/
theorem hasFarSignedWitnesses_add_of_carlsonMajorant
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι}
    {error main remainder height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hmain : HasFarSignedWitnesses main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder height
        (finiteLayerBudget layers layerTerm))
    (adapter :
      CarlsonKernelMajorantLayerAdapter layers height layerTerm)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarSignedWitnesses error (amplitude / 2) :=
  hasFarSignedWitnesses_add_of_kernelDensityFactorization
    hamplitude hmain remainderCertificate
      adapter.toKernelDensityFactorization hdecomp

end PrimeNumberTheorem
