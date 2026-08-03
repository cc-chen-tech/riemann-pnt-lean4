import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteDecay

/-!
# Kernel-density factorization for dynamic Carlson layers

For one real-part strip, write the layer contribution as

`(explicit-formula kernel × Carlson majorant) × (density / majorant)`.

The first factor is designed to tend to zero through the choice of dynamic
height.  Carlson's estimate makes the normalized second factor eventually
bounded.  This file proves that their product tends to zero and packages the
argument for every member of a finite layer decomposition.
-/

namespace PrimeNumberTheorem

/--
A real function tending to zero remains tending to zero after multiplication
by an eventually uniformly bounded real function.
-/
theorem tendsto_mul_zero_of_eventually_abs_le
    {kernel density : ℝ → ℝ} {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hkernel :
      Filter.Tendsto kernel Filter.atTop (nhds 0))
    (hdensity :
      ∀ᶠ x in Filter.atTop, |density x| ≤ bound) :
    Filter.Tendsto (fun x => kernel x * density x)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hdenom : 0 < bound + 1 := by linarith
  have hdelta : 0 < ε / (bound + 1) :=
    div_pos hε hdenom
  have hkernelEventually :
      ∀ᶠ x in Filter.atTop,
        dist (kernel x) 0 < ε / (bound + 1) :=
    (Metric.tendsto_nhds.1 hkernel) _ hdelta
  filter_upwards [hkernelEventually, hdensity] with x hkx hdx
  have hkabs : |kernel x| < ε / (bound + 1) := by
    simpa [Real.dist_eq] using hkx
  have hratio : bound / (bound + 1) < 1 :=
    (div_lt_one hdenom).2 (by linarith)
  have hcap : ε / (bound + 1) * bound < ε := by
    calc
      ε / (bound + 1) * bound =
          ε * (bound / (bound + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := by ring
  have hproduct : |kernel x| * |density x| < ε := by
    calc
      |kernel x| * |density x| ≤
          (ε / (bound + 1)) * bound :=
        mul_le_mul (le_of_lt hkabs) hdx
          (abs_nonneg _) (le_of_lt hdelta)
      _ < ε := hcap
  simpa [Real.dist_eq, abs_mul] using hproduct

/--
Stripwise factorization data.  `kernelFactor` includes the explicit-formula
kernel and the chosen Carlson majorant; `densityRatio` is the actual density
input divided by that majorant.
-/
structure CarlsonKernelLayerFactorization
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (height : ℝ → ℝ)
    (layerTerm : ι → ℝ → ℝ → ℝ) where
  kernelFactor : ι → ℝ → ℝ
  densityRatio : ι → ℝ → ℝ
  densityBound : ι → ℝ
  densityBound_nonneg :
    ∀ i ∈ layers, 0 ≤ densityBound i
  factorization :
    ∀ i ∈ layers, ∀ x,
      layerTerm i x (height x) =
        kernelFactor i x * densityRatio i x
  kernel_tendsto_zero :
    ∀ i ∈ layers,
      Filter.Tendsto (kernelFactor i) Filter.atTop (nhds 0)
  densityRatio_eventually_bounded :
    ∀ i ∈ layers,
      ∀ᶠ x in Filter.atTop,
        |densityRatio i x| ≤ densityBound i

/--
Kernel decay plus the normalized Carlson bound automatically gives the
stripwise dynamic decay certificate used by finite-layer aggregation.
-/
def CarlsonKernelLayerFactorization.toFiniteDynamicLayerDecay
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι} {height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    (certificate :
      CarlsonKernelLayerFactorization layers height layerTerm) :
    FiniteDynamicLayerDecay layers height layerTerm where
  layer_tendsto_zero := by
    intro i hi
    have hproduct :=
      tendsto_mul_zero_of_eventually_abs_le
        (certificate.densityBound_nonneg i hi)
        (certificate.kernel_tendsto_zero i hi)
        (certificate.densityRatio_eventually_bounded i hi)
    simpa only [certificate.factorization i hi] using hproduct

/--
Full absolute-Omega transfer from finite kernel-density factorizations.
-/
theorem hasFarNormWitness_add_of_kernelDensityFactorization
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι}
    {error main remainder height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hmain : HasFarNormWitness main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder height
        (finiteLayerBudget layers layerTerm))
    (factorization :
      CarlsonKernelLayerFactorization layers height layerTerm)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarNormWitness error (amplitude / 2) :=
  hasFarNormWitness_add_of_finiteLayerDecay
    hamplitude hmain remainderCertificate
      factorization.toFiniteDynamicLayerDecay hdecomp

/--
Full Omega-plus/minus transfer from the same finite kernel-density data.
-/
theorem hasFarSignedWitnesses_add_of_kernelDensityFactorization
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι}
    {error main remainder height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hmain : HasFarSignedWitnesses main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder height
        (finiteLayerBudget layers layerTerm))
    (factorization :
      CarlsonKernelLayerFactorization layers height layerTerm)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarSignedWitnesses error (amplitude / 2) :=
  hasFarSignedWitnesses_add_of_finiteLayerDecay
    hamplitude hmain remainderCertificate
      factorization.toFiniteDynamicLayerDecay hdecomp

end PrimeNumberTheorem
