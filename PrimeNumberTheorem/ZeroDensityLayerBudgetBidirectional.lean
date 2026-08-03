import PrimeNumberTheorem.ZeroDensityLayerBudgetKernelDensity
import PrimeNumberTheorem.ZeroDensityLayerBudgetOptimization

/-!
# Bidirectional dynamic explicit-formula transfer

The same finite Carlson layer data now drives both directions:

* upper transfer: the layer sum, truncation term, and compact term dominate a
  normalized PNT error and all tend to zero;
* lower transfer: a recurrent finite rightmost cluster survives the vanishing
  layer remainder and yields an Omega or Omega-plus/minus conclusion.

The upper and lower errors may use different normalizations, as they generally
do in sharp PNT upper bounds and oscillation statements.
-/

namespace PrimeNumberTheorem

/-- The full dynamic explicit-formula upper budget along `T = T(x)`. -/
def dynamicExplicitFormulaUpperBudgetAlong
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (height : ℝ → ℝ)
    (layerTerm : ι → ℝ → ℝ → ℝ)
    (truncation compact : ℝ → ℝ) (x : ℝ) : ℝ :=
  finiteLayerBudgetAlong layers height layerTerm x +
    truncation x + compact x

/--
An upper explicit-formula certificate: eventually, the normalized error is
dominated by the absolute value of the complete dynamic budget.
-/
structure DynamicExplicitFormulaUpperCertificate
    {ι : Type*} [DecidableEq ι]
    (error : ℝ → ℝ) (layers : Finset ι) (height : ℝ → ℝ)
    (layerTerm : ι → ℝ → ℝ → ℝ)
    (truncation compact : ℝ → ℝ) : Prop where
  eventually_bound :
    ∀ᶠ x in Filter.atTop,
      |error x| ≤
        |dynamicExplicitFormulaUpperBudgetAlong
          layers height layerTerm truncation compact x|

/--
An error eventually dominated in absolute value by a function tending to zero
also tends to zero.
-/
theorem tendsto_zero_of_eventually_abs_le_abs
    {error budget : ℝ → ℝ}
    (hbudget : Filter.Tendsto budget Filter.atTop (nhds 0))
    (hbound : ∀ᶠ x in Filter.atTop, |error x| ≤ |budget x|) :
    Filter.Tendsto error Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hbudgetEventually :
      ∀ᶠ x in Filter.atTop, dist (budget x) 0 < ε :=
    (Metric.tendsto_nhds.1 hbudget) ε hε
  filter_upwards [hbudgetEventually, hbound] with x hbudgetx hboundx
  have hbudgetAbs : |budget x| < ε := by
    simpa [Real.dist_eq] using hbudgetx
  have herrorAbs : |error x| < ε :=
    hboundx.trans_lt hbudgetAbs
  simpa [Real.dist_eq] using herrorAbs

/--
Finite layer decay, truncation decay, and compact-term decay imply decay of
the complete dynamic explicit-formula upper budget.
-/
theorem dynamicExplicitFormulaUpperBudgetAlong_tendsto_zero
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι} {height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ}
    (layerDecay : FiniteDynamicLayerDecay layers height layerTerm)
    (htruncation :
      Filter.Tendsto truncation Filter.atTop (nhds 0))
    (hcompact :
      Filter.Tendsto compact Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (dynamicExplicitFormulaUpperBudgetAlong
        layers height layerTerm truncation compact)
      Filter.atTop (nhds 0) := by
  simpa [dynamicExplicitFormulaUpperBudgetAlong] using
    layerDecay.total_tendsto_zero.add htruncation |>.add hcompact

/--
Upper PNT transfer from the same kernel-density factorization used on the
oscillation side.
-/
theorem dynamicExplicitFormulaUpper_tendsto_zero_of_kernelDensityFactorization
    {ι : Type*} [DecidableEq ι]
    {error : ℝ → ℝ} {layers : Finset ι} {height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ}
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate error layers height
        layerTerm truncation compact)
    (factorization :
      CarlsonKernelLayerFactorization layers height layerTerm)
    (htruncation :
      Filter.Tendsto truncation Filter.atTop (nhds 0))
    (hcompact :
      Filter.Tendsto compact Filter.atTop (nhds 0)) :
    Filter.Tendsto error Filter.atTop (nhds 0) :=
  tendsto_zero_of_eventually_abs_le_abs
    (dynamicExplicitFormulaUpperBudgetAlong_tendsto_zero
      factorization.toFiniteDynamicLayerDecay htruncation hcompact)
    upperCertificate.eventually_bound

/-- A single certificate containing upper decay and an absolute Omega bound. -/
structure BidirectionalDynamicTransferConclusion
    (upperError lowerError : ℝ → ℝ) (amplitude : ℝ) : Prop where
  upper_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  lower_omega :
    HasFarNormWitness lowerError (amplitude / 2)

/--
Unified upper/lower transfer from one finite kernel-density layer
factorization.
-/
theorem bidirectional_dynamic_transfer_of_kernelDensityFactorization
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder height : ℝ → ℝ}
    {layers : Finset ι} {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError layers height
        layerTerm truncation compact)
    (htruncation :
      Filter.Tendsto truncation Filter.atTop (nhds 0))
    (hcompact :
      Filter.Tendsto compact Filter.atTop (nhds 0))
    (hmain : HasFarNormWitness main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder height
        (finiteLayerBudget layers layerTerm))
    (factorization :
      CarlsonKernelLayerFactorization layers height layerTerm)
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    BidirectionalDynamicTransferConclusion upperError lowerError amplitude where
  upper_tendsto_zero :=
    dynamicExplicitFormulaUpper_tendsto_zero_of_kernelDensityFactorization
      upperCertificate factorization htruncation hcompact
  lower_omega :=
    hasFarNormWitness_add_of_kernelDensityFactorization
      hamplitude hmain remainderCertificate factorization hdecomp

/--
Signed version of the unified transfer: the upper conclusion is unchanged,
while both signs recur on the lower side.
-/
theorem bidirectional_dynamic_signed_transfer_of_kernelDensityFactorization
    {ι : Type*} [DecidableEq ι]
    {upperError lowerError main remainder height : ℝ → ℝ}
    {layers : Finset ι} {layerTerm : ι → ℝ → ℝ → ℝ}
    {truncation compact : ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (upperCertificate :
      DynamicExplicitFormulaUpperCertificate upperError layers height
        layerTerm truncation compact)
    (htruncation :
      Filter.Tendsto truncation Filter.atTop (nhds 0))
    (hcompact :
      Filter.Tendsto compact Filter.atTop (nhds 0))
    (hmain : HasFarSignedWitnesses main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder height
        (finiteLayerBudget layers layerTerm))
    (factorization :
      CarlsonKernelLayerFactorization layers height layerTerm)
    (hdecomp : ∀ x, lowerError x = main x + remainder x) :
    Filter.Tendsto upperError Filter.atTop (nhds 0) ∧
      HasFarSignedWitnesses lowerError (amplitude / 2) :=
  ⟨dynamicExplicitFormulaUpper_tendsto_zero_of_kernelDensityFactorization
      upperCertificate factorization htruncation hcompact,
    hasFarSignedWitnesses_add_of_kernelDensityFactorization
      hamplitude hmain remainderCertificate factorization hdecomp⟩

end PrimeNumberTheorem
