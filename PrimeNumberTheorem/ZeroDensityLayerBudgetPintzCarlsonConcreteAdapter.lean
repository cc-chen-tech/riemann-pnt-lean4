import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonUnified
import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonDensityTransfer

/-!
# Concrete Pintz--Carlson density adapter

This module converts the actual multiplicity-counted Carlson density budget into
the abstract kernel-majorant adapter consumed by the unified upper/lower
transfer machine. The equality between the optimizer height and the adaptive
Pintz--Carlson height is deliberately explicit: it is the remaining interface
that a concrete finite-grid cost model must prove.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Aggregate all real-part strips into one explicit-formula layer evaluated at
the supplied truncation height. -/
noncomputable def pintzCarlsonAggregatedDensityLayerTerm
    {ι : Type*} (layers : Finset ι) (count : ι → ℝ → ℝ) :
    Unit → ℝ → ℝ → ℝ :=
  fun _ x T =>
    ∑ i ∈ layers, count i T * Real.exp (-Pintz.pintzZeroEnvelope x)

/-- A concrete Carlson-density adapter together with the Pintz constant that
controls every rate in the supplied finite grid. -/
structure AdaptiveClassicalCarlsonDensityAdapterPackage
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (sigma : ι → ℝ)
    (rates : Finset ℝ) : Type where
  c : ℝ
  c_pos : 0 < c
  adapter : ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      ∀ (height : ℝ → ℝ),
        (∀ x, height x = pintzCarlsonHeight (selectRate x) x) →
        CarlsonKernelMajorantLayerAdapter
          ({()} : Finset Unit) height
          (pintzCarlsonAggregatedDensityLayerTerm layers
            (fun i T => (ZeroDensity.zeroDensityCount (sigma i) T : ℝ)))

/-- The concrete Carlson count decay supplies the abstract adapter required by
the unified transfer theorem, provided the chosen truncation height is exactly
the adaptive Pintz--Carlson height. -/
noncomputable def constructAdaptiveClassicalCarlsonDensityAdapterPackage
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (sigma : ι → ℝ)
    (hσ : ∀ i, 1 / 2 < sigma i)
    (hσ1 : ∀ i, sigma i < 1)
    (rates : Finset ℝ) :
    AdaptiveClassicalCarlsonDensityAdapterPackage layers sigma rates := by
  let hex :=
    exists_pintzConstant_adaptiveClassicalCarlsonDensity_tendsto
      layers sigma hσ hσ1 rates
  let c := Classical.choose hex
  have hc : 0 < c := (Classical.choose_spec hex).1
  have hdecay := (Classical.choose_spec hex).2
  refine { c := c, c_pos := hc, adapter := ?_ }
  intro selectRate hselect hratesPos hratesGap height hheight
  have hbudget :=
    hdecay selectRate hselect hratesPos hratesGap
  refine
    { majorant := fun _ x =>
        pintzCarlsonActualDensityBudget layers
          (fun i T => (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
          selectRate x
      kernelWeight := fun _ _ => 1
      normalizedDensity := fun _ _ => 1
      factorization := ?_
      weightedKernel_tendsto_zero := ?_
      normalizedDensity_eventually_le_one := ?_ }
  · intro i hi x
    have hi' : i = () := Finset.mem_singleton.mp hi
    subst i
    simp only [pintzCarlsonAggregatedDensityLayerTerm,
      pintzCarlsonActualDensityBudget, one_mul, mul_one]
    rw [hheight]
  · intro i hi
    simpa only [one_mul] using hbudget
  · intro i hi
    exact Filter.Eventually.of_forall (fun _ => by simp)

end PrimeNumberTheorem
