import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonConcreteRateGridUnified

/-!
# Explicit-formula tail bridge for Pintz--Carlson budgets

This module bounds a layered finite zero tail by the project's actual
multiplicity-counted Carlson density budget and packages such a tail estimate
as the upper certificate consumed by the unified transfer constructors.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- A layered zero tail whose terms share the Pintz envelope kernel is bounded
by the actual multiplicity-counted Carlson density budget. -/
theorem norm_tail_sum_le_pintzCarlsonAggregatedDensityLayerTerm
    {ρ E : Type*} [DecidableEq ρ] [NormedAddCommGroup E]
    (C : LayerCertificate ρ E)
    (sigma : Fin C.layerCount → ℝ)
    (T x : ℝ) (term : ρ → E)
    (hcount : ∀ i,
      ((C.layer i).card : ℝ) ≤
        (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
    (hkernel : ∀ i, ∀ z ∈ C.layer i,
      ‖term z‖ ≤ Real.exp (-Pintz.pintzZeroEnvelope x)) :
    ‖∑ z ∈ C.tail, term z‖ ≤
      pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin C.layerCount)) sigma () x T := by
  have hbound :=
    norm_tail_sum_le_layeredTailBudget C term
      (fun i => (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
      (fun _ => Real.exp (-Pintz.pintzZeroEnvelope x))
      hcount hkernel (fun _ => Real.exp_nonneg _)
  change ‖∑ z ∈ C.tail, term z‖ ≤
    ∑ i, (ZeroDensity.zeroDensityCount (sigma i) T : ℝ) *
      Real.exp (-Pintz.pintzZeroEnvelope x)
  simpa only [layeredTailBudget] using hbound

theorem pintzCarlsonClassicalAggregatedDensityLayerTerm_nonneg
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (sigma : ι → ℝ) (x T : ℝ) :
    0 ≤ pintzCarlsonClassicalAggregatedDensityLayerTerm
      layers sigma () x T := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (Nat.cast_nonneg (ZeroDensity.zeroDensityCount (sigma i) T))
    (Real.exp_nonneg _)

/-- An eventual explicit-formula tail estimate against the concrete Carlson
budget yields the exact upper certificate required by the unified machine. -/
theorem dynamicExplicitFormulaUpperCertificate_of_pintzCarlsonTail
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (sigma : ι → ℝ)
    (error tail height truncation compact : ℝ → ℝ)
    (herror : ∀ᶠ x in atTop,
      |error x| ≤ tail x + truncation x + compact x)
    (htail : ∀ᶠ x in atTop,
      tail x ≤ pintzCarlsonClassicalAggregatedDensityLayerTerm
        layers sigma () x (height x))
    (htruncation : ∀ᶠ x in atTop, 0 ≤ truncation x)
    (hcompact : ∀ᶠ x in atTop, 0 ≤ compact x) :
    DynamicExplicitFormulaUpperCertificate error ({()} : Finset Unit)
      height
      (pintzCarlsonClassicalAggregatedDensityLayerTerm layers sigma)
      truncation compact := by
  constructor
  filter_upwards [herror, htail, htruncation, hcompact] with
    x herror_x htail_x htruncation_x hcompact_x
  simp only [dynamicExplicitFormulaUpperBudgetAlong,
    finiteLayerBudgetAlong, finiteLayerBudget, Finset.sum_singleton]
  have hbudget_nonneg :
      0 ≤ pintzCarlsonClassicalAggregatedDensityLayerTerm
          layers sigma () x (height x) + truncation x + compact x :=
    add_nonneg
      (add_nonneg
        (pintzCarlsonClassicalAggregatedDensityLayerTerm_nonneg
          layers sigma x (height x))
        htruncation_x)
      hcompact_x
  conv_rhs => rw [abs_of_nonneg hbudget_nonneg]
  exact herror_x.trans
    (add_le_add (add_le_add htail_x le_rfl) le_rfl)

end PrimeNumberTheorem
