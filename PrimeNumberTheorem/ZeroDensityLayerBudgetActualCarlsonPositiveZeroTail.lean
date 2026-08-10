import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonWeightedPowerTail

/-!
# Actual Carlson positive-zero tails

This file adds the finite initial height range to the dyadic Carlson shells.
The resulting index contains the actual positive nontrivial zeta zeros used by
the weighted power-tail transfer:

* the base range has `0 < Im rho <= 1`;
* the dyadic part has `2^n < Im rho <= 2^(n+1)`.

The summability argument does not impose a uniform real-part gap.  It only
requires each residual zero to lie strictly to the left of the target real
part.  Zeros with the same real part as the target therefore remain part of
the main-cluster problem rather than being hidden in the tail.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

/-- Actual positive zeta zeros above `sigma`, split into a finite base range
and the dyadic Carlson shells. -/
def ActualCarlsonPositiveZeroIndex (sigma : ℝ) :=
  {rho : ℂ // rho ∈ ZeroDensity.zeroDensityZerosFinset sigma 1} ⊕
    ActualCarlsonDyadicZeroIndex sigma

/-- The zeta zero represented by an actual positive-zero index. -/
def actualCarlsonPositiveZero {sigma : ℝ}
    (index : ActualCarlsonPositiveZeroIndex sigma) : ℂ :=
  match index with
  | Sum.inl rho => rho
  | Sum.inr index => index.2

/-- The multiplicity-weighted reciprocal norm of an indexed zeta zero. -/
def actualCarlsonPositiveZeroWeight {sigma : ℝ}
    (index : ActualCarlsonPositiveZeroIndex sigma) : ℝ :=
  match index with
  | Sum.inl rho => (analyticOrderNatAt riemannZeta rho : ℝ) / ‖(rho : ℂ)‖
  | Sum.inr index => actualCarlsonDyadicZeroWeight index

/-- The real part of an indexed zeta zero. -/
def actualCarlsonPositiveZeroRealPart {sigma : ℝ}
    (index : ActualCarlsonPositiveZeroIndex sigma) : ℝ :=
  (actualCarlsonPositiveZero index).re

theorem actualCarlsonPositiveZero_spec {sigma : ℝ}
    (index : ActualCarlsonPositiveZeroIndex sigma) :
    RiemannHypothesis.IsNontrivialZero (actualCarlsonPositiveZero index) ∧
      0 < (actualCarlsonPositiveZero index).im ∧
      sigma < actualCarlsonPositiveZeroRealPart index := by
  cases index with
  | inl rho =>
      rcases ZeroDensity.mem_zeroDensityZerosFinset.mp rho.property with
        ⟨hz, him, _, hre⟩
      exact ⟨hz, him, hre⟩
  | inr index =>
      rcases index with ⟨n, rho⟩
      have hupper :
          (rho : ℂ) ∈
            ZeroDensity.zeroDensityZerosFinset sigma ((2 : ℝ) ^ (n + 1)) :=
        (Finset.mem_sdiff.mp rho.property).1
      rcases ZeroDensity.mem_zeroDensityZerosFinset.mp hupper with
        ⟨hz, him, _, hre⟩
      exact ⟨hz, him, hre⟩

theorem actualCarlsonPositiveZeroWeight_nonneg {sigma : ℝ}
    (index : ActualCarlsonPositiveZeroIndex sigma) :
    0 ≤ actualCarlsonPositiveZeroWeight index := by
  cases index with
  | inl rho =>
      exact div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  | inr index =>
      exact actualCarlsonDyadicZeroWeight_nonneg index

theorem summable_actualCarlsonPositiveZeroWeight {sigma : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable (@actualCarlsonPositiveZeroWeight sigma) := by
  apply Summable.sum actualCarlsonPositiveZeroWeight
  · exact Summable.of_finite
  · simpa [Function.comp_def, actualCarlsonPositiveZeroWeight] using
      summable_actualCarlsonDyadicZeroWeight hhalf hone

/-- Pointwise strict separation from `beta` is enough for the complete
positive-zero weighted power tail to vanish. -/
theorem actualCarlsonPositiveZeroWeightedPowerTail_tendsto_zero
    {sigma beta : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hre : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZeroRealPart index < beta) :
    Tendsto
      (fun m : ℕ =>
        ∑' index : ActualCarlsonPositiveZeroIndex sigma,
          actualCarlsonPositiveZeroWeight index *
            pntPowerLayerToTargetRatio beta
              (actualCarlsonPositiveZeroRealPart index) m)
      atTop (nhds 0) :=
  weightedPowerLayers_tendsto_zero_of_summable
    (summable_actualCarlsonPositiveZeroWeight hhalf hone)
    actualCarlsonPositiveZeroWeight_nonneg hre

end

end PrimeNumberTheorem
