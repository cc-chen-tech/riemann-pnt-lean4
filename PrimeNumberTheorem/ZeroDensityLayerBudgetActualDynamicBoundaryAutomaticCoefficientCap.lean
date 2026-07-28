import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPositiveCoefficientMassUpper
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonConjugateCapturedMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryUpperTransfer

/-!
# Automatic coefficient cap for the dynamic boundary package

The moving equal-real-part package is split into positive, negative, and
real-ordinate parts.  Its positive part is bounded by the complete summable
Carlson positive-zero weight.  Conjugation gives equality of the positive and
negative masses, while the real part is contained in the fixed finite
real-ordinate zero set.

This constructs the uniform package coefficient cap required by the dynamic
PNT upper transfer.
-/

namespace PrimeNumberTheorem

open scoped BigOperators ComplexConjugate
open Complex

noncomputable section

/-- Real-ordinate part of a finite visible zero cluster. -/
def realFiniteVisibleClusterPart (E : Finset ℂ) : Finset ℂ :=
  E.filter fun rho => rho.im = 0

/-- Exact positive/negative/real decomposition of finite coefficient mass. -/
theorem finiteVisibleClusterCoefficientMass_eq_positive_add_negative_add_real
    (E : Finset ℂ) :
    finiteVisibleClusterCoefficientMass E =
      finiteVisibleClusterCoefficientMass
          (positiveFiniteVisibleClusterPart E) +
        finiteVisibleClusterCoefficientMass
          (negativeFiniteVisibleClusterPart E) +
        finiteVisibleClusterCoefficientMass
          (realFiniteVisibleClusterPart E) := by
  classical
  let weight : ℂ → ℝ :=
    fun rho => (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖
  let nonpositive := E.filter fun rho => ¬ 0 < rho.im
  have hsplitPositive :=
    Finset.sum_filter_add_sum_filter_not
      E (fun rho : ℂ => 0 < rho.im) weight
  have hsplitNegative :=
    Finset.sum_filter_add_sum_filter_not
      nonpositive (fun rho : ℂ => rho.im < 0) weight
  have hnegative :
      nonpositive.filter (fun rho => rho.im < 0) =
        negativeFiniteVisibleClusterPart E := by
    ext rho
    simp only [nonpositive, negativeFiniteVisibleClusterPart,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨hrho, _⟩, hnegative⟩
      exact ⟨hrho, hnegative⟩
    · rintro ⟨hrho, hnegative⟩
      exact ⟨⟨hrho, by linarith⟩, hnegative⟩
  have hreal :
      nonpositive.filter (fun rho => ¬ rho.im < 0) =
        realFiniteVisibleClusterPart E := by
    ext rho
    simp only [nonpositive, realFiniteVisibleClusterPart,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨hrho, hnonpositive⟩, hnnegative⟩
      exact
        ⟨hrho,
          le_antisymm (le_of_not_gt hnonpositive)
            (not_lt.mp hnnegative)⟩
    · rintro ⟨hrho, him⟩
      exact ⟨⟨hrho, by simp [him]⟩, by simp [him]⟩
  unfold finiteVisibleClusterCoefficientMass
  change
    (∑ rho ∈ E, weight rho) =
      (∑ rho ∈ positiveFiniteVisibleClusterPart E, weight rho) +
        (∑ rho ∈ negativeFiniteVisibleClusterPart E, weight rho) +
          ∑ rho ∈ realFiniteVisibleClusterPart E, weight rho
  calc
    (∑ rho ∈ E, weight rho) =
        (∑ rho ∈ positiveFiniteVisibleClusterPart E, weight rho) +
          ∑ rho ∈ nonpositive, weight rho := hsplitPositive.symm
    _ =
        (∑ rho ∈ positiveFiniteVisibleClusterPart E, weight rho) +
          ((∑ rho ∈ negativeFiniteVisibleClusterPart E, weight rho) +
            ∑ rho ∈ realFiniteVisibleClusterPart E, weight rho) := by
      rw [← hsplitNegative, hnegative, hreal]
    _ =
        (∑ rho ∈ positiveFiniteVisibleClusterPart E, weight rho) +
          (∑ rho ∈ negativeFiniteVisibleClusterPart E, weight rho) +
            ∑ rho ∈ realFiniteVisibleClusterPart E, weight rho := by
      ring

/-- Coefficient mass is monotone under finite-set inclusion. -/
theorem finiteVisibleClusterCoefficientMass_mono
    {E F : Finset ℂ} (hsubset : E ⊆ F) :
    finiteVisibleClusterCoefficientMass E ≤
      finiteVisibleClusterCoefficientMass F := by
  unfold finiteVisibleClusterCoefficientMass
  apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
  intro rho _ _
  positivity

/-- The dynamic equal-real-part package is stable under complex conjugation. -/
theorem dynamicEqualRealPartZeroPackage_conjugationStable
    (H : ℝ → ℝ) (beta x : ℝ) :
    ∀ rho : ℂ,
      rho ∈ dynamicEqualRealPartZeroPackage H beta x ↔
        (starRingEnd ℂ) rho ∈
          dynamicEqualRealPartZeroPackage H beta x := by
  intro rho
  rw [mem_dynamicEqualRealPartZeroPackage,
    mem_dynamicEqualRealPartZeroPackage]
  constructor
  · rintro ⟨hzero, hheight, hre⟩
    exact
      ⟨RiemannVonMangoldt.isNontrivialZero_conj hzero,
        by simpa using hheight,
        by simpa using hre⟩
  · rintro ⟨hzero, hheight, hre⟩
    have hzero' :=
      RiemannVonMangoldt.isNontrivialZero_conj hzero
    exact
      ⟨by simpa using hzero',
        by simpa using hheight,
        by simpa using hre⟩

/-- The real part of a dynamic package is contained in the fixed finite
real-ordinate nontrivial-zero set. -/
theorem realPart_dynamicEqualRealPartZeroPackage_subset
    (H : ℝ → ℝ) (beta x : ℝ) :
    realFiniteVisibleClusterPart
        (dynamicEqualRealPartZeroPackage H beta x) ⊆
      realOrdinateNontrivialZerosFinset 0 := by
  intro rho hrho
  rcases Finset.mem_filter.mp hrho with ⟨hrhoPackage, him⟩
  have hzero :=
    (mem_dynamicEqualRealPartZeroPackage.mp hrhoPackage).1
  apply mem_realOrdinateNontrivialZerosFinset.mpr
  exact
    ⟨mem_nontrivialZerosFinset.mpr
        ⟨hzero, by simp [him]⟩,
      him⟩

/-- Explicit global coefficient cap for every dynamic boundary package. -/
def actualCarlsonDynamicBoundaryCoefficientCapConstant
    (sigma : ℝ) : ℝ :=
  2 *
      (∑' index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroWeight index) +
    finiteVisibleClusterCoefficientMass
      (realOrdinateNontrivialZerosFinset 0)

/--
Every dynamic equal-real-part package is bounded by the same explicit Carlson
plus real-ordinate coefficient constant.
-/
theorem finiteVisibleClusterCoefficientMass_dynamicEqualRealPartZeroPackage_le
    {sigma beta : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hsigmaBeta : sigma < beta)
    (H : ℝ → ℝ) (x : ℝ) :
    finiteVisibleClusterCoefficientMass
        (dynamicEqualRealPartZeroPackage H beta x) ≤
      actualCarlsonDynamicBoundaryCoefficientCapConstant sigma := by
  let E := dynamicEqualRealPartZeroPackage H beta x
  have hpositive :
      finiteVisibleClusterCoefficientMass
          (positiveFiniteVisibleClusterPart E) ≤
        ∑' index : ActualCarlsonPositiveZeroIndex sigma,
          actualCarlsonPositiveZeroWeight index := by
    apply
      finiteVisibleClusterCoefficientMass_le_actualCarlsonPositiveZeroWeight_tsum
        hhalf hone
    intro rho hrho
    have hrhoE :=
      positiveFiniteVisibleClusterPart_subset E hrho
    have hpackage :=
      mem_dynamicEqualRealPartZeroPackage.mp hrhoE
    exact
      ⟨hpackage.1,
        (Finset.mem_filter.mp hrho).2,
        by rw [hpackage.2.2]; exact hsigmaBeta⟩
  have hnegative :
      finiteVisibleClusterCoefficientMass
          (negativeFiniteVisibleClusterPart E) =
        finiteVisibleClusterCoefficientMass
          (positiveFiniteVisibleClusterPart E) := by
    apply finiteVisibleClusterCoefficientMass_negative_eq_positive
    · exact dynamicEqualRealPartZeroPackage_conjugationStable H beta x
    · intro rho hrho
      exact (mem_dynamicEqualRealPartZeroPackage.mp hrho).1
  have hreal :
      finiteVisibleClusterCoefficientMass
          (realFiniteVisibleClusterPart E) ≤
        finiteVisibleClusterCoefficientMass
          (realOrdinateNontrivialZerosFinset 0) :=
    finiteVisibleClusterCoefficientMass_mono
      (realPart_dynamicEqualRealPartZeroPackage_subset H beta x)
  rw [finiteVisibleClusterCoefficientMass_eq_positive_add_negative_add_real,
    hnegative]
  unfold actualCarlsonDynamicBoundaryCoefficientCapConstant
  linarith

/-- Automatic eventual cap consumed by the dynamic PNT upper transfer. -/
theorem actualCarlsonDynamicBoundaryCoefficientCap
    {sigma beta : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hsigmaBeta : sigma < beta)
    (H : ℝ → ℝ) :
    DynamicBoundaryPackageCoefficientCap beta H
      (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma) :=
  Filter.Eventually.of_forall fun m =>
    finiteVisibleClusterCoefficientMass_dynamicEqualRealPartZeroPackage_le
      hhalf hone hsigmaBeta H (m : ℝ)

end

end PrimeNumberTheorem
