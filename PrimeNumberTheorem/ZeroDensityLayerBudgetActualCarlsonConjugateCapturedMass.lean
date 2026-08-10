import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteComparison
import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition

/-!
# Conjugate cost of captured positive Carlson mass

Carlson boundary mass is indexed only by positive-height zeros.  A
conjugation-stable finite visible cluster must also pay for the corresponding
negative-height zeros.  For a finite cluster consisting of nontrivial zeta
zeros, this doubles the captured coefficient cost.
-/

namespace PrimeNumberTheorem

open Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Positive-height part of a finite visible cluster. -/
def positiveFiniteVisibleClusterPart (E : Finset ℂ) : Finset ℂ :=
  E.filter fun rho => 0 < rho.im

/-- Negative-height part of a finite visible cluster. -/
def negativeFiniteVisibleClusterPart (E : Finset ℂ) : Finset ℂ :=
  E.filter fun rho => rho.im < 0

theorem positiveFiniteVisibleClusterPart_subset (E : Finset ℂ) :
    positiveFiniteVisibleClusterPart E ⊆ E := by
  intro rho hrho
  exact (Finset.mem_filter.mp hrho).1

theorem negativeFiniteVisibleClusterPart_subset (E : Finset ℂ) :
    negativeFiniteVisibleClusterPart E ⊆ E := by
  intro rho hrho
  exact (Finset.mem_filter.mp hrho).1

/-- The positive and negative finite cluster parts are disjoint. -/
theorem positiveFiniteVisibleClusterPart_disjoint_negative
    (E : Finset ℂ) :
    Disjoint
      (positiveFiniteVisibleClusterPart E)
      (negativeFiniteVisibleClusterPart E) := by
  rw [Finset.disjoint_left]
  intro rho hpos hneg
  have hposIm := (Finset.mem_filter.mp hpos).2
  have hnegIm := (Finset.mem_filter.mp hneg).2
  linarith

/-- The combined strict half-plane coefficient mass is bounded by the full
finite cluster coefficient mass. -/
theorem finiteVisibleClusterCoefficientMass_positive_add_negative_le
    (E : Finset ℂ) :
    finiteVisibleClusterCoefficientMass
          (positiveFiniteVisibleClusterPart E) +
        finiteVisibleClusterCoefficientMass
          (negativeFiniteVisibleClusterPart E) ≤
      finiteVisibleClusterCoefficientMass E := by
  let weight : ℂ → ℝ :=
    fun rho => (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖
  have hsub :
      positiveFiniteVisibleClusterPart E ∪
          negativeFiniteVisibleClusterPart E ⊆ E := by
    intro rho hrho
    rcases Finset.mem_union.mp hrho with hpos | hneg
    · exact positiveFiniteVisibleClusterPart_subset E hpos
    · exact negativeFiniteVisibleClusterPart_subset E hneg
  have hnonneg : ∀ rho, rho ∈ E → 0 ≤ weight rho := by
    intro rho _
    dsimp [weight]
    positivity
  unfold finiteVisibleClusterCoefficientMass
  calc
    (∑ rho ∈ positiveFiniteVisibleClusterPart E, weight rho) +
          ∑ rho ∈ negativeFiniteVisibleClusterPart E, weight rho =
        ∑ rho ∈
          positiveFiniteVisibleClusterPart E ∪
            negativeFiniteVisibleClusterPart E,
          weight rho := by
      exact
        (Finset.sum_union
          (positiveFiniteVisibleClusterPart_disjoint_negative E)).symm
    _ ≤ ∑ rho ∈ E, weight rho := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun rho hrho _ => hnonneg rho hrho)

/-- Conjugation preserves the exact multiplicity-weighted coefficient of a
nontrivial zeta zero. -/
theorem finiteVisibleZeroCoefficient_conj
    {rho : ℂ} (hzero : RiemannHypothesis.IsNontrivialZero rho) :
    (analyticOrderNatAt riemannZeta (conj rho) : ℝ) / ‖conj rho‖ =
      (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ := by
  rw [
    RiemannVonMangoldt.analyticOrderNatAt_riemannZeta_conj_of_nontrivialZero
      hzero,
    norm_conj]

/-- Conjugation-stable finite zeta-zero clusters have equal positive and
negative coefficient masses. -/
theorem finiteVisibleClusterCoefficientMass_negative_eq_positive
    {E : Finset ℂ}
    (hstable :
      ∀ rho : ℂ, rho ∈ E ↔ (starRingEnd ℂ) rho ∈ E)
    (hzero :
      ∀ rho ∈ E, RiemannHypothesis.IsNontrivialZero rho) :
    finiteVisibleClusterCoefficientMass
        (negativeFiniteVisibleClusterPart E) =
      finiteVisibleClusterCoefficientMass
        (positiveFiniteVisibleClusterPart E) := by
  let weight : ℂ → ℝ :=
    fun rho => (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖
  have hsum :
      (∑ rho ∈ positiveFiniteVisibleClusterPart E, weight rho) =
        ∑ rho ∈ negativeFiniteVisibleClusterPart E, weight rho := by
    apply Finset.sum_bij (fun rho _ => conj rho)
    · intro rho hrho
      have hrho' := Finset.mem_filter.mp hrho
      apply Finset.mem_filter.mpr
      exact ⟨(hstable rho).mp hrho'.1, by simpa using neg_neg_of_pos hrho'.2⟩
    · intro rho₁ _ rho₂ _ heq
      have h := congrArg conj heq
      simpa using h
    · intro rho hrho
      have hrho' := Finset.mem_filter.mp hrho
      refine ⟨conj rho, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact
          ⟨(hstable rho).mp hrho'.1,
            by simpa using neg_pos.mpr hrho'.2⟩
      · simp
    · intro rho hrho
      have hrhoE :=
        positiveFiniteVisibleClusterPart_subset E hrho
      exact
        (finiteVisibleZeroCoefficient_conj
          (hzero rho hrhoE)).symm
  unfold finiteVisibleClusterCoefficientMass
  exact hsum.symm

/-- A conjugation-stable finite zeta-zero cluster pays at least twice the
coefficient mass of its positive-height part. -/
theorem
    two_mul_finiteVisibleClusterCoefficientMass_positive_le
    {E : Finset ℂ}
    (hstable :
      ∀ rho : ℂ, rho ∈ E ↔ (starRingEnd ℂ) rho ∈ E)
    (hzero :
      ∀ rho ∈ E, RiemannHypothesis.IsNontrivialZero rho) :
    2 * finiteVisibleClusterCoefficientMass
          (positiveFiniteVisibleClusterPart E) ≤
      finiteVisibleClusterCoefficientMass E := by
  have hhalf :=
    finiteVisibleClusterCoefficientMass_positive_add_negative_le E
  rw [
    finiteVisibleClusterCoefficientMass_negative_eq_positive
      hstable hzero] at hhalf
  linarith

/-- Restricting a cluster to positive height does not change the captured
Carlson mass, because every Carlson index represents a positive-height
zero. -/
theorem actualCarlsonCapturedBoundaryMass_positivePart
    {sigma beta : ℝ} (E : Finset ℂ) :
    actualCarlsonCapturedBoundaryMass
        (sigma := sigma) beta
        (positiveFiniteVisibleClusterPart E) =
      actualCarlsonCapturedBoundaryMass
        (sigma := sigma) beta E := by
  unfold actualCarlsonCapturedBoundaryMass
  apply tsum_congr
  intro index
  have him : 0 < (actualCarlsonPositiveZero index).im :=
    (actualCarlsonPositiveZero_spec index).2.1
  by_cases hre : actualCarlsonPositiveZeroRealPart index = beta
  · by_cases hmem : actualCarlsonPositiveZero index ∈ E
    · simp [actualCarlsonCapturedBoundaryTerm,
        positiveFiniteVisibleClusterPart, hre, hmem, him]
    · simp [actualCarlsonCapturedBoundaryTerm,
        positiveFiniteVisibleClusterPart, hre, hmem]
  · simp [actualCarlsonCapturedBoundaryTerm, hre]

/-- A conjugation-stable finite cluster of zeta zeros pays at least twice its
captured positive Carlson boundary mass. -/
theorem
    two_mul_actualCarlsonCapturedBoundaryMass_le_finiteVisibleClusterCoefficientMass
    {sigma beta : ℝ} (E : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hstable :
      ∀ rho : ℂ, rho ∈ E ↔ (starRingEnd ℂ) rho ∈ E)
    (hzero :
      ∀ rho ∈ E, RiemannHypothesis.IsNontrivialZero rho) :
    2 * actualCarlsonCapturedBoundaryMass
          (sigma := sigma) beta E ≤
      finiteVisibleClusterCoefficientMass E := by
  have hcaptured :
      actualCarlsonCapturedBoundaryMass
          (sigma := sigma) beta E ≤
        finiteVisibleClusterCoefficientMass
          (positiveFiniteVisibleClusterPart E) := by
    rw [← actualCarlsonCapturedBoundaryMass_positivePart E]
    exact
      actualCarlsonCapturedBoundaryMass_le_finiteVisibleClusterCoefficientMass
        (positiveFiniteVisibleClusterPart E) hhalf hone
  have hdouble :=
    two_mul_finiteVisibleClusterCoefficientMass_positive_le
      hstable hzero
  linarith

end

end PrimeNumberTheorem
