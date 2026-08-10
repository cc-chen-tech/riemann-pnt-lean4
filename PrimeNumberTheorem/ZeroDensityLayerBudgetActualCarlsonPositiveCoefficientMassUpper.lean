import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPositiveZeroCoverage
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPositiveZeroIndexInjective
import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterCoefficientMass

/-!
# Positive zero coefficient mass below the Carlson total weight

Carlson's actual positive-zero index covers every positive nontrivial zeta
zero to the right of `sigma`, and the chosen index map is injective.  Therefore
the exact multiplicity-weighted reciprocal-norm mass of any finite family of
such zeros is bounded above by the complete summable Carlson weight.

This supplies the comparison direction needed for a uniform dynamic-package
upper bound.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

noncomputable section

/-- Forgetful embedding from high positive zeros to their complex values. -/
def actualCarlsonHighPositiveZeroValueEmbedding (sigma : ℝ) :
    ActualCarlsonHighPositiveZero sigma ↪ ℂ :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The coefficient mass of the complex values of a finite high-positive-zero
family is its finite Carlson-index weight sum. -/
theorem finiteVisibleClusterCoefficientMass_map_highPositive_eq
    {sigma : ℝ} (s : Finset (ActualCarlsonHighPositiveZero sigma)) :
    finiteVisibleClusterCoefficientMass
        (s.map (actualCarlsonHighPositiveZeroValueEmbedding sigma)) =
      ∑ rho ∈ s,
        actualCarlsonPositiveZeroWeight
          (actualCarlsonPositiveZeroIndexOf rho) := by
  unfold finiteVisibleClusterCoefficientMass
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro rho _
  simp [actualCarlsonHighPositiveZeroValueEmbedding,
    actualCarlsonPositiveZeroWeight_eq_coefficient,
    actualCarlsonPositiveZero_indexOf]

/--
Every finite high-positive-zero coefficient mass is bounded by the complete
Carlson positive-zero reciprocal weight.
-/
theorem finite_actualCarlsonHighPositiveZeroCoefficientMass_le_tsum
    {sigma : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (s : Finset (ActualCarlsonHighPositiveZero sigma)) :
    finiteVisibleClusterCoefficientMass
        (s.map (actualCarlsonHighPositiveZeroValueEmbedding sigma)) ≤
      ∑' index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroWeight index := by
  rw [finiteVisibleClusterCoefficientMass_map_highPositive_eq]
  let e : ActualCarlsonHighPositiveZero sigma ↪
      ActualCarlsonPositiveZeroIndex sigma :=
    ⟨actualCarlsonPositiveZeroIndexOf,
      actualCarlsonPositiveZeroIndexOf_injective⟩
  have hsum :
      (∑ rho ∈ s,
          actualCarlsonPositiveZeroWeight
            (actualCarlsonPositiveZeroIndexOf rho)) =
        ∑ index ∈ s.map e,
          actualCarlsonPositiveZeroWeight index := by
    rw [Finset.sum_map]
    simp [e]
  rw [hsum]
  exact
    (summable_actualCarlsonPositiveZeroWeight hhalf hone).sum_le_tsum
      (s.map e)
      (fun index _ => actualCarlsonPositiveZeroWeight_nonneg index)

/--
Ordinary finite-set facade: a finite complex zero family whose members are
high positive zeros has coefficient mass bounded by the Carlson total weight.
-/
theorem finiteVisibleClusterCoefficientMass_le_actualCarlsonPositiveZeroWeight_tsum
    {sigma : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    {E : Finset ℂ}
    (hE :
      ∀ rho ∈ E,
        RiemannHypothesis.IsNontrivialZero rho ∧
          0 < rho.im ∧ sigma < rho.re) :
    finiteVisibleClusterCoefficientMass E ≤
      ∑' index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroWeight index := by
  classical
  let lift : {rho : ℂ // rho ∈ E} ↪
      ActualCarlsonHighPositiveZero sigma :=
    ⟨fun rho => ⟨rho.1, hE rho.1 rho.2⟩, by
      intro rho₁ rho₂ heq
      apply Subtype.ext
      exact
        congrArg
          (fun z : ActualCarlsonHighPositiveZero sigma => z.1)
          heq⟩
  let s : Finset (ActualCarlsonHighPositiveZero sigma) :=
    E.attach.map lift
  have hvalues :
      s.map (actualCarlsonHighPositiveZeroValueEmbedding sigma) = E := by
    ext rho
    simp [s, lift, actualCarlsonHighPositiveZeroValueEmbedding]
  rw [← hvalues]
  exact
    finite_actualCarlsonHighPositiveZeroCoefficientMass_le_tsum
      hhalf hone s

end

end PrimeNumberTheorem
