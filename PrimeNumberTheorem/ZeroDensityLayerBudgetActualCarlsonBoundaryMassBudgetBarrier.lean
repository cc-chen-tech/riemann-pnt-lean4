import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteComparison

/-!
# Finite-extension budget barrier

The exact seed-relative mass allocation gives a sharp arithmetic obstruction
to simultaneously making the adjoined finite cluster and the final outside
boundary layer small.
-/

namespace PrimeNumberTheorem

/-- If an extension spends less than `loss` on finite coefficient mass and
leaves doubled outside mass below `gap`, then the seed's original outside
boundary mass is below `loss + gap / 2`. -/
theorem actualCarlsonSeedOutside_lt_loss_add_half_gap_of_extensionBudgets
    {sigma beta loss gap : ℝ} {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hadded :
      finiteVisibleClusterCoefficientMass (S \ S₀) < loss)
    (hgap :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < gap) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀ <
      loss + gap / 2 := by
  apply
    actualCarlsonSeedOutside_lt_add_of_extensionMass_lt_of_outside_lt
      hsub hhalf hone hadded
  linarith

/-- A seed whose outside boundary mass already exceeds the combined allowance
admits no finite extension satisfying both transfer budgets. -/
theorem
    not_exists_actualCarlsonFiniteExtension_of_seedOutside_ge_loss_add_half_gap
    {sigma beta loss gap : ℝ} {S₀ : Finset ℂ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hbarrier :
      loss + gap / 2 ≤
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S₀) :
    ¬ ∃ S : Finset ℂ,
        S₀ ⊆ S ∧
        finiteVisibleClusterCoefficientMass (S \ S₀) < loss ∧
        2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S < gap := by
  rintro ⟨S, hsub, hadded, hgap⟩
  have hlt :=
    actualCarlsonSeedOutside_lt_loss_add_half_gap_of_extensionBudgets
      hsub hhalf hone hadded hgap
  linarith

/-- For the canonical half-retention gap, the necessary seed allowance is
`loss + (c - loss) / 4`. -/
theorem
    actualCarlsonSeedOutside_lt_loss_add_quarter_net_of_canonicalBudgets
    {sigma beta c loss : ℝ} {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hadded :
      finiteVisibleClusterCoefficientMass (S \ S₀) < loss)
    (hgap :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀ <
      loss + (c - loss) / 4 := by
  have hlt :=
    actualCarlsonSeedOutside_lt_loss_add_half_gap_of_extensionBudgets
      hsub hhalf hone hadded hgap
  linarith

/-- If the seed violates the canonical quarter-net allowance, no finite
extension can satisfy both the coefficient-mass and half-retention gaps. -/
theorem
    not_exists_actualCarlsonFiniteExtension_of_seedOutside_ge_canonicalAllowance
    {sigma beta c loss : ℝ} {S₀ : Finset ℂ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hbarrier :
      loss + (c - loss) / 4 ≤
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S₀) :
    ¬ ∃ S : Finset ℂ,
        S₀ ⊆ S ∧
        finiteVisibleClusterCoefficientMass (S \ S₀) < loss ∧
        2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S <
          (c - loss) - (c - loss) / 2 := by
  rintro ⟨S, hsub, hadded, hgap⟩
  have hlt :=
    actualCarlsonSeedOutside_lt_loss_add_quarter_net_of_canonicalBudgets
      hsub hhalf hone hadded hgap
  linarith

end PrimeNumberTheorem
