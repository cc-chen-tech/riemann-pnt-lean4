import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassBudgetBarrier

/-!
# Canonical finite-seed Carlson barrier

For a positive retained net coefficient `c - loss`, the canonical combined
allowance

`loss + (c - loss) / 4`

is strictly smaller than `c`.  Thus any finite extension satisfying both the
coefficient-mass perturbation budget and the canonical Carlson outside-mass
gap forces the original seed outside mass to be strictly below the seed
oscillation coefficient `c`.
-/

namespace PrimeNumberTheorem

/-- A successful canonical finite extension necessarily starts from a seed
whose outside boundary mass is smaller than the local oscillation
coefficient. -/
theorem actualCarlsonSeedOutside_lt_localCoefficient_of_canonicalExtension
    {sigma beta c loss : ℝ} {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hnet : 0 < c - loss)
    (hadded :
      finiteVisibleClusterCoefficientMass (S \ S₀) < loss)
    (hgap :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀ < c := by
  have hbudget :=
    actualCarlsonSeedOutside_lt_loss_add_quarter_net_of_canonicalBudgets
      hsub hhalf hone hadded hgap
  linarith

/-- If the seed outside mass is at least `c`, no fixed admissible `loss` can
produce a canonical finite extension satisfying both budgets. -/
theorem
    not_exists_actualCarlsonCanonicalFiniteExtension_of_localCoefficient_le_seedOutside
    {sigma beta c loss : ℝ} {S₀ : Finset ℂ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hnet : 0 < c - loss)
    (hseed :
      c ≤ actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀) :
    ¬ ∃ S : Finset ℂ,
        S₀ ⊆ S ∧
        finiteVisibleClusterCoefficientMass (S \ S₀) < loss ∧
        2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S <
          (c - loss) - (c - loss) / 2 := by
  rintro ⟨S, hsub, hadded, hgap⟩
  have hlt :=
    actualCarlsonSeedOutside_lt_localCoefficient_of_canonicalExtension
      hsub hhalf hone hnet hadded hgap
  linarith

/-- If the seed outside mass is at least `c`, varying `loss` cannot rescue the
canonical finite-extension strategy. -/
theorem
    not_exists_loss_and_actualCarlsonCanonicalFiniteExtension_of_localCoefficient_le_seedOutside
    {sigma beta c : ℝ} {S₀ : Finset ℂ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hseed :
      c ≤ actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀) :
    ¬ ∃ loss : ℝ, ∃ S : Finset ℂ,
        0 < c - loss ∧
        S₀ ⊆ S ∧
        finiteVisibleClusterCoefficientMass (S \ S₀) < loss ∧
        2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S <
          (c - loss) - (c - loss) / 2 := by
  rintro ⟨loss, S, hnet, hsub, hadded, hgap⟩
  exact
    (not_exists_actualCarlsonCanonicalFiniteExtension_of_localCoefficient_le_seedOutside
      hhalf hone hnet hseed)
      ⟨S, hsub, hadded, hgap⟩

end PrimeNumberTheorem
