import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonConjugateCapturedMass

/-!
# Conjugation-aware finite-seed Carlson barrier

A conjugation-stable extension made entirely of nontrivial zeta zeros pays
twice for every positive-height Carlson zero that it captures.  Combining
this factor-two cost with the exact seed-relative boundary-mass allocation
sharpens the canonical necessary condition from seed outside mass `< c` to
seed outside mass `< c / 2`.

The zeta-zero membership hypothesis is explicit.  It is not inferred merely
from boundary support.
-/

namespace PrimeNumberTheorem

/-- The difference of two conjugation-stable finite sets is conjugation
stable. -/
theorem finiteSeedExtension_sdiff_conjugationStable
    {S₀ S : Finset ℂ}
    (hseed :
      ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hfinal :
      ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) :
    ∀ rho : ℂ,
      rho ∈ S \ S₀ ↔ (starRingEnd ℂ) rho ∈ S \ S₀ := by
  intro rho
  simpa only [Finset.mem_sdiff] using
    and_congr (hfinal rho) (not_congr (hseed rho))

/-- Under conjugation stability and genuine zeta-zero membership of the
extension, successful canonical budgets force the seed's original outside
boundary mass below half of the local oscillation coefficient. -/
theorem
    actualCarlsonSeedOutside_lt_half_localCoefficient_of_conjugateCanonicalExtension
    {sigma beta c loss : ℝ} {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hnet : 0 < c - loss)
    (hstable :
      ∀ rho : ℂ,
        rho ∈ S \ S₀ ↔ (starRingEnd ℂ) rho ∈ S \ S₀)
    (hzero :
      ∀ rho ∈ S \ S₀,
        RiemannHypothesis.IsNontrivialZero rho)
    (hadded :
      finiteVisibleClusterCoefficientMass (S \ S₀) < loss)
    (hgap :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀ < c / 2 := by
  have hcaptured :
      2 * actualCarlsonCapturedBoundaryMass
            (sigma := sigma) beta (S \ S₀) <
        loss :=
    lt_of_le_of_lt
      (two_mul_actualCarlsonCapturedBoundaryMass_le_finiteVisibleClusterCoefficientMass
        (S \ S₀) hhalf hone hstable hzero)
      hadded
  have hallocation :=
    actualCarlsonCapturedBoundaryMass_extension_add_outside_eq_seedOutside
      (beta := beta) hsub hhalf hone
  linarith

/-- Conjugation stability of the seed and final cluster supplies the
extension-stability input to the half-coefficient barrier. -/
theorem
    actualCarlsonSeedOutside_lt_half_localCoefficient_of_stableCanonicalExtension
    {sigma beta c loss : ℝ} {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hnet : 0 < c - loss)
    (hseed :
      ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hfinal :
      ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hzero :
      ∀ rho ∈ S \ S₀,
        RiemannHypothesis.IsNontrivialZero rho)
    (hadded :
      finiteVisibleClusterCoefficientMass (S \ S₀) < loss)
    (hgap :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀ < c / 2 :=
  actualCarlsonSeedOutside_lt_half_localCoefficient_of_conjugateCanonicalExtension
    hsub hhalf hone hnet
    (finiteSeedExtension_sdiff_conjugationStable hseed hfinal)
    hzero hadded hgap

/-- If the seed outside mass is at least `c / 2`, no fixed admissible loss
admits a conjugation-stable, zero-supported canonical extension. -/
theorem
    not_exists_conjugateActualCarlsonCanonicalFiniteExtension_of_halfCoefficient_le_seedOutside
    {sigma beta c loss : ℝ} {S₀ : Finset ℂ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hnet : 0 < c - loss)
    (hseed :
      c / 2 ≤ actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀) :
    ¬ ∃ S : Finset ℂ,
        S₀ ⊆ S ∧
        (∀ rho : ℂ,
          rho ∈ S \ S₀ ↔
            (starRingEnd ℂ) rho ∈ S \ S₀) ∧
        (∀ rho ∈ S \ S₀,
          RiemannHypothesis.IsNontrivialZero rho) ∧
        finiteVisibleClusterCoefficientMass (S \ S₀) < loss ∧
        2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S <
          (c - loss) - (c - loss) / 2 := by
  rintro ⟨S, hsub, hstable, hzero, hadded, hgap⟩
  have hlt :=
    actualCarlsonSeedOutside_lt_half_localCoefficient_of_conjugateCanonicalExtension
      hsub hhalf hone hnet hstable hzero hadded hgap
  linarith

/-- Varying the loss cannot evade the half-coefficient obstruction. -/
theorem
    not_exists_loss_and_conjugateActualCarlsonCanonicalFiniteExtension_of_halfCoefficient_le_seedOutside
    {sigma beta c : ℝ} {S₀ : Finset ℂ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hseed :
      c / 2 ≤ actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀) :
    ¬ ∃ loss : ℝ, ∃ S : Finset ℂ,
        0 < c - loss ∧
        S₀ ⊆ S ∧
        (∀ rho : ℂ,
          rho ∈ S \ S₀ ↔
            (starRingEnd ℂ) rho ∈ S \ S₀) ∧
        (∀ rho ∈ S \ S₀,
          RiemannHypothesis.IsNontrivialZero rho) ∧
        finiteVisibleClusterCoefficientMass (S \ S₀) < loss ∧
        2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S <
          (c - loss) - (c - loss) / 2 := by
  rintro ⟨loss, S, hnet, hsub, hstable, hzero, hadded, hgap⟩
  exact
    (not_exists_conjugateActualCarlsonCanonicalFiniteExtension_of_halfCoefficient_le_seedOutside
      hhalf hone hnet hseed)
      ⟨S, hsub, hstable, hzero, hadded, hgap⟩

end PrimeNumberTheorem
