import PrimeNumberTheorem.HalfIsolatedZeroDichotomy.Audit
import PrimeNumberTheorem.ZeroDensityAmplificationAuditIterationExpansionContract
import PrimeNumberTheorem.VKEdgeConditionalPackageContract

namespace PrimeNumberTheorem
namespace ExceptionalZeroAmplification

open Filter
open HalfIsolatedZeroDichotomy

/-- The density layer recursion agrees with the directed half-isolated recursion
when its children are the directed local-cluster successors. -/
theorem iterativeWindowLayer_eq_halfIsolatedDirectedIteration
    (roots : ℝ → Finset ℂ) (β δ : ℝ) (n : ℕ) (T : ℝ) :
    iterativeWindowLayer roots
        (fun _ T ρ => halfIsolatedDirectedNext T β δ ρ) n T =
      halfIsolatedDirectedIteration T β δ n (roots T) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [iterativeWindowLayer, halfIsolatedDirectedIteration]
      rw [ih]

/-- A genuine density-layer certificate built from the directed
half-isolated-zero successor relation. The hypotheses are the eventual
root, branching, and disjointness facts required by the existing density
certificate; no propagation conclusion is stored as a new field. -/
noncomputable def halfIsolatedDirectedWindowLayerCertificate
    (depth : ℕ) (roots : ℝ → Finset ℂ) (q : ℝ → ℕ) (β δ : ℝ)
    (hroots :
      ∀ᶠ T in atTop, 1 ≤ (roots T).card)
    (hbranch :
      ∀ n < depth, ∀ᶠ T in atTop,
        ∀ ρ ∈ halfIsolatedDirectedIteration T β δ n (roots T),
          q T ≤ (halfIsolatedDirectedNext T β δ ρ).card)
    (hdisjoint :
      ∀ n < depth, ∀ᶠ T in atTop,
        ((↑(halfIsolatedDirectedIteration T β δ n (roots T)) : Set ℂ)).PairwiseDisjoint
          (halfIsolatedDirectedNext T β δ)) :
    IterativeWindowLayerCertificate (ι := ℂ) where
  depth := depth
  roots := roots
  children := fun _ T ρ => halfIsolatedDirectedNext T β δ ρ
  q := q
  hroots_nonempty := hroots
  hbranch_degree := by
    intro n hn
    exact (hbranch n hn).mono (by
      intro T hT ρ hρ
      apply hT ρ
      rwa [iterativeWindowLayer_eq_halfIsolatedDirectedIteration] at hρ)
  hchildren_disjoint := by
    intro n hn
    exact (hdisjoint n hn).mono (by
      intro T hT
      simpa only [iterativeWindowLayer_eq_halfIsolatedDirectedIteration] using hT)

/-- Specialize the existing iterative Carlson contradiction to a layer
certificate whose vertices and children are actual directed half-isolated
zero candidates. The inferred remaining arguments are exactly the existing
depth, branch-count, local-window, density, and asymptotic-gap hypotheses. -/
noncomputable def exceptionalZeroAmplificationCarlsonAdapter
    {ρ : Type*} [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ℂ) realPart ordinate sigma H)
    (depth : ℕ) (roots : ℝ → Finset ℂ) (q : ℝ → ℕ) (β δ : ℝ)
    (hroots :
      ∀ᶠ T in atTop, 1 ≤ (roots T).card)
    (hbranch :
      ∀ n < depth, ∀ᶠ T in atTop,
        ∀ z ∈ halfIsolatedDirectedIteration T β δ n (roots T),
          q T ≤ (halfIsolatedDirectedNext T β δ z).card)
    (hdisjoint :
      ∀ n < depth, ∀ᶠ T in atTop,
        ((↑(halfIsolatedDirectedIteration T β δ n (roots T)) : Set ℂ)).PairwiseDisjoint
          (halfIsolatedDirectedNext T β δ)) :=
  iterativeWindowLayer_to_carlson_contradiction C
    (L := halfIsolatedDirectedWindowLayerCertificate
      depth roots q β δ hroots hbranch hdisjoint)

/-- The adapter is definitionally the existing Carlson contradiction with its
layer certificate instantiated by the directed half-isolated recursion. -/
theorem exceptionalZeroAmplification_to_carlson_of_expandingLayers
    {ρ : Type*} [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ℂ) realPart ordinate sigma H)
    (depth : ℕ) (roots : ℝ → Finset ℂ) (q : ℝ → ℕ) (β δ : ℝ)
    (hroots :
      ∀ᶠ T in atTop, 1 ≤ (roots T).card)
    (hbranch :
      ∀ n < depth, ∀ᶠ T in atTop,
        ∀ z ∈ halfIsolatedDirectedIteration T β δ n (roots T),
          q T ≤ (halfIsolatedDirectedNext T β δ z).card)
    (hdisjoint :
      ∀ n < depth, ∀ᶠ T in atTop,
        ((↑(halfIsolatedDirectedIteration T β δ n (roots T)) : Set ℂ)).PairwiseDisjoint
          (halfIsolatedDirectedNext T β δ)) :
    exceptionalZeroAmplificationCarlsonAdapter
        C depth roots q β δ hroots hbranch hdisjoint =
      iterativeWindowLayer_to_carlson_contradiction C
        (L := halfIsolatedDirectedWindowLayerCertificate
          depth roots q β δ hroots hbranch hdisjoint) := rfl

end ExceptionalZeroAmplification
end PrimeNumberTheorem
