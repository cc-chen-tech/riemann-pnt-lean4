import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedTargetLineSelector
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageQuantitativeEnergy

/-!
# Finite-height actual-package capture of Carlson boundary mass

A finite target-line zeta seed fits inside an equal-real-part package at one
finite height.  Combining this elementary height choice with the existing
target-line Carlson selector turns arbitrary finite boundary capture into an
actual height-package capture.
-/

namespace PrimeNumberTheorem

open scoped BigOperators
open Complex ZeroForcedOscillation

noncomputable section

/-- Every finite target-line nontrivial-zero seed is contained in an actual
equal-real-part package at a nonnegative finite height. -/
theorem exists_height_targetLineSeed_subset_equalRealPartZeroPackage
    {S : Finset ℂ} {beta : ℝ}
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ rho ∈ S, rho ∈ equalRealPartZeroPackage T beta := by
  let T := ∑ rho ∈ S, |rho.im|
  have hT : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg fun rho _ => abs_nonneg rho.im
  refine ⟨T, hT, ?_⟩
  intro rho hrho
  have him : |rho.im| ≤ T := by
    dsimp [T]
    exact
      Finset.single_le_sum
        (fun z hz => abs_nonneg z.im) hrho
  exact mem_equalRealPartZeroPackage.mpr
    ⟨(hseed rho hrho).1, him, (hseed rho hrho).2⟩

/--
Under a global real-part cap supplied by a target-line seed, an actual finite
height package can make the outside Carlson boundary mass smaller than any
prescribed positive tolerance.
-/
theorem exists_actualZeroPackage_boundaryMass_lt
    {S₀ : Finset ℂ} {sigma beta epsilon : ℝ}
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hepsilon : 0 < epsilon) :
    ∃ T : ℝ,
      0 ≤ T ∧
      (∀ rho ∈ S₀, rho ∈ equalRealPartZeroPackage T beta) ∧
      OutsideClusterRealPartCap
        (equalRealPartZeroPackage T beta) beta ∧
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (equalRealPartZeroPackage T beta) <
        epsilon := by
  rcases
      exists_targetLine_actualCarlsonFiniteSeedGapTransferCluster
        (sigma := sigma) (beta := beta) (c := 2 * epsilon) (q := 0)
        hS₀ hseed hhalf hone (by linarith) hcap with
    ⟨S, hS₀S, _hS, htarget, hcapS, _hreHigh, _hreReal, hgap⟩
  rcases
      exists_height_targetLineSeed_subset_equalRealPartZeroPackage htarget with
    ⟨T, hT, hSPackage⟩
  have hS₀Package :
      ∀ rho ∈ S₀, rho ∈ equalRealPartZeroPackage T beta := by
    intro rho hrho
    exact hSPackage rho (hS₀S rho hrho)
  have hcapPackage :
      OutsideClusterRealPartCap
        (equalRealPartZeroPackage T beta) beta := by
    intro rho hzero houtPackage
    apply hcapS rho hzero
    intro hrhoS
    exact houtPackage (hSPackage rho hrhoS)
  have hmassS :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < epsilon := by
    linarith
  have hmassPackage :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (equalRealPartZeroPackage T beta) <
        epsilon := by
    exact
      (actualCarlsonOutsideClusterBoundaryMass_antitone
        hhalf hone (fun rho hrho => hSPackage rho hrho)).trans_lt hmassS
  exact ⟨T, hT, hS₀Package, hcapPackage, hmassPackage⟩

end
end PrimeNumberTheorem
