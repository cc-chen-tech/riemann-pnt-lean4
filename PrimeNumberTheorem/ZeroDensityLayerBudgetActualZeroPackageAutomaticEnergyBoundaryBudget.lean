import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageFiniteHeightBoundaryCapture

/-!
# Automatic actual-package energy versus Carlson boundary budget

A nonempty target-line seed supplies a fixed positive diagonal-energy anchor.
Use half of that anchor to choose an arbitrarily small Carlson boundary tail,
enlarge to an actual height package, and only then choose a smoothing window
whose package energy stays above the anchor.  This order removes the apparent
circularity between package energy and boundary-tail size.
-/

namespace PrimeNumberTheorem

open scoped BigOperators
open Complex ZeroForcedOscillation

noncomputable section

/-- Diagonal package energy is monotone under inclusion of the underlying
equal-real-part packages. -/
theorem actualEqualRealPartZeroPackageDiagonalEnergy_mono_of_subset
    {T₀ T beta : ℝ}
    (hsub :
      equalRealPartZeroPackage T₀ beta ⊆
        equalRealPartZeroPackage T beta) :
    actualEqualRealPartZeroPackageDiagonalEnergy T₀ beta ≤
      actualEqualRealPartZeroPackageDiagonalEnergy T beta := by
  unfold actualEqualRealPartZeroPackageDiagonalEnergy
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro rho _ _
  positivity

/--
A nonempty target-line seed under a global right-edge cap automatically
produces an actual height package and smoothing window whose positive energy
dominates the remaining Carlson boundary mass at every fixed `q > 0`.
-/
theorem exists_actualZeroPackage_energy_boundaryBudget
    {S₀ : Finset ℂ} {sigma beta q : ℝ}
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hnonempty : S₀.Nonempty)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hq : 0 < q) :
    ∃ T L : ℝ,
      0 ≤ T ∧
      0 < L ∧
      (∀ rho ∈ S₀, rho ∈ equalRealPartZeroPackage T beta) ∧
      OutsideClusterRealPartCap
        (equalRealPartZeroPackage T beta) beta ∧
      0 < actualEqualRealPartZeroPackageEnergy T beta L ∧
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (equalRealPartZeroPackage T beta) <
        (q * Real.sqrt
          (actualEqualRealPartZeroPackageEnergy T beta L)) / 2 := by
  rcases
      exists_height_targetLineSeed_subset_equalRealPartZeroPackage hseed with
    ⟨T₀, _hT₀, hS₀P₀⟩
  let P₀ := equalRealPartZeroPackage T₀ beta
  have hP₀Nonempty : P₀.Nonempty := by
    rcases hnonempty with ⟨rho, hrho⟩
    exact ⟨rho, hS₀P₀ rho hrho⟩
  have hD₀ :
      0 < actualEqualRealPartZeroPackageDiagonalEnergy T₀ beta :=
    actualEqualRealPartZeroPackageDiagonalEnergy_pos_of_nonempty hP₀Nonempty
  have hP₀Stable :
      ∀ rho : ℂ, rho ∈ P₀ ↔ (starRingEnd ℂ) rho ∈ P₀ := by
    intro rho
    exact
      (equalRealPartZeroPackage_isConjugationInvariant T₀ beta rho).symm
  have hP₀Seed : IsTargetRealPartNontrivialZeroSeed beta P₀ := by
    intro rho hrho
    have hrhoData := mem_equalRealPartZeroPackage.mp hrho
    exact ⟨hrhoData.1, hrhoData.2.2⟩
  have hP₀Cap : OutsideClusterRealPartCap P₀ beta := by
    intro rho hzero houtP₀
    apply hcap rho hzero
    intro hrhoS₀
    exact houtP₀ (hS₀P₀ rho hrhoS₀)
  let d := actualEqualRealPartZeroPackageDiagonalEnergy T₀ beta / 2
  have hd : 0 < d := by
    dsimp [d]
    linarith
  let epsilon := q * Real.sqrt d / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  rcases
      exists_actualZeroPackage_boundaryMass_lt
        (S₀ := P₀) (sigma := sigma) (beta := beta)
        hP₀Stable hP₀Seed hhalf hone hP₀Cap hepsilon with
    ⟨T, hT, hP₀P, hcapP, hmass⟩
  have hDmono :
      actualEqualRealPartZeroPackageDiagonalEnergy T₀ beta ≤
        actualEqualRealPartZeroPackageDiagonalEnergy T beta :=
    actualEqualRealPartZeroPackageDiagonalEnergy_mono_of_subset
      (fun rho hrho => hP₀P rho hrho)
  have hdD :
      d < actualEqualRealPartZeroPackageDiagonalEnergy T beta := by
    dsimp [d]
    linarith
  rcases exists_actualEqualRealPartZeroPackageEnergy_gt hdD with
    ⟨L, hL, henergyLower⟩
  have henergy :
      0 < actualEqualRealPartZeroPackageEnergy T beta L :=
    hd.trans henergyLower
  have hsqrt :
      Real.sqrt d <
        Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) := by
    have hdSq := Real.sq_sqrt hd.le
    have henergySq := Real.sq_sqrt henergy.le
    have hdSqrtNonneg := Real.sqrt_nonneg d
    have henergySqrtNonneg :=
      Real.sqrt_nonneg (actualEqualRealPartZeroPackageEnergy T beta L)
    nlinarith
  have hepsilonTarget :
      epsilon <
        q * Real.sqrt
            (actualEqualRealPartZeroPackageEnergy T beta L) / 2 := by
    have hscaled := mul_lt_mul_of_pos_left hsqrt hq
    dsimp [epsilon]
    linarith
  have hS₀P :
      ∀ rho ∈ S₀, rho ∈ equalRealPartZeroPackage T beta := by
    intro rho hrho
    exact hP₀P rho (hS₀P₀ rho hrho)
  exact
    ⟨T, L, hT, hL, hS₀P, hcapP, henergy,
      hmass.trans hepsilonTarget⟩

end
end PrimeNumberTheorem
