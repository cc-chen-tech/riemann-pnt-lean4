import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedZeroSupportedSelector
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer

/-!
# Target-line finite-seed Carlson selector

Boundary filtering removes auxiliary real-ordinate zeros that need not lie on
the target line while preserving the captured Carlson boundary mass exactly.
-/

namespace PrimeNumberTheorem

open Complex

noncomputable section

/-- A conjugation-stable target-line zeta seed extends to a finite target-line
cluster which retains the Carlson outside cap, strict real-ordinate residual,
and prescribed boundary-mass gap. -/
theorem exists_targetLine_actualCarlsonFiniteSeedGapTransferCluster
    {S₀ : Finset ℂ} {sigma beta c q : ℝ}
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hqC : q < c)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ S : Finset ℂ,
      (∀ rho ∈ S₀, rho ∈ S) ∧
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      IsTargetRealPartNontrivialZeroSeed beta S ∧
      OutsideClusterRealPartCap S beta ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q := by
  rcases
      exists_zeroSupportedExtension_actualCarlsonFiniteSeedGapTransferCluster
        hS₀ hhalf hone hqC hcap with
    ⟨T, hS₀T, hT, hcapT, hzeroExtension, _hboundarySupport,
      _hreHighT, hreRealT, hgapT⟩
  let S := actualCarlsonBoundaryClusterPart beta T
  have hS₀S : ∀ rho ∈ S₀, rho ∈ S := by
    intro rho hrho
    exact mem_actualCarlsonBoundaryClusterPart.mpr
      ⟨hS₀T rho hrho, (hseed rho hrho).2⟩
  have hS :
      ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S := by
    intro rho
    exact actualCarlsonBoundaryClusterPart_conjugationStable hT rho
  have htarget : IsTargetRealPartNontrivialZeroSeed beta S := by
    intro rho hrho
    rcases mem_actualCarlsonBoundaryClusterPart.mp hrho with
      ⟨hrhoT, hre⟩
    refine ⟨?_, hre⟩
    by_cases hrhoSeed : rho ∈ S₀
    · exact (hseed rho hrhoSeed).1
    · exact hzeroExtension rho
        (Finset.mem_sdiff.mpr ⟨hrhoT, hrhoSeed⟩)
  have hcapS : OutsideClusterRealPartCap S beta := by
    intro rho hzero houtS
    by_cases hrhoT : rho ∈ T
    · have houtSeed : rho ∉ S₀ := by
        intro hrhoSeed
        exact houtS (hS₀S rho hrhoSeed)
      exact hcap rho hzero houtSeed
    · exact hcapT rho hzero hrhoT
  have hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta :=
    fun index hout =>
      hcapS.actualCarlsonPositiveZeroRealPart_le index hout
  have hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta := by
    intro rho hrho
    have hreal : rho ∈ realOrdinateNontrivialZerosFinset 0 :=
      (Finset.mem_sdiff.mp hrho).1
    have houtS : rho ∉ S := (Finset.mem_sdiff.mp hrho).2
    by_cases hrhoT : rho ∈ T
    · have hzero : RiemannHypothesis.IsNontrivialZero rho :=
        (mem_nontrivialZerosFinset.mp
          (mem_realOrdinateNontrivialZerosFinset.mp hreal).1).1
      have hle : rho.re ≤ beta := hcapS rho hzero houtS
      have hne : rho.re ≠ beta := by
        intro hre
        exact houtS
          (mem_actualCarlsonBoundaryClusterPart.mpr ⟨hrhoT, hre⟩)
      exact lt_of_le_of_ne hle hne
    · exact hreRealT rho (Finset.mem_sdiff.mpr ⟨hreal, hrhoT⟩)
  have hgap :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q := by
    simpa [S,
      actualCarlsonOutsideClusterBoundaryMass_boundaryClusterPart] using
      hgapT
  exact ⟨S, hS₀S, hS, htarget, hcapS, hreHigh, hreReal, hgap⟩

end

end PrimeNumberTheorem

