import PrimeNumberTheorem.ZeroDensityLayerBudgetAttainedGlobalRightEdgeReciprocalOmega

/-!
# Real-ordinate closed seed at an attained global right edge

The conjugate-pair seed is enlarged by every real-ordinate nontrivial zero on
the same maximal real-part line.  Any actual equal-real-part package containing
this finite seed then has a strict real-ordinate gap outside the package.
-/

namespace PrimeNumberTheorem

open Complex ZeroForcedOscillation

noncomputable section

/-- Conjugate pair together with every real-ordinate nontrivial zero on the
same real-part line. -/
noncomputable def attainedGlobalRightEdgeRealClosedSeed (rho : ℂ) : Finset ℂ :=
  {rho, (starRingEnd ℂ) rho} ∪
    (realOrdinateNontrivialZerosFinset 0).filter (fun z => z.re = rho.re)

/-- The real-closed seed is nonempty, lies on the target line, supplies the
global outside cap, and forces a strict real-ordinate gap outside every actual
equal-real-part package containing it. -/
theorem attainedGlobalRightEdgeRealClosedSeed_spec
    {rho : ℂ} (hattained : IsAttainedGlobalNontrivialZeroRealPart rho) :
    IsTargetRealPartNontrivialZeroSeed rho.re
        (attainedGlobalRightEdgeRealClosedSeed rho) ∧
      (attainedGlobalRightEdgeRealClosedSeed rho).Nonempty ∧
      OutsideClusterRealPartCap
        (attainedGlobalRightEdgeRealClosedSeed rho) rho.re ∧
      ∀ {T : ℝ},
        (∀ z ∈ attainedGlobalRightEdgeRealClosedSeed rho,
          z ∈ equalRealPartZeroPackage T rho.re) →
        ∀ z ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0
            (equalRealPartZeroPackage T rho.re),
          z.re < rho.re := by
  classical
  have hpair := attainedGlobalNontrivialZeroRealPart_conjugatePair_spec hattained
  have hseed : IsTargetRealPartNontrivialZeroSeed rho.re
      (attainedGlobalRightEdgeRealClosedSeed rho) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hpairMem | hrealMem
    · exact hpair.1 z hpairMem
    · rcases Finset.mem_filter.mp hrealMem with ⟨hreal, hre⟩
      have hdata := mem_realOrdinateNontrivialZerosFinset.mp hreal
      exact ⟨(mem_nontrivialZerosFinset.mp hdata.1).1, hre⟩
  have hnonempty : (attainedGlobalRightEdgeRealClosedSeed rho).Nonempty := by
    exact ⟨rho, Finset.mem_union_left _ (by simp)⟩
  have hcap : OutsideClusterRealPartCap
      (attainedGlobalRightEdgeRealClosedSeed rho) rho.re := by
    intro z hz _
    exact hattained.2 z hz
  refine ⟨hseed, hnonempty, hcap, ?_⟩
  intro T hcontains z hz
  rcases Finset.mem_sdiff.mp hz with ⟨hreal, hout⟩
  have hdata := mem_realOrdinateNontrivialZerosFinset.mp hreal
  have hzero : RiemannHypothesis.IsNontrivialZero z :=
    (mem_nontrivialZerosFinset.mp hdata.1).1
  have hle : z.re ≤ rho.re := hattained.2 z hzero
  have hne : z.re ≠ rho.re := by
    intro hre
    have hseedMem : z ∈ attainedGlobalRightEdgeRealClosedSeed rho := by
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hreal, hre⟩
    exact hout (hcontains z hseedMem)
  exact lt_of_le_of_ne hle hne

end
end PrimeNumberTheorem
