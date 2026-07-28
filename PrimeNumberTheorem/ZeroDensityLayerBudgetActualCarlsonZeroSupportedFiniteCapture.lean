import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteGapSupportedCapture
import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition

/-!
# Zero-supported finite Carlson capture

The standard finite Carlson capture is constructed from actual positive zeta
zeros, but its public existential interface forgets that fact.  This module
retains zero support through finite capture, conjugation closure, and boundary
filtering.
-/

namespace PrimeNumberTheorem

open Complex

noncomputable section

/-- Every member of a finite Carlson index image is a nontrivial zeta zero. -/
theorem actualCarlsonBoundaryCaptureFinset_isNontrivialZero
    {sigma : ℝ}
    (F : Finset (ActualCarlsonPositiveZeroIndex sigma))
    {rho : ℂ}
    (hrho : rho ∈ actualCarlsonBoundaryCaptureFinset F) :
    RiemannHypothesis.IsNontrivialZero rho := by
  rcases Finset.mem_image.mp hrho with ⟨index, _, rfl⟩
  exact (actualCarlsonPositiveZero_spec index).1

/-- The summable Carlson boundary tail admits a finite capture consisting
entirely of nontrivial zeta zeros. -/
theorem exists_zeroSupported_actualCarlsonOutsideClusterBoundaryMass_lt
    {sigma beta epsilon : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hepsilon : 0 < epsilon) :
    ∃ S : Finset ℂ,
      (∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho) ∧
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < epsilon := by
  classical
  have hsummable :
      Summable (@actualCarlsonBoundaryTerm sigma beta) :=
    summable_actualCarlsonBoundaryTerm hhalf hone
  obtain ⟨F, hF⟩ :=
    (summable_iff_vanishing_norm.mp hsummable)
      (epsilon / 2) (by linarith)
  let S : Finset ℂ := actualCarlsonBoundaryCaptureFinset F
  refine ⟨S, ?_, ?_⟩
  · intro rho hrho
    exact actualCarlsonBoundaryCaptureFinset_isNontrivialZero F hrho
  · unfold actualCarlsonOutsideClusterBoundaryMass weightedPowerBoundaryMass
    have htermNonneg :
        0 ≤
          (fun index : ActualCarlsonPositiveZeroIndex sigma =>
            if actualCarlsonOutsideClusterRealPart beta S index = beta then
              actualCarlsonOutsideClusterWeight S index
            else 0) := by
      intro index
      by_cases heq :
          actualCarlsonOutsideClusterRealPart beta S index = beta
      · simp [heq, actualCarlsonOutsideClusterWeight_nonneg S index]
      · simp [heq]
    refine
      (Real.tsum_le_of_sum_le (c := epsilon / 2) htermNonneg ?_).trans_lt
        (by linarith)
    intro u
    let t :=
      u.filter
        (fun index : ActualCarlsonPositiveZeroIndex sigma =>
          actualCarlsonPositiveZero index ∉ S)
    have htF : Disjoint t F := by
      rw [Finset.disjoint_left]
      intro index hindexT hindexF
      have houtside :
          actualCarlsonPositiveZero index ∉ S :=
        (Finset.mem_filter.mp hindexT).2
      apply houtside
      exact Finset.mem_image.mpr ⟨index, hindexF, rfl⟩
    have htail := hF t htF
    have hsumEq :
        (∑ index ∈ u,
            if actualCarlsonOutsideClusterRealPart beta S index = beta then
              actualCarlsonOutsideClusterWeight S index
            else 0) =
          ∑ index ∈ t, actualCarlsonBoundaryTerm beta index := by
      dsimp [t]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro index hindex
      by_cases hmem : actualCarlsonPositiveZero index ∈ S
      · simp [actualCarlsonOutsideClusterWeight,
          actualCarlsonOutsideClusterRealPart,
          actualCarlsonBoundaryTerm, hmem]
      · simp [actualCarlsonOutsideClusterWeight,
          actualCarlsonOutsideClusterRealPart,
          actualCarlsonBoundaryTerm, hmem]
    rw [hsumEq]
    have hsumNonneg :
        0 ≤ ∑ index ∈ t, actualCarlsonBoundaryTerm beta index :=
      Finset.sum_nonneg fun index _ =>
        actualCarlsonBoundaryTerm_nonneg index
    have hsumLt :
        (∑ index ∈ t, actualCarlsonBoundaryTerm beta index) <
          epsilon / 2 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hsumNonneg] using htail
    exact hsumLt.le

/-- Conjugation closure preserves support on nontrivial zeta zeros. -/
theorem actualCarlsonConjugationClosure_isNontrivialZero
    {S : Finset ℂ}
    (hzero : ∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho)
    {rho : ℂ}
    (hrho : rho ∈ actualCarlsonConjugationClosure S) :
    RiemannHypothesis.IsNontrivialZero rho := by
  rcases Finset.mem_union.mp hrho with hrhoS | hrhoConj
  · exact hzero rho hrhoS
  · rcases Finset.mem_image.mp hrhoConj with ⟨z, hz, rfl⟩
    simpa using
      RiemannVonMangoldt.isNontrivialZero_conj (hzero z hz)

/-- Arbitrarily small outside boundary mass is achieved by a finite cluster
that is both conjugation-stable and supported on nontrivial zeta zeros. -/
theorem
    exists_conjugationStable_zeroSupported_actualCarlsonOutsideClusterBoundaryMass_lt
    {sigma beta epsilon : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hepsilon : 0 < epsilon) :
    ∃ S : Finset ℂ,
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      (∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho) ∧
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < epsilon := by
  obtain ⟨S, hzero, hmass⟩ :=
    exists_zeroSupported_actualCarlsonOutsideClusterBoundaryMass_lt
      hhalf hone hepsilon
  let T := actualCarlsonConjugationClosure S
  refine ⟨T, mem_actualCarlsonConjugationClosure_iff S, ?_, ?_⟩
  · intro rho hrho
    exact actualCarlsonConjugationClosure_isNontrivialZero hzero hrho
  · have hST : S ⊆ T := by
      intro rho hrho
      exact Finset.mem_union_left _ hrho
    exact
      (actualCarlsonOutsideClusterBoundaryMass_antitone
        hhalf hone hST).trans_lt hmass

/-- Every strict coefficient gap admits a conjugation-stable,
zero-supported finite Carlson capture. -/
theorem
    exists_conjugationStable_zeroSupported_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
    {sigma beta c q : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hqC : q < c) :
    ∃ S : Finset ℂ,
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      (∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q := by
  have hepsilon : 0 < (c - q) / 2 := by
    linarith
  obtain ⟨S, hstable, hzero, hmass⟩ :=
    exists_conjugationStable_zeroSupported_actualCarlsonOutsideClusterBoundaryMass_lt
      (beta := beta) hhalf hone hepsilon
  refine ⟨S, hstable, hzero, ?_⟩
  linarith

/-- Boundary filtering preserves support on nontrivial zeta zeros. -/
theorem actualCarlsonBoundaryClusterPart_isNontrivialZero
    {beta : ℝ} {S : Finset ℂ}
    (hzero : ∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho)
    {rho : ℂ}
    (hrho : rho ∈ actualCarlsonBoundaryClusterPart beta S) :
    RiemannHypothesis.IsNontrivialZero rho :=
  hzero rho (mem_actualCarlsonBoundaryClusterPart.mp hrho).1

/-- The finite capture can simultaneously retain conjugation stability,
zero support, boundary support, and the prescribed Carlson gap. -/
theorem
    exists_conjugationStable_zeroSupported_boundarySupported_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
    {sigma beta c q : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hqC : q < c) :
    ∃ S : Finset ℂ,
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      (∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho) ∧
      (∀ rho ∈ S, rho.re = beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q := by
  rcases
      exists_conjugationStable_zeroSupported_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
        (beta := beta) hhalf hone hqC with
    ⟨S, hstable, hzero, hgap⟩
  refine
    ⟨actualCarlsonBoundaryClusterPart beta S,
      actualCarlsonBoundaryClusterPart_conjugationStable hstable,
      ?_, ?_, ?_⟩
  · intro rho hrho
    exact actualCarlsonBoundaryClusterPart_isNontrivialZero hzero hrho
  · intro rho hrho
    exact actualCarlsonBoundaryClusterPart_realPart hrho
  · rw [actualCarlsonOutsideClusterBoundaryMass_boundaryClusterPart]
    exact hgap

end

end PrimeNumberTheorem
