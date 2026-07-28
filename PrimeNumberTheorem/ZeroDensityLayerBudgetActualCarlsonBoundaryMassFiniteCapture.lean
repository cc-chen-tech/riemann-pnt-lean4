import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassClusterCapture
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Finite capture of Carlson boundary mass

The full multiplicity-weighted Carlson boundary layer is summable.  Hence a
finite set of indexed zeros captures all but an arbitrarily small amount of
its coefficient mass.  Mapping that finite index set to actual zeros and then
closing under conjugation produces the finite, conjugation-stable cluster
required by the PNT transfer theorems.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

noncomputable section

/-- The full positive-zero coefficient term on `Re rho = beta`, before any
visible cluster is removed. -/
def actualCarlsonBoundaryTerm
    {sigma : ℝ} (beta : ℝ)
    (index : ActualCarlsonPositiveZeroIndex sigma) : ℝ :=
  if actualCarlsonPositiveZeroRealPart index = beta then
    actualCarlsonPositiveZeroWeight index
  else 0

theorem actualCarlsonBoundaryTerm_nonneg
    {sigma beta : ℝ}
    (index : ActualCarlsonPositiveZeroIndex sigma) :
    0 ≤ actualCarlsonBoundaryTerm beta index := by
  by_cases heq : actualCarlsonPositiveZeroRealPart index = beta
  · simp [actualCarlsonBoundaryTerm, heq,
      actualCarlsonPositiveZeroWeight_nonneg index]
  · simp [actualCarlsonBoundaryTerm, heq]

/-- Carlson summability of all positive-zero weights implies summability of
the coefficient mass restricted to the target boundary line. -/
theorem summable_actualCarlsonBoundaryTerm
    {sigma beta : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable (@actualCarlsonBoundaryTerm sigma beta) := by
  refine Summable.of_nonneg_of_le actualCarlsonBoundaryTerm_nonneg ?_
    (summable_actualCarlsonPositiveZeroWeight hhalf hone)
  intro index
  by_cases heq : actualCarlsonPositiveZeroRealPart index = beta
  · simp [actualCarlsonBoundaryTerm, heq]
  · simp [actualCarlsonBoundaryTerm, heq,
      actualCarlsonPositiveZeroWeight_nonneg index]

/-- The finite set of actual zeros represented by a finite set of Carlson
positive-zero indices. -/
def actualCarlsonBoundaryCaptureFinset
    {sigma : ℝ} (F : Finset (ActualCarlsonPositiveZeroIndex sigma)) :
    Finset ℂ :=
  F.image actualCarlsonPositiveZero

/-- A finite visible cluster makes the outside boundary mass smaller than any
prescribed positive tolerance. -/
theorem exists_actualCarlsonOutsideClusterBoundaryMass_lt
    {sigma beta epsilon : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hepsilon : 0 < epsilon) :
    ∃ S : Finset ℂ,
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
  refine ⟨S, ?_⟩
  unfold actualCarlsonOutsideClusterBoundaryMass weightedPowerBoundaryMass
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
    exact
      Finset.mem_image.mpr
        ⟨index, hindexF, rfl⟩
  have htail :=
    hF t htF
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
        actualCarlsonOutsideClusterRealPart, actualCarlsonBoundaryTerm, hmem]
    · simp [actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart, actualCarlsonBoundaryTerm, hmem]
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

/-- Conjugation closure of a finite complex cluster. -/
def actualCarlsonConjugationClosure (S : Finset ℂ) : Finset ℂ :=
  S ∪ S.image (starRingEnd ℂ)

theorem mem_actualCarlsonConjugationClosure_iff
    (S : Finset ℂ) (rho : ℂ) :
    rho ∈ actualCarlsonConjugationClosure S ↔
      (starRingEnd ℂ) rho ∈ actualCarlsonConjugationClosure S := by
  classical
  constructor
  · intro hrho
    rcases Finset.mem_union.mp hrho with hrhoS | hrhoImage
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨rho, hrhoS, rfl⟩
    · rcases Finset.mem_image.mp hrhoImage with ⟨z, hzS, hzr⟩
      apply Finset.mem_union_left
      have hz : z = (starRingEnd ℂ) rho := by
        apply_fun (starRingEnd ℂ) at hzr
        simpa using hzr
      exact hz ▸ hzS
  · intro hrho
    rcases Finset.mem_union.mp hrho with hrhoS | hrhoImage
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨(starRingEnd ℂ) rho, hrhoS, ?_⟩
      simp
    · rcases Finset.mem_image.mp hrhoImage with ⟨z, hzS, hzr⟩
      apply Finset.mem_union_left
      have hz : z = rho := by
        apply_fun (starRingEnd ℂ) at hzr
        simpa using hzr
      exact hz ▸ hzS

/-- The arbitrarily small outside boundary mass can be achieved by a finite
cluster already closed under complex conjugation. -/
theorem exists_conjugationStable_actualCarlsonOutsideClusterBoundaryMass_lt
    {sigma beta epsilon : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hepsilon : 0 < epsilon) :
    ∃ S : Finset ℂ,
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < epsilon := by
  obtain ⟨S, hmass⟩ :=
    exists_actualCarlsonOutsideClusterBoundaryMass_lt
      hhalf hone hepsilon
  let T := actualCarlsonConjugationClosure S
  refine ⟨T, ?_, ?_⟩
  · exact mem_actualCarlsonConjugationClosure_iff S
  · have hST : S ⊆ T := by
      intro rho hrho
      exact Finset.mem_union_left _ hrho
    exact
      (actualCarlsonOutsideClusterBoundaryMass_antitone
        hhalf hone hST).trans_lt hmass

end

end PrimeNumberTheorem
