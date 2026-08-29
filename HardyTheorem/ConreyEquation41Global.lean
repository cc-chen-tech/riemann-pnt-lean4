import HardyTheorem.ConreyDegreeOneNontrivial
import MathlibAux.ArgumentCrossing

/-!
# Actual critical-line zero data for Conrey equation (41)

This module starts the specialization of the abstract global argument
partition to Conrey's actual degree-one auxiliary function.  The divisor of
`eta` on a compact critical-line segment supplies a finite zero family
directly, without introducing mollifier parameters.
-/

open Complex Set
open scoped BigOperators

namespace HardyTheorem

/-- The compact critical-line segment with ordinates in `[0,T]`. -/
def conreyCriticalLineSegment (T : ℝ) : Set ℂ :=
  Set.Icc (1 / 2 : ℝ) (1 / 2) ×ℂ Set.Icc 0 T

theorem isCompact_conreyCriticalLineSegment (T : ℝ) :
    IsCompact (conreyCriticalLineSegment T) := by
  unfold conreyCriticalLineSegment
  exact isCompact_Icc.reProdIm isCompact_Icc

@[simp]
theorem mem_conreyCriticalLineSegment {T : ℝ} {s : ℂ} :
    s ∈ conreyCriticalLineSegment T ↔
      s.re = 1 / 2 ∧ 0 ≤ s.im ∧ s.im ≤ T := by
  rw [conreyCriticalLineSegment, mem_reProdIm]
  constructor
  · rintro ⟨hsre, hsim⟩
    exact ⟨le_antisymm hsre.2 hsre.1, hsim⟩
  · rintro ⟨hsre, hsim⟩
    rw [hsre]
    exact ⟨⟨le_rfl, le_rfl⟩, hsim⟩

/-- Positive zeros of the actual degree-one `eta` on the compact critical-line
segment. -/
noncomputable def conreyEtaCriticalZeros
    (g g0 g1 L T : ℝ) : Finset ℂ :=
  let K := conreyCriticalLineSegment T
  let D := MeromorphicOn.divisor (conreyDegreeOneEta g g0 g1 L) K
  ((D.finiteSupport (isCompact_conreyCriticalLineSegment T)).toFinset).filter
    fun s => 0 < s.im

/-- Exact complex membership in the actual critical-line eta-zero finset. -/
theorem mem_conreyEtaCriticalZeros
    {g g0 g1 L T : ℝ} (hg : g ≠ 0) {s : ℂ} :
    s ∈ conreyEtaCriticalZeros g g0 g1 L T ↔
      s.re = 1 / 2 ∧ 0 < s.im ∧ s.im ≤ T ∧
        conreyDegreeOneEta g g0 g1 L s = 0 := by
  classical
  let K := conreyCriticalLineSegment T
  let f := conreyDegreeOneEta g g0 g1 L
  let D := MeromorphicOn.divisor f K
  have han : AnalyticOnNhd ℂ f K := by
    intro z hz
    exact analyticOnNhd_conreyDegreeOneEta g g0 g1 L z (by simp)
  have hnotop : ∀ u : K, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(han u u.property).meromorphicOrderAt_eq]
    intro htop
    exact analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero hg u
      (ENat.map_eq_top_iff.mp htop)
  have hzeroSupport := han.meromorphicNFOn.zero_set_eq_divisor_support hnotop
  have hzeroSupportD : K ∩ f ⁻¹' {0} = D.support := by
    simpa [D] using hzeroSupport
  have hfinite : D.support.Finite :=
    D.finiteSupport (isCompact_conreyCriticalLineSegment T)
  change s ∈ hfinite.toFinset.filter (fun z => 0 < z.im) ↔ _
  rw [Finset.mem_filter, hfinite.mem_toFinset, ← hzeroSupportD]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hsK, hzero⟩, hsim⟩
    have hsdata := mem_conreyCriticalLineSegment.mp hsK
    exact ⟨hsdata.1, hsim, hsdata.2.2, hzero⟩
  · rintro ⟨hsre, hsim, hsimT, hzero⟩
    exact ⟨⟨mem_conreyCriticalLineSegment.mpr
      ⟨hsre, hsim.le, hsimT⟩, hzero⟩, hsim⟩

/-- Positive critical-line ordinates up to `T` where Conrey's actual
degree-one `eta` vanishes. -/
noncomputable def conreyEtaCriticalZeroOrdinates
    (g g0 g1 L T : ℝ) : Finset ℝ :=
  (conreyEtaCriticalZeros g g0 g1 L T).image fun s => s.im

/-- Exact membership in the actual finite critical-line eta-zero ordinate
set. -/
theorem mem_conreyEtaCriticalZeroOrdinates
    {g g0 g1 L T t : ℝ} (hg : g ≠ 0) :
    t ∈ conreyEtaCriticalZeroOrdinates g g0 g1 L T ↔
      0 < t ∧ t ≤ T ∧
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) = 0 := by
  classical
  simp only [conreyEtaCriticalZeroOrdinates, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hsdata := (mem_conreyEtaCriticalZeros hg).mp hs
    have hsEq : s = conreyCriticalPoint s.im := by
      apply Complex.ext
      · simpa using hsdata.1
      · simp
    refine ⟨hsdata.2.1, hsdata.2.2.1, ?_⟩
    rw [← hsEq]
    exact hsdata.2.2.2
  · rintro ⟨ht0, htT, heta⟩
    refine ⟨conreyCriticalPoint t, ?_, by simp⟩
    apply (mem_conreyEtaCriticalZeros hg).mpr
    refine ⟨by simp, ?_, ?_, heta⟩
    · simpa
    · simpa

end HardyTheorem
