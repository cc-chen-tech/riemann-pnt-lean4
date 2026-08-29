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

/-- The actual positive critical-line eta-zero ordinates in increasing order. -/
noncomputable def conreyEtaCriticalZeroOrdinatesSorted
    (g g0 g1 L T : ℝ) : List ℝ :=
  (conreyEtaCriticalZeroOrdinates g g0 g1 L T).sort

@[simp]
theorem length_conreyEtaCriticalZeroOrdinatesSorted
    (g g0 g1 L T : ℝ) :
    (conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T).length =
      (conreyEtaCriticalZeroOrdinates g g0 g1 L T).card := by
  unfold conreyEtaCriticalZeroOrdinatesSorted
  exact Finset.length_sort (s :=
    conreyEtaCriticalZeroOrdinates g g0 g1 L T) (· ≤ ·)

@[simp]
theorem mem_conreyEtaCriticalZeroOrdinatesSorted
    {g g0 g1 L T t : ℝ} :
    t ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T ↔
      t ∈ conreyEtaCriticalZeroOrdinates g g0 g1 L T := by
  unfold conreyEtaCriticalZeroOrdinatesSorted
  exact Finset.mem_sort (s :=
    conreyEtaCriticalZeroOrdinates g g0 g1 L T) (· ≤ ·)

theorem pairwise_lt_conreyEtaCriticalZeroOrdinatesSorted
    (g g0 g1 L T : ℝ) :
    (conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T).Pairwise (· < ·) := by
  unfold conreyEtaCriticalZeroOrdinatesSorted
  exact (Finset.sortedLT_sort
    (conreyEtaCriticalZeroOrdinates g g0 g1 L T)).pairwise

/-- Every ordinate in the actual sorted eta-zero list has finite analytic
order. -/
theorem conreyEtaCriticalZeroOrder_ne_top
    {g g0 g1 L T t : ℝ} (hg : g ≠ 0)
    (_ht : t ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T) :
    analyticOrderAt (conreyDegreeOneEta g g0 g1 L)
      (conreyCriticalPoint t) ≠ ⊤ :=
  analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero hg _

/-- Every ordinate in the actual sorted eta-zero list has a positive natural
analytic order.  This is its positive finite bridge multiplicity. -/
theorem conreyEtaCriticalZeroOrderNat_pos
    {g g0 g1 L T t : ℝ} (hg : g ≠ 0)
    (ht : t ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T) :
    0 < analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L)
      (conreyCriticalPoint t) := by
  have htFinset : t ∈ conreyEtaCriticalZeroOrdinates g g0 g1 L T :=
    mem_conreyEtaCriticalZeroOrdinatesSorted.mp ht
  have hzero := (mem_conreyEtaCriticalZeroOrdinates hg).mp htFinset |>.2.2
  have hanalytic :
      AnalyticAt ℂ (conreyDegreeOneEta g g0 g1 L)
        (conreyCriticalPoint t) :=
    analyticOnNhd_conreyDegreeOneEta g g0 g1 L _ (by simp)
  have horderNeZero :
      analyticOrderAt (conreyDegreeOneEta g g0 g1 L)
        (conreyCriticalPoint t) ≠ 0 :=
    hanalytic.analyticOrderAt_ne_zero.mpr hzero
  have hfinite := conreyEtaCriticalZeroOrder_ne_top hg ht
  apply Nat.pos_of_ne_zero
  intro hnatZero
  apply horderNeZero
  rw [← Nat.cast_analyticOrderNatAt hfinite, hnatZero]
  simp

/-- If no listed critical-line eta zero lies strictly between two listed
ordinates, then the actual eta restriction is nonzero throughout that open
interval. -/
theorem conreyDegreeOneEta_ne_zero_between_consecutiveCriticalZeroOrdinates
    {g g0 g1 L T a b t : ℝ} (hg : g ≠ 0)
    (ha : a ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T)
    (hb : b ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T)
    (hgap : ∀ u ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T,
      ¬ (a < u ∧ u < b))
    (ht : t ∈ Set.Ioo a b) :
    conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 := by
  intro hzero
  have haFinset : a ∈ conreyEtaCriticalZeroOrdinates g g0 g1 L T :=
    mem_conreyEtaCriticalZeroOrdinatesSorted.mp ha
  have hbFinset : b ∈ conreyEtaCriticalZeroOrdinates g g0 g1 L T :=
    mem_conreyEtaCriticalZeroOrdinatesSorted.mp hb
  have haData := (mem_conreyEtaCriticalZeroOrdinates hg).mp haFinset
  have hbData := (mem_conreyEtaCriticalZeroOrdinates hg).mp hbFinset
  have htFinset : t ∈ conreyEtaCriticalZeroOrdinates g g0 g1 L T :=
    (mem_conreyEtaCriticalZeroOrdinates hg).mpr
      ⟨lt_trans haData.1 ht.1, le_trans ht.2.le hbData.2.1, hzero⟩
  exact hgap t (mem_conreyEtaCriticalZeroOrdinatesSorted.mpr htFinset) ht

/-- On every open component between consecutive actual critical-line eta
zeros, the eta restriction has a continuous logarithm on the whole component.
This is the component argument lift needed by equation (41). -/
theorem exists_conreyDegreeOneEta_continuousLog_between_consecutiveCriticalZeroOrdinates
    {g g0 g1 L T a b : ℝ} (hg : g ≠ 0) (hab : a < b)
    (ha : a ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T)
    (hb : b ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T)
    (hgap : ∀ u ∈ conreyEtaCriticalZeroOrdinatesSorted g g0 g1 L T,
      ¬ (a < u ∧ u < b)) :
    ∃ ell : ℝ → ℂ,
      ContinuousOn ell (Set.Ioo a b) ∧
      ∀ t ∈ Set.Ioo a b,
        Complex.exp (ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) := by
  have hcriticalContinuous : Continuous conreyCriticalPoint := by
    unfold conreyCriticalPoint
    fun_prop
  have hetaContinuous :
      ContinuousOn
        (fun t => conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t))
        (Set.Ioo a b) := by
    intro t _ht
    exact ((analyticAt_conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint t)).continuousAt.comp
        hcriticalContinuous.continuousAt).continuousWithinAt
  have hetaNe : ∀ t ∈ Set.Ioo a b,
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 :=
    fun t ht =>
      conreyDegreeOneEta_ne_zero_between_consecutiveCriticalZeroOrdinates
        hg ha hb hgap ht
  exact MathlibAux.exists_continuousLogOn_Ioo hab hetaContinuous hetaNe

end HardyTheorem
