import HardyTheorem.ConreyDegreeOneNontrivial
import MathlibAux.ArgumentCrossing

/-!
# Actual critical-line zero data for Conrey equation (41)

This module starts the specialization of the abstract global argument
partition to Conrey's actual degree-one auxiliary function.  The divisor of
`eta` on a compact critical-line segment supplies a finite zero family
directly, without introducing mollifier parameters.
-/

open Complex Set Filter
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

/-- Actual critical-line eta-zero ordinates in `(U,T]`.  Conrey equation (41)
uses the specialization `U = 2`. -/
noncomputable def conreyEtaCriticalZeroOrdinatesBetween
    (g g0 g1 L U T : ℝ) : Finset ℝ :=
  (conreyEtaCriticalZeroOrdinates g g0 g1 L T).filter fun t => U < t

/-- Exact membership in the actual eta-zero ordinate set on `(U,T]`, for a
nonnegative lower endpoint. -/
theorem mem_conreyEtaCriticalZeroOrdinatesBetween
    {g g0 g1 L U T t : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U) :
    t ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T ↔
      U < t ∧ t ≤ T ∧
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) = 0 := by
  classical
  rw [conreyEtaCriticalZeroOrdinatesBetween, Finset.mem_filter,
    mem_conreyEtaCriticalZeroOrdinates hg]
  constructor
  · rintro ⟨⟨_ht0, htT, heta⟩, hUt⟩
    exact ⟨hUt, htT, heta⟩
  · rintro ⟨hUt, htT, heta⟩
    exact ⟨⟨lt_of_le_of_lt hU hUt, htT, heta⟩, hUt⟩

/-- The actual eta-zero ordinates in `(U,T]`, in increasing order. -/
noncomputable def conreyEtaCriticalZeroOrdinatesSortedBetween
    (g g0 g1 L U T : ℝ) : List ℝ :=
  (conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T).sort

@[simp]
theorem mem_conreyEtaCriticalZeroOrdinatesSortedBetween
    {g g0 g1 L U T t : ℝ} :
    t ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T ↔
      t ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T := by
  unfold conreyEtaCriticalZeroOrdinatesSortedBetween
  exact Finset.mem_sort (s :=
    conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T) (· ≤ ·)

theorem pairwise_lt_conreyEtaCriticalZeroOrdinatesSortedBetween
    (g g0 g1 L U T : ℝ) :
    (conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T).Pairwise
      (· < ·) := by
  unfold conreyEtaCriticalZeroOrdinatesSortedBetween
  exact (Finset.sortedLT_sort
    (conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T)).pairwise

/-- The exact multiplicity loss `N_{0,eta}(U,T)` used by the phase bridges in
equation (41).  Multiple zeros are charged by their analytic order. -/
noncomputable def conreyEtaCriticalZeroMultiplicityMassBetween
    (g g0 g1 L U T : ℝ) : ℕ :=
  ∑ t ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T,
    analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L)
      (conreyCriticalPoint t)

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

/-- Every zero in the equation-(41) interval `(U,T]` has positive bridge
multiplicity. -/
theorem conreyEtaCriticalZeroOrderNat_pos_of_mem_sortedBetween
    {g g0 g1 L U T t : ℝ} (hg : g ≠ 0)
    (ht : t ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T) :
    0 < analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L)
      (conreyCriticalPoint t) := by
  have htBetween :
      t ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T :=
    mem_conreyEtaCriticalZeroOrdinatesSortedBetween.mp ht
  have htGlobal : t ∈ conreyEtaCriticalZeroOrdinates g g0 g1 L T :=
    (Finset.mem_filter.mp htBetween).1
  exact conreyEtaCriticalZeroOrderNat_pos hg
    (mem_conreyEtaCriticalZeroOrdinatesSorted.mpr htGlobal)

/-- Consecutive zeros in the actual equation-(41) interval `(U,T]` bound a
zero-free open component of the eta restriction. -/
theorem conreyDegreeOneEta_ne_zero_between_consecutiveCriticalZeroOrdinatesBetween
    {g g0 g1 L U T a b t : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U)
    (ha : a ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hb : b ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hgap : ∀ u ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T,
      ¬ (a < u ∧ u < b))
    (ht : t ∈ Set.Ioo a b) :
    conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 := by
  intro hzero
  have haBetween :
      a ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T :=
    mem_conreyEtaCriticalZeroOrdinatesSortedBetween.mp ha
  have hbBetween :
      b ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T :=
    mem_conreyEtaCriticalZeroOrdinatesSortedBetween.mp hb
  have haData :=
    (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mp haBetween
  have hbData :=
    (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mp hbBetween
  have htBetween :
      t ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T :=
    (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mpr
      ⟨lt_trans haData.1 ht.1, le_trans ht.2.le hbData.2.1, hzero⟩
  exact hgap t
    (mem_conreyEtaCriticalZeroOrdinatesSortedBetween.mpr htBetween) ht

/-- The actual eta restriction has one continuous logarithm on every open
component between consecutive equation-(41) zero ordinates. -/
theorem exists_conreyDegreeOneEta_continuousLog_between_consecutiveCriticalZeroOrdinatesBetween
    {g g0 g1 L U T a b : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U) (hab : a < b)
    (ha : a ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hb : b ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hgap : ∀ u ∈ conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T,
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
      conreyDegreeOneEta_ne_zero_between_consecutiveCriticalZeroOrdinatesBetween
        hg hU ha hb hgap ht
  exact MathlibAux.exists_continuousLogOn_Ioo hab hetaContinuous hetaNe

/-- A nonzero value of the actual eta restriction remains nonzero on a real
open neighborhood of that ordinate. -/
theorem exists_conreyDegreeOneEta_nonzero_real_neighborhood
    {g g0 g1 L u : ℝ}
    (hu : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint u) ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t ∈ Set.Ioo (u - delta) (u + delta),
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 := by
  have hcriticalContinuous : Continuous conreyCriticalPoint := by
    unfold conreyCriticalPoint
    fun_prop
  have hetaContinuousAt :
      ContinuousAt
        (fun t => conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) u :=
    (analyticAt_conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint u)).continuousAt.comp
        hcriticalContinuous.continuousAt
  have hneEventually :
      ∀ᶠ t in nhds u,
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 :=
    hetaContinuousAt.eventually_ne hu
  rcases Metric.mem_nhds_iff.mp hneEventually with
    ⟨delta, hdelta, hball⟩
  refine ⟨delta, hdelta, fun t ht => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- If eta is nonzero at the lower endpoint `U`, the component from `U` to
the first zero in `(U,T]` admits one logarithm on an open interval containing
`U` and extending all the way to that zero. -/
theorem exists_conreyDegreeOneEta_continuousLog_lowerEndpoint_to_firstZero
    {g g0 g1 L U T tau : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U)
    (hUeta : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint U) ≠ 0)
    (htau : tau ∈
      conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hfirst : ∀ u ∈
      conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T,
      tau ≤ u) :
    ∃ delta : ℝ, ∃ ell : ℝ → ℂ,
      0 < delta ∧ U ∈ Set.Ioo (U - delta) tau ∧
      ContinuousOn ell (Set.Ioo (U - delta) tau) ∧
      ∀ t ∈ Set.Ioo (U - delta) tau,
        Complex.exp (ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) := by
  rcases exists_conreyDegreeOneEta_nonzero_real_neighborhood hUeta with
    ⟨delta, hdelta, hlocal⟩
  have htauBetween :
      tau ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T :=
    mem_conreyEtaCriticalZeroOrdinatesSortedBetween.mp htau
  have htauData :=
    (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mp htauBetween
  have hetaNe : ∀ t ∈ Set.Ioo (U - delta) tau,
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 := by
    intro t ht
    rcases lt_trichotomy t U with htU | rfl | hUt
    · exact hlocal t ⟨ht.1, by linarith⟩
    · exact hUeta
    · intro hzero
      have htBetween :
          t ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T :=
        (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mpr
          ⟨hUt, le_trans ht.2.le htauData.2.1, hzero⟩
      have htList : t ∈
          conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T :=
        mem_conreyEtaCriticalZeroOrdinatesSortedBetween.mpr htBetween
      exact (not_le_of_gt ht.2) (hfirst t htList)
  have hcriticalContinuous : Continuous conreyCriticalPoint := by
    unfold conreyCriticalPoint
    fun_prop
  have hetaContinuous :
      ContinuousOn
        (fun t => conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t))
        (Set.Ioo (U - delta) tau) := by
    intro t _ht
    exact ((analyticAt_conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint t)).continuousAt.comp
        hcriticalContinuous.continuousAt).continuousWithinAt
  have hdomain : U - delta < tau := by linarith [htauData.1]
  rcases MathlibAux.exists_continuousLogOn_Ioo
      hdomain hetaContinuous hetaNe with ⟨ell, hellContinuous, hellExp⟩
  exact ⟨delta, ell, hdelta, ⟨by linarith, htauData.1⟩,
    hellContinuous, hellExp⟩

/-- If eta is nonzero at the upper endpoint `T`, the component from the last
zero in `(U,T]` to `T` admits one logarithm on an open interval beginning at
that zero and containing `T`. -/
theorem exists_conreyDegreeOneEta_continuousLog_lastZero_to_upperEndpoint
    {g g0 g1 L U T tau : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U)
    (hTeta : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint T) ≠ 0)
    (htau : tau ∈
      conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T)
    (hlast : ∀ u ∈
      conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T,
      u ≤ tau) :
    ∃ delta : ℝ, ∃ ell : ℝ → ℂ,
      0 < delta ∧ T ∈ Set.Ioo tau (T + delta) ∧
      ContinuousOn ell (Set.Ioo tau (T + delta)) ∧
      ∀ t ∈ Set.Ioo tau (T + delta),
        Complex.exp (ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) := by
  rcases exists_conreyDegreeOneEta_nonzero_real_neighborhood hTeta with
    ⟨delta, hdelta, hlocal⟩
  have htauBetween :
      tau ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T :=
    mem_conreyEtaCriticalZeroOrdinatesSortedBetween.mp htau
  have htauData :=
    (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mp htauBetween
  have htauNeT : tau ≠ T := by
    intro htauT
    apply hTeta
    rw [← htauT]
    exact htauData.2.2
  have htauT : tau < T := lt_of_le_of_ne htauData.2.1 htauNeT
  have hetaNe : ∀ t ∈ Set.Ioo tau (T + delta),
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 := by
    intro t ht
    rcases lt_trichotomy t T with htT | rfl | hTt
    · intro hzero
      have htBetween :
          t ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T :=
        (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mpr
          ⟨lt_trans htauData.1 ht.1, htT.le, hzero⟩
      have htList : t ∈
          conreyEtaCriticalZeroOrdinatesSortedBetween g g0 g1 L U T :=
        mem_conreyEtaCriticalZeroOrdinatesSortedBetween.mpr htBetween
      exact (not_le_of_gt ht.1) (hlast t htList)
    · exact hTeta
    · exact hlocal t ⟨by linarith, ht.2⟩
  have hcriticalContinuous : Continuous conreyCriticalPoint := by
    unfold conreyCriticalPoint
    fun_prop
  have hetaContinuous :
      ContinuousOn
        (fun t => conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t))
        (Set.Ioo tau (T + delta)) := by
    intro t _ht
    exact ((analyticAt_conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint t)).continuousAt.comp
        hcriticalContinuous.continuousAt).continuousWithinAt
  have hdomain : tau < T + delta := by linarith
  rcases MathlibAux.exists_continuousLogOn_Ioo
      hdomain hetaContinuous hetaNe with ⟨ell, hellContinuous, hellExp⟩
  exact ⟨delta, ell, hdelta, ⟨htauT, by linarith⟩,
    hellContinuous, hellExp⟩

/-- If the equation-(41) interval contains no eta zero and both endpoint
values are nonzero, the whole interval is one zero-free logarithm component.
The logarithm domain is open and contains both endpoints. -/
theorem exists_conreyDegreeOneEta_continuousLog_of_zeroInterval_empty
    {g g0 g1 L U T : ℝ} (hg : g ≠ 0) (hU : 0 ≤ U) (hUT : U ≤ T)
    (hUeta : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint U) ≠ 0)
    (hTeta : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint T) ≠ 0)
    (hEmpty : conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T = ∅) :
    ∃ deltaU deltaT : ℝ, ∃ ell : ℝ → ℂ,
      0 < deltaU ∧ 0 < deltaT ∧
      U ∈ Set.Ioo (U - deltaU) (T + deltaT) ∧
      T ∈ Set.Ioo (U - deltaU) (T + deltaT) ∧
      ContinuousOn ell (Set.Ioo (U - deltaU) (T + deltaT)) ∧
      ∀ t ∈ Set.Ioo (U - deltaU) (T + deltaT),
        Complex.exp (ell t) =
          conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) := by
  rcases exists_conreyDegreeOneEta_nonzero_real_neighborhood hUeta with
    ⟨deltaU, hdeltaU, hlocalU⟩
  rcases exists_conreyDegreeOneEta_nonzero_real_neighborhood hTeta with
    ⟨deltaT, hdeltaT, hlocalT⟩
  have hetaNe : ∀ t ∈ Set.Ioo (U - deltaU) (T + deltaT),
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0 := by
    intro t ht
    rcases lt_trichotomy t U with htU | rfl | hUt
    · exact hlocalU t ⟨ht.1, by linarith⟩
    · exact hUeta
    · rcases lt_trichotomy t T with htT | rfl | hTt
      · intro hzero
        have htBetween :
            t ∈ conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T :=
          (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mpr
            ⟨hUt, htT.le, hzero⟩
        rw [hEmpty] at htBetween
        simp at htBetween
      · exact hTeta
      · exact hlocalT t ⟨by linarith, ht.2⟩
  have hcriticalContinuous : Continuous conreyCriticalPoint := by
    unfold conreyCriticalPoint
    fun_prop
  have hetaContinuous :
      ContinuousOn
        (fun t => conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t))
        (Set.Ioo (U - deltaU) (T + deltaT)) := by
    intro t _ht
    exact ((analyticAt_conreyDegreeOneEta g g0 g1 L
      (conreyCriticalPoint t)).continuousAt.comp
        hcriticalContinuous.continuousAt).continuousWithinAt
  have hdomain : U - deltaU < T + deltaT := by linarith
  rcases MathlibAux.exists_continuousLogOn_Ioo
      hdomain hetaContinuous hetaNe with ⟨ell, hellContinuous, hellExp⟩
  exact ⟨deltaU, deltaT, ell, hdeltaU, hdeltaT,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    hellContinuous, hellExp⟩

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
