import HardyTheorem.ConreyMollifierProduct
import MathlibAux.HalfWeightedMultiplicity

/-!
# Finite-rectangle form of Conrey's equation (35)

This file lifts the local zero-multiplicity inclusion for `V1 * B` to the
half-weighted zero count on a bounded right-half rectangle.  To cross the
apparent pole at `s = 1` without inserting an artificial positive lower
height, the finite zero families are represented by the entire functions
`eta` and `eta * B`.  At positive height the nonvanishing factor `H` identifies
these zeros, including multiplicity, with the actual `V1` and `V1 * B` zeros.
-/

open Complex Set
open scoped BigOperators

namespace HardyTheorem

/-- Closed rectangle `[1/2,A] x [0,T]` whose positive-height part is the
bounded approximation to Conrey's equation-(35) half-strip. -/
def conreyClosedZeroRectangle (A T : ℝ) : Set ℂ :=
  Set.Icc (1 / 2 : ℝ) A ×ℂ Set.Icc 0 T

theorem isCompact_conreyClosedZeroRectangle (A T : ℝ) :
    IsCompact (conreyClosedZeroRectangle A T) := by
  simpa [conreyClosedZeroRectangle] using
    (isCompact_Icc.reProdIm isCompact_Icc)

/-- Entire regularization of the actual mollified factor `V1 * B`. -/
noncomputable def conreyRegularizedMollifiedDegreeOneV1
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (s : ℂ) : ℂ :=
  conreyDegreeOneEta g g0 g1 L s * conreyMollifier Y sigma0 P s

theorem analyticOnNhd_conreyRegularizedMollifiedDegreeOneV1
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) :
    AnalyticOnNhd ℂ
      (conreyRegularizedMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P)
      Set.univ := by
  unfold conreyRegularizedMollifiedDegreeOneV1
  exact (analyticOnNhd_conreyDegreeOneEta g g0 g1 L).mul
    (analyticOnNhd_conreyMollifier Y sigma0 P)

/-- The entire regularization differs from the paper's actual product by the
nonvanishing archimedean factor `H` on `Re s > 0`, `s != 1`. -/
theorem conreyRegularizedMollifiedDegreeOneV1_eq_conreyH_mul_mollified
    {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    conreyRegularizedMollifiedDegreeOneV1
        g g0 g1 L Y sigma0 P s =
      conreyH s *
        conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s := by
  unfold conreyRegularizedMollifiedDegreeOneV1
  rw [conreyDegreeOneEta_eq_conreyH_mul_conreyDegreeOneV1_of_re_pos_of_ne_one
    hs0 hs1]
  unfold conreyMollifiedDegreeOneV1
  ring

theorem conreyRegularizedMollifiedDegreeOneV1_eq_zero_iff_mollified_eq_zero
    {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    conreyRegularizedMollifiedDegreeOneV1
        g g0 g1 L Y sigma0 P s = 0 ↔
      conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s = 0 := by
  rw [conreyRegularizedMollifiedDegreeOneV1_eq_conreyH_mul_mollified
    hs0 hs1, mul_eq_zero]
  exact or_iff_right (conreyH_ne_zero_of_re_pos_of_ne_one hs0 hs1)

theorem analyticOrderAt_conreyRegularizedMollifiedDegreeOneV1_ne_top
    {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) (s : ℂ) :
    analyticOrderAt
        (conreyRegularizedMollifiedDegreeOneV1
          g g0 g1 L Y sigma0 P) s ≠ ⊤ := by
  have heta := analyticOnNhd_conreyDegreeOneEta g g0 g1 L s (by simp)
  have hB := analyticOnNhd_conreyMollifier Y sigma0 P s (by simp)
  have hetaFinite :=
    analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero
      (g0 := g0) (g1 := g1) (L := L) hg s
  have hBFinite := analyticOrderAt_conreyMollifier_ne_top hY hP1 sigma0 s
  unfold conreyRegularizedMollifiedDegreeOneV1
  change analyticOrderAt
    (conreyDegreeOneEta g g0 g1 L * conreyMollifier Y sigma0 P) s ≠ ⊤
  rw [analyticOrderAt_mul heta hB]
  intro htop
  rw [ENat.add_eq_top] at htop
  exact htop.elim hetaFinite hBFinite

/-- Positive-height divisor support of `eta` in the closed rectangle.  Under
`g != 0` this is exactly the bounded positive-height zero family of `V1`. -/
noncomputable def conreyV1BoundedZeros
    (g g0 g1 L A T : ℝ) : Finset ℂ :=
  let K := conreyClosedZeroRectangle A T
  let D := MeromorphicOn.divisor (conreyDegreeOneEta g g0 g1 L) K
  ((D.finiteSupport (isCompact_conreyClosedZeroRectangle A T)).toFinset).filter
    fun s => 0 < s.im

/-- Positive-height divisor support of `eta * B` in the closed rectangle.
Under the normalization hypotheses this is exactly the bounded zero family
of the actual product `V1 * B`. -/
noncomputable def conreyMollifiedV1BoundedZeros
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (A T : ℝ) : Finset ℂ :=
  let K := conreyClosedZeroRectangle A T
  let F := conreyRegularizedMollifiedDegreeOneV1
    g g0 g1 L Y sigma0 P
  let D := MeromorphicOn.divisor F K
  ((D.finiteSupport (isCompact_conreyClosedZeroRectangle A T)).toFinset).filter
    fun s => 0 < s.im

theorem mem_conreyV1BoundedZeros
    {g g0 g1 L A T : ℝ} (hg : g ≠ 0) {s : ℂ} :
    s ∈ conreyV1BoundedZeros g g0 g1 L A T ↔
      1 / 2 ≤ s.re ∧ s.re ≤ A ∧
        0 < s.im ∧ s.im ≤ T ∧
          conreyDegreeOneV1 g g0 g1 L s = 0 := by
  classical
  let K := conreyClosedZeroRectangle A T
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
    D.finiteSupport (isCompact_conreyClosedZeroRectangle A T)
  change s ∈ hfinite.toFinset.filter (fun z => 0 < z.im) ↔ _
  rw [Finset.mem_filter, hfinite.mem_toFinset, ← hzeroSupportD]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hsK, heta⟩, hsim⟩
    have hs0 : 0 < s.re := by
      have := hsK.1.1
      norm_num at this ⊢
      linarith
    have hs1 : s ≠ 1 := by
      intro hs
      have := congrArg Complex.im hs
      simp at this
      linarith
    have hV : conreyDegreeOneV1 g g0 g1 L s = 0 :=
      (conreyDegreeOneEta_eq_zero_iff_conreyDegreeOneV1_eq_zero_of_re_pos_of_ne_one
        hs0 hs1).mp heta
    exact ⟨hsK.1.1, hsK.1.2, hsim, hsK.2.2, hV⟩
  · rintro ⟨hsre0, hsreA, hsim0, hsimT, hV⟩
    have hs0 : 0 < s.re := by linarith
    have hs1 : s ≠ 1 := by
      intro hs
      have := congrArg Complex.im hs
      simp at this
      linarith
    have heta : f s = 0 := by
      exact (conreyDegreeOneEta_eq_zero_iff_conreyDegreeOneV1_eq_zero_of_re_pos_of_ne_one
        hs0 hs1).mpr hV
    have hsK : s ∈ K := by
      rw [show K = Set.Icc (1 / 2 : ℝ) A ×ℂ Set.Icc 0 T by
        rfl, mem_reProdIm]
      exact ⟨⟨hsre0, hsreA⟩, ⟨hsim0.le, hsimT⟩⟩
    exact ⟨⟨hsK, heta⟩, hsim0⟩

theorem mem_conreyMollifiedV1BoundedZeros
    {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) {s : ℂ} :
    s ∈ conreyMollifiedV1BoundedZeros
        g g0 g1 L Y sigma0 P A T ↔
      1 / 2 ≤ s.re ∧ s.re ≤ A ∧
        0 < s.im ∧ s.im ≤ T ∧
          conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s = 0 := by
  classical
  let K := conreyClosedZeroRectangle A T
  let f := conreyRegularizedMollifiedDegreeOneV1
    g g0 g1 L Y sigma0 P
  let D := MeromorphicOn.divisor f K
  have han : AnalyticOnNhd ℂ f K := by
    intro z hz
    exact analyticOnNhd_conreyRegularizedMollifiedDegreeOneV1
      g g0 g1 L Y sigma0 P z (by simp)
  have hnotop : ∀ u : K, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(han u u.property).meromorphicOrderAt_eq]
    intro htop
    exact analyticOrderAt_conreyRegularizedMollifiedDegreeOneV1_ne_top
      hg hY hP1 u (ENat.map_eq_top_iff.mp htop)
  have hzeroSupport := han.meromorphicNFOn.zero_set_eq_divisor_support hnotop
  have hzeroSupportD : K ∩ f ⁻¹' {0} = D.support := by
    simpa [D] using hzeroSupport
  have hfinite : D.support.Finite :=
    D.finiteSupport (isCompact_conreyClosedZeroRectangle A T)
  change s ∈ hfinite.toFinset.filter (fun z => 0 < z.im) ↔ _
  rw [Finset.mem_filter, hfinite.mem_toFinset, ← hzeroSupportD]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hsK, hfzero⟩, hsim⟩
    have hs0 : 0 < s.re := by linarith [hsK.1.1]
    have hs1 : s ≠ 1 := by
      intro hs
      have := congrArg Complex.im hs
      simp at this
      linarith
    have hproduct :=
      (conreyRegularizedMollifiedDegreeOneV1_eq_zero_iff_mollified_eq_zero
        hs0 hs1).mp hfzero
    exact ⟨hsK.1.1, hsK.1.2, hsim, hsK.2.2, hproduct⟩
  · rintro ⟨hsre0, hsreA, hsim0, hsimT, hproduct⟩
    have hs0 : 0 < s.re := by linarith
    have hs1 : s ≠ 1 := by
      intro hs
      have := congrArg Complex.im hs
      simp at this
      linarith
    have hfzero : f s = 0 :=
      (conreyRegularizedMollifiedDegreeOneV1_eq_zero_iff_mollified_eq_zero
        hs0 hs1).mpr hproduct
    have hsK : s ∈ K := by
      rw [show K = Set.Icc (1 / 2 : ℝ) A ×ℂ Set.Icc 0 T by
        rfl, mem_reProdIm]
      exact ⟨⟨hsre0, hsreA⟩, ⟨hsim0.le, hsimT⟩⟩
    exact ⟨⟨hsK, hfzero⟩, hsim0⟩

theorem conreyV1BoundedZeros_subset_mollified
    {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    conreyV1BoundedZeros g g0 g1 L A T ⊆
      conreyMollifiedV1BoundedZeros
        g g0 g1 L Y sigma0 P A T := by
  intro s hs
  rcases (mem_conreyV1BoundedZeros hg).mp hs with
    ⟨hsre0, hsreA, hsim0, hsimT, hV⟩
  apply (mem_conreyMollifiedV1BoundedZeros hg hY hP1).mpr
  exact ⟨hsre0, hsreA, hsim0, hsimT,
    conreyMollifiedDegreeOneV1_eq_zero_of_v1_eq_zero hV⟩

/-- Shared finite boundary set.  Using the union makes membership in this set
equivalent to `Re s = 1/2` for every zero in either family. -/
noncomputable def conreyV1MollifiedCriticalBoundaryZeros
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (A T : ℝ) : Finset ℂ :=
  (conreyV1BoundedZeros g g0 g1 L A T ∪
    conreyMollifiedV1BoundedZeros g g0 g1 L Y sigma0 P A T).filter
      fun s => s.re = 1 / 2

/-- Half-weighted bounded count represented by the actual analytic
multiplicities of `V1`. -/
noncomputable def conreyV1BoundedHalfWeightedZeroCount
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (A T : ℝ) : ℝ :=
  MathlibAux.halfWeightedMultiplicityMass
    (conreyV1BoundedZeros g g0 g1 L A T)
    (conreyV1MollifiedCriticalBoundaryZeros
      g g0 g1 L Y sigma0 P A T)
    (analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L))

/-- Half-weighted bounded count represented by the actual analytic
multiplicities of `V1 * B`. -/
noncomputable def conreyMollifiedV1BoundedHalfWeightedZeroCount
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (A T : ℝ) : ℝ :=
  MathlibAux.halfWeightedMultiplicityMass
    (conreyMollifiedV1BoundedZeros g g0 g1 L Y sigma0 P A T)
    (conreyV1MollifiedCriticalBoundaryZeros
      g g0 g1 L Y sigma0 P A T)
    (analyticOrderNatAt
      (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P))

/-- Bounded finite-rectangle form of Conrey's equation (35), with exact half
weight on the critical-line boundary and actual analytic multiplicities. -/
theorem conreyV1BoundedHalfWeightedZeroCount_le_mollified
    {g g0 g1 L sigma0 A T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    conreyV1BoundedHalfWeightedZeroCount
        g g0 g1 L Y sigma0 P A T ≤
      conreyMollifiedV1BoundedHalfWeightedZeroCount
        g g0 g1 L Y sigma0 P A T := by
  unfold conreyV1BoundedHalfWeightedZeroCount
    conreyMollifiedV1BoundedHalfWeightedZeroCount
  apply MathlibAux.halfWeightedMultiplicityMass_mono
  · exact conreyV1BoundedZeros_subset_mollified hg hY hP1
  · intro s hs
    rcases (mem_conreyV1BoundedZeros hg).mp hs with
      ⟨hsre0, _hsreA, hsim0, _hsimT, _hV⟩
    have hs0 : 0 < s.re := by linarith
    have hs1 : s ≠ 1 := by
      intro hsone
      have := congrArg Complex.im hsone
      simp at this
      linarith
    exact analyticOrderNatAt_conreyDegreeOneV1_le_mollified_of_g_ne_zero
      hg hs0 hs1 hY hP1

end HardyTheorem
