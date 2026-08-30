import HardyTheorem.ConreyMollifiedFullCount

/-!
The full shifted positive-height rectangle has a finite actual V1*B zero
table. Its Re >= 1/2 subfamily has exactly the full bounded (U,T] count.
Zeros on the shifted left edge are not excluded or half-weighted.
-/

open Complex Set
open scoped BigOperators

namespace HardyTheorem

/-- Construct all actual mollified zeros in the shifted closed rectangle,
their finite analytic orders, and the exact full critical-right mass.
Only the bottom edge must be zero-free for this count identification. -/
theorem exists_conreyMollified_rectangle_zero_finset
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hsigma0 : 0 < sigma0) (hsigmaHalf : sigma0 ≤ 1 / 2) (hU : 0 < U)
    (hbottom : ∀ z ∈ (Icc sigma0 A ×ℂ Icc U T), z.im = U →
      conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z ≠ 0) :
    ∃ K : Finset ℂ,
      (∀ z, z ∈ K ↔ sigma0 ≤ z.re ∧ z.re ≤ A ∧ U ≤ z.im ∧ z.im ≤ T ∧
        conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z = 0) ∧
      (∀ z ∈ K,
        analyticOrderAt (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z =
          analyticOrderNatAt (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z) ∧
      (∑ z ∈ K.filter (fun z => 1 / 2 ≤ z.re),
        analyticOrderNatAt (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) z) =
        conreyMollifiedV1BoundedFullZeroCountBetween g g0 g1 L Y sigma0 P A U T := by
  classical
  let R : Set ℂ := Icc sigma0 A ×ℂ Icc U T
  let F := conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P
  have hgeom : ∀ z ∈ R, 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    refine ⟨hsigma0.trans_le hz.1.1, ?_⟩
    intro hz1
    have him := hz.2.1
    simp only [hz1, Complex.one_im] at him
    linarith
  have han : AnalyticOnNhd ℂ F R := by
    intro z hz
    have hV := analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
      (g := g) (g0 := g0) (g1 := g1) (L := L) (hgeom z hz).1 (hgeom z hz).2
    exact hV.mul (analyticOnNhd_conreyMollifier Y sigma0 P z (by simp))
  have hfiniteOrder : ∀ z ∈ R, analyticOrderAt F z ≠ ⊤ := by
    intro z hz
    have hV := analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
      (g := g) (g0 := g0) (g1 := g1) (L := L) (hgeom z hz).1 (hgeom z hz).2
    have hB := analyticOnNhd_conreyMollifier Y sigma0 P z (by simp)
    have hVfinite := analyticOrderAt_conreyDegreeOneV1_ne_top_of_g_ne_zero
      (g0 := g0) (g1 := g1) (L := L) hg (hgeom z hz).1 (hgeom z hz).2
    have hBfinite := analyticOrderAt_conreyMollifier_ne_top hY hP1 sigma0 z
    change analyticOrderAt
      (conreyDegreeOneV1 g g0 g1 L * conreyMollifier Y sigma0 P) z ≠ ⊤
    rw [analyticOrderAt_mul hV hB]
    intro htop
    exact (ENat.add_eq_top.mp htop).elim hVfinite hBfinite
  let D := MeromorphicOn.divisor F R
  have hcompact : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hnotop : ∀ u : R, meromorphicOrderAt F u ≠ ⊤ := by
    intro u
    rw [(han u u.property).meromorphicOrderAt_eq]
    intro htop
    exact hfiniteOrder u u.property (ENat.map_eq_top_iff.mp htop)
  have hzeroD : R ∩ F ⁻¹' {0} = D.support := by
    simpa [D] using han.meromorphicNFOn.zero_set_eq_divisor_support hnotop
  have hfinite : D.support.Finite := D.finiteSupport hcompact
  let K : Finset ℂ := hfinite.toFinset
  have hK : ∀ z, z ∈ K ↔ sigma0 ≤ z.re ∧ z.re ≤ A ∧ U ≤ z.im ∧ z.im ≤ T ∧ F z = 0 := by
    intro z
    change z ∈ hfinite.toFinset ↔ _
    rw [hfinite.mem_toFinset, ← hzeroD]
    simp only [R, mem_inter_iff, mem_reProdIm, mem_Icc,
      mem_preimage, mem_singleton_iff, and_assoc]
  have hKmem : ∀ z ∈ K, z ∈ R := by
    intro z hz
    obtain ⟨hlo, hhi, hU', hT', _⟩ := (hK z).mp hz
    exact ⟨⟨hlo, hhi⟩, hU', hT'⟩
  have hfilter : K.filter (fun z => 1 / 2 ≤ z.re) =
      (conreyMollifiedV1BoundedZeros g g0 g1 L Y sigma0 P A T).filter
        (fun z => U < z.im) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzK, hzhalf⟩ := Finset.mem_filter.mp hz
      obtain ⟨_hzlo, hzhi, hzU, hzT, hz0⟩ := (hK z).mp hzK
      have hzUstrict : U < z.im := by
        apply lt_of_le_of_ne hzU
        intro heq
        exact hbottom z (hKmem z hzK) heq.symm hz0
      refine Finset.mem_filter.mpr ⟨?_, hzUstrict⟩
      exact (mem_conreyMollifiedV1BoundedZeros hg hY hP1).mpr
        ⟨hzhalf, hzhi, hU.trans hzUstrict, hzT, hz0⟩
    · intro hz
      obtain ⟨hzB, hzU⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzhalf, hzhi, _hzpos, hzT, hz0⟩ :=
        (mem_conreyMollifiedV1BoundedZeros hg hY hP1).mp hzB
      exact Finset.mem_filter.mpr
        ⟨(hK z).mpr ⟨hsigmaHalf.trans hzhalf, hzhi, hzU.le, hzT, hz0⟩, hzhalf⟩
  refine ⟨K, hK, ?_, ?_⟩
  · intro z hz
    unfold analyticOrderNatAt
    exact (ENat.natCast_toNat (hfiniteOrder z (hKmem z hz))).symm
  · rw [hfilter]
    rfl

end HardyTheorem
