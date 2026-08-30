import HardyTheorem.ConreyEquation41Global

/-!
# All actual eta zeros in a closed rectangle

Compactness and the analytic divisor construct the zero table. Its left-edge
mass agrees exactly with the existing `(U,T]` ordinate budget when the lower
left endpoint is nonzero. No upper endpoint exclusion is needed for this
identity: both sides include the upper endpoint.
-/

open Complex Set
open scoped BigOperators

namespace HardyTheorem

/-- Construct the entire closed-rectangle zero table of the actual degree-one
eta and identify its left-edge mass with the actual critical-line budget. -/
theorem exists_conreyDegreeOneEta_rectangle_zero_finset
    {g g0 g1 L A U T : ℝ}
    (hg : g ≠ 0) (hA : 1 / 2 ≤ A) (hU : 0 ≤ U)
    (hbase : conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint U) ≠ 0) :
    ∃ K : Finset ℂ,
      (∀ z, z ∈ K ↔ 1 / 2 ≤ z.re ∧ z.re ≤ A ∧ U ≤ z.im ∧ z.im ≤ T ∧
        conreyDegreeOneEta g g0 g1 L z = 0) ∧
      (∑ z ∈ K.filter (fun z => z.re = 1 / 2),
        analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) z) =
        conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T := by
  classical
  let R : Set ℂ := Icc (1 / 2 : ℝ) A ×ℂ Icc U T
  let f := conreyDegreeOneEta g g0 g1 L
  let D := MeromorphicOn.divisor f R
  have hcompact : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have han : AnalyticOnNhd ℂ f R := by
    intro z _hz
    exact analyticAt_conreyDegreeOneEta g g0 g1 L z
  have hnotop : ∀ u : R, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(han u u.property).meromorphicOrderAt_eq]
    intro htop
    exact analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero hg u
      (ENat.map_eq_top_iff.mp htop)
  have hzeroD : R ∩ f ⁻¹' {0} = D.support := by
    simpa [D] using han.meromorphicNFOn.zero_set_eq_divisor_support hnotop
  have hfinite : D.support.Finite := D.finiteSupport hcompact
  let K : Finset ℂ := hfinite.toFinset
  have hK : ∀ z, z ∈ K ↔ 1 / 2 ≤ z.re ∧ z.re ≤ A ∧ U ≤ z.im ∧ z.im ≤ T ∧
      conreyDegreeOneEta g g0 g1 L z = 0 := by
    intro z
    change z ∈ hfinite.toFinset ↔ _
    rw [hfinite.mem_toFinset, ← hzeroD]
    simp only [R, f, mem_inter_iff, mem_reProdIm, mem_Icc,
      mem_preimage, mem_singleton_iff, and_assoc]
  let O := conreyEtaCriticalZeroOrdinatesBetween g g0 g1 L U T
  have hleft : K.filter (fun z => z.re = 1 / 2) = O.image conreyCriticalPoint := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzK, hzre⟩ := Finset.mem_filter.mp hz
      obtain ⟨_hzlo, _hzhi, hzU, hzT, hz0⟩ := (hK z).mp hzK
      have hzpoint : conreyCriticalPoint z.im = z := by
        apply Complex.ext
        · simpa using hzre.symm
        · simp
      have hzUstrict : U < z.im := by
        apply lt_of_le_of_ne hzU
        intro heq
        apply hbase
        have hzbase : conreyCriticalPoint U = z := by rwa [heq]
        rwa [hzbase]
      apply Finset.mem_image.mpr
      refine ⟨z.im, ?_, hzpoint⟩
      apply (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mpr
      exact ⟨hzUstrict, hzT, by rwa [hzpoint]⟩
    · intro hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨htU, htT, ht0⟩ :=
        (mem_conreyEtaCriticalZeroOrdinatesBetween hg hU).mp ht
      apply Finset.mem_filter.mpr
      refine ⟨(hK _).mpr ?_, by simp⟩
      simpa only [conreyCriticalPoint_re, conreyCriticalPoint_im] using
        And.intro (le_refl (1 / 2 : ℝ)) ⟨hA, htU.le, htT, ht0⟩
  refine ⟨K, hK, ?_⟩
  rw [hleft, Finset.sum_image]
  · rfl
  · intro a _ha b _hb hab
    simpa using congrArg Complex.im hab

end HardyTheorem
