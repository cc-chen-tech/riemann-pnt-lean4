import HardyTheorem.ConreyEtaRectangleZeros
import HardyTheorem.ConreyBalancedTraceCount
import MathlibAux.HalfBoundaryArgumentPrinciple

/-!
# Actual eta contour counting with full multiplicity loss

The three nonsingular edges determine a finite lower bound for genuine zeta
simple zeros. The eta zero table, regularized trace and phase partition are
constructed, not supplied. The boundary half-weight and the component loss
combine into twice the full eta multiplicity on the same rectangle.

Nonvanishing on the three edges remains an explicit actual-eta hypothesis.
This finite identity does not assert quantitative edge estimates or the
long-mollifier asymptotic needed for Conrey's proportion theorem.
-/

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace HardyTheorem

/-- The actual three-edge argument controls genuine zeta simple zeros after
charging twice the full eta-zero multiplicity, including left-edge zeros. -/
theorem exists_conreyDegreeOneEta_simpleZero_finset_of_three_edges
    {g g0 g1 L A U T : ℝ}
    (hg : g ≠ 0) (hA : 1 / 2 < A) (hU : 0 ≤ U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        conreyDegreeOneEta g g0 g1 L z ≠ 0) :
    ∃ (K : Finset ℂ) (S : Finset ℝ),
      (∀ z, z ∈ K ↔ 1 / 2 ≤ z.re ∧ z.re ≤ A ∧ U ≤ z.im ∧ z.im ≤ T ∧
        conreyDegreeOneEta g g0 g1 L z = 0) ∧
      (∀ t ∈ S, t ∈ Ioo U T ∧ riemannZeta (conreyCriticalPoint t) = 0 ∧
        analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1) ∧
      ((∫ x in (1 / 2 : ℝ)..A,
          (logDeriv (conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * U)).im) +
        (∫ t in U..T,
          (logDeriv (conreyDegreeOneEta g g0 g1 L) ((A : ℂ) + I * t)).re) -
        (∫ x in (1 / 2 : ℝ)..A,
          (logDeriv (conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * T)).im)) /
          Real.pi - 2 * (∑ z ∈ K,
            (analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) z : ℝ)) - 1 ≤ S.card := by
  classical
  let f := conreyDegreeOneEta g g0 g1 L
  let m := analyticOrderNatAt f
  have hbase : f (conreyCriticalPoint U) ≠ 0 := by
    apply hedge _ _ (Or.inl (by simp))
    simp only [mem_reProdIm, mem_Icc, conreyCriticalPoint_re, conreyCriticalPoint_im]
    exact ⟨⟨le_rfl, hA.le⟩, le_rfl, hUT.le⟩
  obtain ⟨K, hK, hmass⟩ :=
    exists_conreyDegreeOneEta_rectangle_zero_finset hg hA.le hU hbase
  let off := K.filter (fun z => 1 / 2 < z.re)
  let left := K.filter (fun z => z.re = 1 / 2)
  have hunion : off ∪ left = K := by
    ext z
    simp only [off, left, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    · intro hz
      rcases lt_or_eq_of_le ((hK z).mp hz).1 with hlt | heq
      · exact Or.inl ⟨hz, hlt⟩
      · exact Or.inr ⟨hz, heq.symm⟩
  have hdisjoint : Disjoint off left := by
    apply Finset.disjoint_left.mpr
    intro z ho hl
    have hlt := (Finset.mem_filter.mp ho).2
    have heq := (Finset.mem_filter.mp hl).2
    linarith
  have hstrict : ∀ z ∈ K, z.re < A ∧ U < z.im ∧ z.im < T := by
    intro z hz
    obtain ⟨hzlo, hzhi, hzU, hzT, hz0⟩ := (hK z).mp hz
    have hzR : z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T) :=
      ⟨⟨hzlo, hzhi⟩, hzU, hzT⟩
    have hnotedge : ¬ (z.im = U ∨ z.re = A ∨ z.im = T) :=
      fun he => hedge z hzR he hz0
    refine ⟨lt_of_le_of_ne hzhi ?_, lt_of_le_of_ne hzU ?_, lt_of_le_of_ne hzT ?_⟩
    · exact fun he => hnotedge (Or.inr (Or.inl he))
    · exact fun he => hnotedge (Or.inl he.symm)
    · exact fun he => hnotedge (Or.inr (Or.inr he))
  have hzero : ∀ z ∈ ([[1 / 2, A]] ×ℂ [[U, T]]), f z = 0 ↔ z ∈ off ∪ left := by
    intro z hz
    have hzR : 1 / 2 ≤ z.re ∧ z.re ≤ A ∧ U ≤ z.im ∧ z.im ≤ T := by
      simpa only [uIcc_of_le hA.le, uIcc_of_le hUT.le, mem_reProdIm,
        mem_Icc, and_assoc] using hz
    rw [hunion, hK z]
    exact ⟨fun hz0 => ⟨hzR.1, hzR.2.1, hzR.2.2.1, hzR.2.2.2, hz0⟩,
      fun hz0 => hz0.2.2.2.2⟩
  have hoff : ∀ z ∈ off, 1 / 2 < z.re ∧ z.re < A ∧ U < z.im ∧ z.im < T := by
    intro z hz
    obtain ⟨hzK, hzlo⟩ := Finset.mem_filter.mp hz
    exact ⟨hzlo, hstrict z hzK⟩
  have hleft : ∀ z ∈ left, z.re = 1 / 2 ∧ U < z.im ∧ z.im < T := by
    intro z hz
    obtain ⟨hzK, hzlo⟩ := Finset.mem_filter.mp hz
    exact ⟨hzlo, (hstrict z hzK).2⟩
  have horder : ∀ z ∈ off ∪ left, analyticOrderAt f z = m z := by
    intro z _hz
    exact (Nat.cast_analyticOrderNatAt
      (analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero hg z)).symm
  obtain ⟨q, hq, htrace, hhalf⟩ :=
    MathlibAux.exists_regularized_trace_half_boundary_argument hA hUT off left m
      (fun z _hz => analyticAt_conreyDegreeOneEta g g0 g1 L z)
      hzero hoff hleft horder
  have hactual : ∀ t ∈ Ioo U T, f (conreyCriticalPoint t) ≠ 0 →
      q t = (logDeriv f (conreyCriticalPoint t)).re := by
    intro t ht hn
    simpa [f, conreyCriticalPoint] using htrace t ⟨ht.1.le, ht.2.le⟩
      (by simpa [f, conreyCriticalPoint] using hn)
  obtain ⟨S, hcount, hS⟩ :=
    exists_conreyDegreeOneEta_simpleZero_finset_of_regularized_trace hg hU hUT hq hactual
  have hmassR : (∑ z ∈ left, (m z : ℝ)) =
      conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T := by
    exact_mod_cast hmass
  have hfull : (∑ z ∈ K, (m z : ℝ)) =
      (∑ z ∈ off, (m z : ℝ)) + (∑ z ∈ left, (m z : ℝ)) := by
    rw [← hunion, Finset.sum_union hdisjoint]
  refine ⟨K, S, hK, hS, ?_⟩
  have hcount' : (∫ t in U..T, q t) ≤
      ((S.card : ℝ) + conreyEtaCriticalZeroMultiplicityMassBetween g g0 g1 L U T + 1) *
        Real.pi := by
    apply (div_le_iff₀ Real.pi_pos).mp
    linarith [hcount]
  have htarget :
      ((∫ x in (1 / 2 : ℝ)..A, (logDeriv f ((x : ℂ) + I * U)).im) +
        (∫ t in U..T, (logDeriv f ((A : ℂ) + I * t)).re) -
        (∫ x in (1 / 2 : ℝ)..A, (logDeriv f ((x : ℂ) + I * T)).im)) / Real.pi ≤
          (S.card : ℝ) + 2 * (∑ z ∈ K, (m z : ℝ)) + 1 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    rw [hfull, hmassR]
    rw [hmassR] at hhalf
    dsimp only [f]
    nlinarith only [hhalf, hcount']
  linarith only [htarget]

end HardyTheorem
