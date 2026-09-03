import HardyTheorem.ConreyMollifiedFullCount
import HardyTheorem.ConreyFiniteContourCount
import HardyTheorem.ConreySimpleZeroCount

/-!
# Actual simple-zero counts from the mollified full-multiplicity budget

This joins the eta contour argument, actual product zero counts, and the
canonical simple critical-line numerator. Three-edge eta nonvanishing stays
explicit; no moment asymptotic or eventual positive proportion is asserted.
-/

open Complex Set
open scoped BigOperators Interval

namespace HardyTheorem

/-- The lower, upward right, and reversed upper eta argument contributions. -/
noncomputable def conreyEtaThreeEdgeArgument (g g0 g1 L A U T : ℝ) : ℝ :=
  (∫ x in (1 / 2 : ℝ)..A,
    (logDeriv (conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * U)).im) +
  (∫ t in U..T,
    (logDeriv (conreyDegreeOneEta g g0 g1 L) ((A : ℂ) + I * t)).re) -
  (∫ x in (1 / 2 : ℝ)..A,
    (logDeriv (conreyDegreeOneEta g g0 g1 L) ((x : ℂ) + I * T)).im)

private theorem simpleZeroWitness_card_le_canonical
    {U T : ℝ} (hU : 0 ≤ U) (S : Finset ℝ)
    (hS : ∀ t ∈ S, t ∈ Ioo U T ∧ riemannZeta (conreyCriticalPoint t) = 0 ∧
      analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1) :
    S.card ≤ positiveCriticalLineSimpleZeroCount T := by
  classical
  have hinj : Function.Injective conreyCriticalPoint := by
    intro a b hab
    simpa using congrArg Complex.im hab
  have hsub : S.image conreyCriticalPoint ⊆ positiveCriticalLineSimpleZerosFinset T := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨htUT, ht0, htm⟩ := hS t ht
    apply mem_positiveCriticalLineSimpleZerosFinset.mpr
    refine ⟨⟨ht0, ?_, ?_⟩, ?_, ?_, by simp, htm⟩
    · norm_num
    · norm_num
    · simpa using lt_of_le_of_lt hU htUT.1
    · simpa using htUT.2.le
  calc
    S.card = (S.image conreyCriticalPoint).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The canonical actual simple-zero numerator is bounded below by the eta
three-edge argument minus twice the full bounded mollified zero mass. -/
theorem conrey_simpleZeroCount_lower_bound_of_three_edges_mollified_bounded
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hA : 1 / 2 < A) (hU : 0 ≤ U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        conreyDegreeOneEta g g0 g1 L z ≠ 0) :
    conreyEtaThreeEdgeArgument g g0 g1 L A U T / Real.pi -
      2 * (conreyMollifiedV1BoundedFullZeroCountBetween
        g g0 g1 L Y sigma0 P A U T : ℝ) - 1 ≤
      positiveCriticalLineSimpleZeroCount T := by
  obtain ⟨K, S, hK, hS, hcount⟩ :=
    exists_conreyDegreeOneEta_simpleZero_finset_of_three_edges hg hA hU hUT hedge
  have hKstrict : ∀ z ∈ K, 1 / 2 ≤ z.re ∧ z.re ≤ A ∧ U < z.im ∧ z.im ≤ T ∧
      conreyDegreeOneEta g g0 g1 L z = 0 := by
    intro z hz
    obtain ⟨hzlo, hzhi, hzU, hzT, hz0⟩ := (hK z).mp hz
    refine ⟨hzlo, hzhi, ?_, hzT, hz0⟩
    apply lt_of_le_of_ne hzU
    intro heq
    exact hedge z ⟨⟨hzlo, hzhi⟩, hzU, hzT⟩ (Or.inl heq.symm) hz0
  have hmass : (∑ z ∈ K, (analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) z : ℝ)) ≤
      conreyMollifiedV1BoundedFullZeroCountBetween g g0 g1 L Y sigma0 P A U T := by
    exact_mod_cast conreyEta_zero_mass_le_mollified_bounded_full hg hY hP1 hU K hKstrict
  have hcanonical : (S.card : ℝ) ≤ positiveCriticalLineSimpleZeroCount T := by
    exact_mod_cast simpleZeroWitness_card_le_canonical hU S hS
  have hcountE : conreyEtaThreeEdgeArgument g g0 g1 L A U T / Real.pi -
      2 * (∑ z ∈ K, (analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) z : ℝ)) - 1 ≤
        S.card := hcount
  linarith only [hmass, hcanonical, hcountE]

/-- The same lower bound with the full actual mollified half-strip count.
The height cutoff and all eta/mollifier parameters are unchanged. -/
theorem conrey_simpleZeroCount_lower_bound_of_three_edges_mollified_halfStrip
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hA : 1 / 2 < A) (hU : 0 ≤ U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        conreyDegreeOneEta g g0 g1 L z ≠ 0) :
    conreyEtaThreeEdgeArgument g g0 g1 L A U T / Real.pi -
      2 * (conreyMollifiedV1HalfStripFullZeroCountBetween
        g g0 g1 L Y sigma0 P U T : ℝ) - 1 ≤
      positiveCriticalLineSimpleZeroCount T := by
  have hb := conrey_simpleZeroCount_lower_bound_of_three_edges_mollified_bounded
    (sigma0 := sigma0) hg hY hP1 hA hU hUT hedge
  have hmass : (conreyMollifiedV1BoundedFullZeroCountBetween
      g g0 g1 L Y sigma0 P A U T : ℝ) ≤
      conreyMollifiedV1HalfStripFullZeroCountBetween g g0 g1 L Y sigma0 P U T := by
    exact_mod_cast conreyMollifiedV1BoundedFullZeroCountBetween_le_halfStrip
      (A := A) (U := U) (T := T) hg hY hP1
  linarith only [hb, hmass]

end HardyTheorem
