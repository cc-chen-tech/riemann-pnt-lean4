import HardyTheorem.ConreyMollifiedLittlewood
import HardyTheorem.ConreyMollifiedMeanSquare

/-!
# Local finite simple-zero witnesses with the actual mean square

局部有限单零点见证；不包含实际均方渐近式或最终零点比例。
This local witness theorem does not supply a final mean-square estimate.

Unlike the existing canonical-count wrapper, this theorem preserves the
finite set in (U,T). Its members are actual simple zeta zeros. The full
eta multiplicity, twice the complete non-left remainder and endpoint
loss one are retained. No final mean-square estimate is supplied.
-/

open Complex Set
open scoped BigOperators Interval
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

private theorem exists_local_simpleZero_finset_of_eta_edges_mollified_full
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hA : 1 / 2 < A) (hU : 0 ≤ U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        conreyDegreeOneEta g g0 g1 L z ≠ 0) :
    ∃ S : Finset ℝ,
      (∀ t ∈ S, t ∈ Ioo U T ∧ riemannZeta (conreyCriticalPoint t) = 0 ∧
        analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1) ∧
      conreyEtaThreeEdgeArgument g g0 g1 L A U T / Real.pi -
        2 * (conreyMollifiedV1BoundedFullZeroCountBetween
          g g0 g1 L Y sigma0 P A U T : ℝ) - 1 ≤ (S.card : ℝ) := by
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
  have hcountE : conreyEtaThreeEdgeArgument g g0 g1 L A U T / Real.pi -
      2 * (∑ z ∈ K, (analyticOrderNatAt (conreyDegreeOneEta g g0 g1 L) z : ℝ)) - 1 ≤
        (S.card : ℝ) := hcount
  refine ⟨S, hS, ?_⟩
  linarith only [hmass, hcountE]

/-- Local finite witness theorem. The shifted left edge may contain
zeros; the positive actual moment and the witnesses are constructed from
the same function and rectangle, not passed as analytic assumptions. -/
theorem exists_conrey_local_simpleZero_finset_lower_bound_meanSquare
    {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hsigma0 : 0 < sigma0) (hsigmaHalf : sigma0 < 1 / 2)
    (hA : 1 / 2 < A) (hU : 0 < U) (hUT : U < T)
    (hedge : ∀ z ∈ (Icc sigma0 A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T →
        conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z ≠ 0) :
    let F := conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P
    ∃ S : Finset ℝ,
      (∀ t ∈ S, t ∈ Ioo U T ∧ riemannZeta (conreyCriticalPoint t) = 0 ∧
        analyticOrderNatAt riemannZeta (conreyCriticalPoint t) = 1) ∧
      0 < (∫ t in U..T, ‖F ((sigma0 : ℂ) + I * t)‖ ^ 2) ∧
      conreyEtaThreeEdgeArgument g g0 g1 L A U T / Real.pi -
        ((T - U) * Real.log
          ((∫ t in U..T, ‖F ((sigma0 : ℂ) + I * t)‖ ^ 2) / (T - U)) +
          2 * littlewoodRectangleNonleftRemainder F sigma0 A U T) /
            (2 * Real.pi * (1 / 2 - sigma0)) - 1 ≤ (S.card : ℝ) := by
  have heta : ∀ z ∈ (Icc (1 / 2 : ℝ) A ×ℂ Icc U T),
      z.im = U ∨ z.re = A ∨ z.im = T → conreyDegreeOneEta g g0 g1 L z ≠ 0 := by
    intro z hz he hz0
    have hzre : 0 < z.re := by linarith [hz.1.1]
    have hz1 : z ≠ 1 := by
      intro heq
      have him := hz.2.1
      simp only [heq, Complex.one_im] at him
      linarith
    apply hedge z ⟨⟨hsigmaHalf.le.trans hz.1.1, hz.1.2⟩, hz.2⟩ he
    exact conreyMollifiedDegreeOneV1_eq_zero_of_v1_eq_zero
      ((conreyDegreeOneEta_eq_zero_iff_conreyDegreeOneV1_eq_zero_of_re_pos_of_ne_one
        hzre hz1).mp hz0)
  obtain ⟨S, hS, hcount⟩ :=
    exists_local_simpleZero_finset_of_eta_edges_mollified_full
      (sigma0 := sigma0) hg hY hP1 hA hU.le hUT heta
  have hmass := conreyMollified_boundedFullCount_le_logNorm_edges
    hg hY hP1 hsigma0 hsigmaHalf hA hU hUT hedge
  have hJ := conreyMollified_logNorm_meanSquare_bounds
    hg hY hP1 hsigma0 hsigmaHalf.le hA hU hUT
    (fun z hz he => hedge z hz (Or.inl he))
  let F := conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P
  let Ilog : ℝ := ∫ t in U..T, Real.log ‖F ((sigma0 : ℂ) + I * t)‖
  let M : ℝ := ∫ t in U..T, ‖F ((sigma0 : ℂ) + I * t)‖ ^ 2
  let B := littlewoodRectangleNonleftRemainder F sigma0 A U T
  let d := Real.pi * (1 / 2 - sigma0)
  have hd : 0 < d := mul_pos Real.pi_pos (sub_pos.mpr hsigmaHalf)
  have htwo : 2 * (conreyMollifiedV1BoundedFullZeroCountBetween
      g g0 g1 L Y sigma0 P A U T : ℝ) ≤ (Ilog + B) / d := by
    apply (le_div_iff₀ hd).mpr
    calc
      _ = (2 * Real.pi) * (1 / 2 - sigma0) *
          (conreyMollifiedV1BoundedFullZeroCountBetween
            g g0 g1 L Y sigma0 P A U T : ℝ) := by dsimp only [d]; ring
      _ ≤ _ := hmass
  have hlog : 2 * Ilog ≤ (T - U) * Real.log (M / (T - U)) := hJ.2
  have hmean : (Ilog + B) / d ≤
      ((T - U) * Real.log (M / (T - U)) + 2 * B) / (2 * d) := by
    calc
      _ = (2 * Ilog + 2 * B) / (2 * d) := by
        field_simp [hd.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hlog])
        (mul_pos (by norm_num : (0 : ℝ) < 2) hd).le
  refine ⟨S, hS, hJ.1, ?_⟩
  change conreyEtaThreeEdgeArgument g g0 g1 L A U T / Real.pi -
    ((T - U) * Real.log (M / (T - U)) + 2 * B) /
      (2 * Real.pi * (1 / 2 - sigma0)) - 1 ≤ (S.card : ℝ)
  rw [show 2 * Real.pi * (1 / 2 - sigma0) = 2 * d by dsimp only [d]; ring]
  linarith only [hcount, htwo, hmean]

end HardyTheorem
