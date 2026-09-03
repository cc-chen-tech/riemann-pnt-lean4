import HardyTheorem.ConreyMollifiedLittlewood
import HardyTheorem.ConreyEquation37Edges

/-!
The selected-height Littlewood bound for the actual simple-zero count at
`exp L`. The three non-left zero-free edges are constructed, the absolute
selection constants are absorbed into one threshold, and every analytic
factor retains the same `L`, `Y`, `R`, `U`, and `T`.

This does not estimate the remaining left log integral or eta argument,
and therefore is not yet Conrey's positive-proportion theorem.
-/

open Complex Set
open scoped Interval
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

/-- The quantitative edge remainder is exactly the complete remainder
used by the actual Littlewood inequality, including both right integrals. -/
theorem conreyEquation37BoundaryRemainder_eq_littlewood (Y : ℕ) (R L U T : ℝ) :
    conreyEquation37BoundaryRemainder Y R L U T =
      littlewoodRectangleNonleftRemainder
        (conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
          (1 / 2 - R / L) conreyExplicitP)
        (1 / 2 - R / L) (2 * Real.log L) U T := by
  simp only [conreyEquation37BoundaryRemainder, conreyEquation37RightLogTerm,
    conreyEquation37HorizontalTerm, conreyEquation37RightArgumentTerm,
    conreyHorizontalLeftEdge, conreyHorizontalRightEdge,
    conreyHorizontalJensenProduct, conreyExplicitRightVerticalFunction,
    conreyExplicitRightVerticalProduct, conreyMollifiedDegreeOneV1,
    littlewoodRectangleNonleftRemainder, mul_comm I]

/-- A uniform threshold suffices to select both heights, construct all
three non-left zero-free product edges, and bound the actual simple-zero
count at `exp L`. No left-edge nonvanishing condition is imposed. -/
theorem exists_conrey_selected_heights_simpleZeroCount_lower_bound :
    ∃ L0 : ℝ, 40000 ≤ L0 ∧
      ∀ {Y : ℕ} {R L : ℝ}, 2 ≤ Y → (Y : ℝ) ≤ Real.exp L →
        0 < R → R ≤ 6 / 5 → L0 ≤ L →
        ∃ U T : ℝ,
          U ∈ Icc (2 * Real.log L + 1) (2 * Real.log L + 2) ∧
          T ∈ Icc (Real.exp L - 1) (Real.exp L) ∧ U < T ∧
          (∀ z ∈ (Icc (1 / 2 - R / L) (2 * Real.log L) ×ℂ Icc U T),
            z.im = U ∨ z.re = 2 * Real.log L ∨ z.im = T →
              conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
                (1 / 2 - R / L) conreyExplicitP z ≠ 0) ∧
          conreyEtaThreeEdgeArgument (49 / 100) 0 (51 / 50) L
              (2 * Real.log L) U T / Real.pi -
            ((∫ t in U..T, Real.log
              ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
                (1 / 2 - R / L) conreyExplicitP
                (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖) +
              (507 * Real.exp L / L + 2200000000000 * L ^ 7 +
                (2 * Real.log L - (1 / 2 - R / L)) * Real.pi)) /
              (Real.pi * (R / L)) - 1 ≤
                positiveCriticalLineSimpleZeroCount (Real.exp L) := by
  obtain ⟨Creg, Cmass, hCreg, hCmass, hselect⟩ :=
    exists_conreyEquation37SelectedHeights_boundaryRemainder_le
  refine ⟨40000 + Creg + Cmass, by linarith, ?_⟩
  intro Y R L hY hYtop hR hRmax hL0
  have hL : 40000 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hCregTop : Creg ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hCmassTop : Cmass ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  obtain ⟨U, T, hU, hT, hUT, hbottom, htop, _, _, hrem⟩ :=
    hselect hY hYtop hR.le hRmax hL hCregTop hCmassTop
  have hquot : 0 < R / L := div_pos hR hLpos
  have hquotLe : R / L ≤ 3 / 100000 := by
    rw [div_le_iff₀ hLpos]
    nlinarith
  have hsigma : 0 < 1 / 2 - R / L := by linarith
  have hsigmaHalf : 1 / 2 - R / L < 1 / 2 := by linarith
  have hA : 1 / 2 < 2 * Real.log L := by
    linarith [two_le_log_of_forty_thousand_le hL]
  have hUone : 1 ≤ U := by
    dsimp [conreyHorizontalRightEdge] at hU
    linarith [hU.1, two_le_log_of_forty_thousand_le hL]
  have hedge : ∀ z ∈ (Icc (1 / 2 - R / L) (2 * Real.log L) ×ℂ Icc U T),
      z.im = U ∨ z.re = 2 * Real.log L ∨ z.im = T →
        conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
          (1 / 2 - R / L) conreyExplicitP z ≠ 0 := by
    intro z hz he
    have hzrepr : (z.re : ℂ) + I * (z.im : ℂ) = z := by
      simpa only [mul_comm I] using Complex.re_add_im z
    rcases he with hbot | hright | htop'
    · have h := hbottom z.re hz.1
      change conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
        (1 / 2 - R / L) conreyExplicitP ((z.re : ℂ) + I * U) ≠ 0 at h
      simpa only [← hbot, hzrepr] using h
    · have hre := three_tenths_le_conreyExplicitRightVerticalProduct_global_re
        hY hsigmaHalf.le hL (hUone.trans hz.2.1) (hz.2.2.trans hT.2)
      have hrepr : ((2 * Real.log L : ℝ) : ℂ) + I * (z.im : ℂ) = z := by
        rw [← hright]
        exact hzrepr
      change (3 / 10 : ℝ) ≤
        (conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
          (1 / 2 - R / L) conreyExplicitP
          (((2 * Real.log L : ℝ) : ℂ) + I * z.im)).re at hre
      rw [hrepr] at hre
      intro heq
      rw [heq, Complex.zero_re] at hre
      norm_num at hre
    · have h := htop z.re hz.1
      change conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
        (1 / 2 - R / L) conreyExplicitP ((z.re : ℂ) + I * T) ≠ 0 at h
      simpa only [← htop', hzrepr] using h
  refine ⟨U, T, hU, hT, hUT, hedge, ?_⟩
  have hcount := conrey_simpleZeroCount_lower_bound_of_mollified_littlewood
    (by norm_num : (49 / 100 : ℝ) ≠ 0) hY
    (show conreyExplicitP 1 = 1 by norm_num [conreyExplicitP])
    hsigma hsigmaHalf hA (by linarith : 0 < U) hUT hedge
  rw [show (1 / 2 : ℝ) - (1 / 2 - R / L) = R / L by ring,
    ← conreyEquation37BoundaryRemainder_eq_littlewood] at hcount
  have hremUpper := (le_abs_self (conreyEquation37BoundaryRemainder Y R L U T)).trans hrem
  have hden : 0 < Real.pi * (R / L) := mul_pos Real.pi_pos hquot
  have hquotRem := div_le_div_of_nonneg_right hremUpper hden.le
  have hmono : (positiveCriticalLineSimpleZeroCount T : ℝ) ≤
      positiveCriticalLineSimpleZeroCount (Real.exp L) := by
    exact_mod_cast positiveCriticalLineSimpleZeroCount_mono hT.2
  dsimp [conreyHorizontalLeftEdge, conreyHorizontalRightEdge] at hquotRem
  simp only [add_div] at hcount hquotRem ⊢
  linarith only [hcount, hquotRem, hmono]

end HardyTheorem
