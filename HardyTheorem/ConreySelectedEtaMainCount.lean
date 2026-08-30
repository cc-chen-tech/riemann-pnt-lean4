import HardyTheorem.ConreySelectedHeightMeanSquare
import HardyTheorem.ConreyEtaArgumentMain

/-! Actual selected-height simple-zero count with eta's argument eliminated.
The original long mollifier, selected heights, and positive mean square remain
unchanged. No mean-square estimate or asymptotic zero proportion is assumed. -/

open Complex Set

namespace HardyTheorem

/-- Insert the proved three-edge eta lower bound into the actual mean-square
count on the same selected rectangle, at the original external cutoff `exp L`. -/
theorem exists_conrey_selected_heights_simpleZeroCount_lower_bound_logMain :
    ∃ L0 : ℝ, 40000 ≤ L0 ∧ ∀ {Y : ℕ} {R L : ℝ},
      2 ≤ Y → (Y : ℝ) ≤ Real.exp L → 0 < R → R ≤ 6 / 5 → L0 ≤ L →
      ∃ U T : ℝ,
        U ∈ Icc (2 * Real.log L + 1) (2 * Real.log L + 2) ∧
        T ∈ Icc (Real.exp L - 1) (Real.exp L) ∧ U < T ∧
        (∀ z ∈ (Icc (1 / 2 - R / L) (2 * Real.log L) ×ℂ Icc U T),
          z.im = U ∨ z.re = 2 * Real.log L ∨ z.im = T →
            conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
              (1 / 2 - R / L) conreyExplicitP z ≠ 0) ∧
        0 < (∫ t in U..T,
          ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
            (1 / 2 - R / L) conreyExplicitP
            (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖ ^ 2) ∧
        conreyEtaThreeEdgeLowerMain L U T / Real.pi -
          ((T - U) * Real.log ((∫ t in U..T,
            ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
              (1 / 2 - R / L) conreyExplicitP
              (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖ ^ 2) / (T - U)) +
            2 * (507 * Real.exp L / L + 2200000000000 * L ^ 7 +
              (2 * Real.log L - (1 / 2 - R / L)) * Real.pi)) /
            (2 * Real.pi * (R / L)) - 1 ≤ positiveCriticalLineSimpleZeroCount (Real.exp L) := by
  obtain ⟨Lm, hm, hselect⟩ :=
    exists_conrey_selected_heights_simpleZeroCount_lower_bound_meanSquare
  obtain ⟨Le, _, hmain⟩ := exists_conreyEta_threeEdgeArgument_lower_bound
  refine ⟨max Lm Le, hm.trans (le_max_left _ _), ?_⟩
  intro Y R L hY hYtop hR hRmax hlarge
  have hLm : Lm ≤ L := (le_max_left Lm Le).trans hlarge
  have hLe : Le ≤ L := (le_max_right Lm Le).trans hlarge
  obtain ⟨U, T, hU, hT, hUT, hedge, hM, hcount⟩ := hselect hY hYtop hR hRmax hLm
  have hLpos : 0 < L := by linarith [hm.trans hLm]
  have hsigma : (1 / 2 : ℝ) - R / L ≤ 1 / 2 := by
    linarith [div_nonneg hR.le hLpos.le]
  have hb : ∀ x ∈ Icc (1 / 2 - R / L) (2 * Real.log L),
      conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
        (1 / 2 - R / L) conreyExplicitP ((x : ℂ) + I * U) ≠ 0 := by
    intro x hx
    apply hedge ((x : ℂ) + I * U)
    · simpa [mem_reProdIm] using And.intro hx (show U ∈ Icc U T from ⟨le_rfl, hUT.le⟩)
    · exact Or.inl (by simp)
  have ht : ∀ x ∈ Icc (1 / 2 - R / L) (2 * Real.log L),
      conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
        (1 / 2 - R / L) conreyExplicitP ((x : ℂ) + I * T) ≠ 0 := by
    intro x hx
    apply hedge ((x : ℂ) + I * T)
    · simpa [mem_reProdIm] using And.intro hx (show T ∈ Icc U T from ⟨hUT.le, le_rfl⟩)
    · exact Or.inr (Or.inr (by simp))
  have hEta := hmain hLe hsigma hU hT hUT hb ht
  have harg := div_le_div_of_nonneg_right hEta Real.pi_pos.le
  refine ⟨U, T, hU, hT, hUT, hedge, hM, ?_⟩
  linarith only [hcount, harg]

end HardyTheorem
