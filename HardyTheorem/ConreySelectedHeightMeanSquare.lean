import HardyTheorem.ConreySelectedHeightCount
import HardyTheorem.ConreyMollifiedMeanSquare

/-!
The actual mean-square form of the selected-height simple-zero bound.
The left edge may contain zeros. This is an exact finite-height inequality,
not an evaluation or upper bound for the long mollified second moment.
-/

open Complex Set
open scoped Interval

namespace HardyTheorem

/-- Construct admissible heights and the actual positive second moment,
then insert Jensen into the canonical simple-zero bound at `exp L`.
The exact selected length, all fixed parameters, and twice the complete
boundary-error bound are retained. -/
theorem exists_conrey_selected_heights_simpleZeroCount_lower_bound_meanSquare :
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
          0 < (∫ t in U..T,
            ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
              (1 / 2 - R / L) conreyExplicitP
              (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖ ^ 2) ∧
          conreyEtaThreeEdgeArgument (49 / 100) 0 (51 / 50) L
              (2 * Real.log L) U T / Real.pi -
            ((T - U) * Real.log ((∫ t in U..T,
              ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
                (1 / 2 - R / L) conreyExplicitP
                (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖ ^ 2) / (T - U)) +
              2 * (507 * Real.exp L / L + 2200000000000 * L ^ 7 +
                (2 * Real.log L - (1 / 2 - R / L)) * Real.pi)) /
              (2 * Real.pi * (R / L)) - 1 ≤
                positiveCriticalLineSimpleZeroCount (Real.exp L) := by
  obtain ⟨L0, hL0, hselect⟩ :=
    exists_conrey_selected_heights_simpleZeroCount_lower_bound
  refine ⟨L0, hL0, ?_⟩
  intro Y R L hY hYtop hR hRmax hlarge
  obtain ⟨U, T, hU, hT, hUT, hedge, hcount⟩ := hselect hY hYtop hR hRmax hlarge
  have hL : 40000 ≤ L := hL0.trans hlarge
  have hLpos : 0 < L := by linarith
  have hquot : 0 < R / L := div_pos hR hLpos
  have hquotLe : R / L ≤ 3 / 100000 := by
    rw [div_le_iff₀ hLpos]
    nlinarith
  have hsigma : 0 < 1 / 2 - R / L := by linarith
  have hsigmaHalf : 1 / 2 - R / L ≤ 1 / 2 := by linarith
  have hA : 1 / 2 < 2 * Real.log L := by
    linarith [two_le_log_of_forty_thousand_le hL]
  have hUpos : 0 < U := by linarith [hU.1]
  have hJ := conreyMollified_logNorm_meanSquare_bounds
    (by norm_num : (49 / 100 : ℝ) ≠ 0) hY
    (show conreyExplicitP 1 = 1 by norm_num [conreyExplicitP])
    hsigma hsigmaHalf hA hUpos hUT (fun z hz he => hedge z hz (Or.inl he))
  refine ⟨U, T, hU, hT, hUT, hedge, hJ.1, ?_⟩
  let F := conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y
    (1 / 2 - R / L) conreyExplicitP
  let Ileft : ℝ := ∫ t in U..T, Real.log ‖F (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖
  let M : ℝ := ∫ t in U..T, ‖F (((1 / 2 - R / L : ℝ) : ℂ) + I * t)‖ ^ 2
  let B : ℝ := 507 * Real.exp L / L + 2200000000000 * L ^ 7 +
    (2 * Real.log L - (1 / 2 - R / L)) * Real.pi
  let d : ℝ := Real.pi * (R / L)
  have hd : 0 < d := mul_pos Real.pi_pos hquot
  have hlog : 2 * Ileft ≤ (T - U) * Real.log (M / (T - U)) := hJ.2
  have hbound : (Ileft + B) / d ≤
      ((T - U) * Real.log (M / (T - U)) + 2 * B) / (2 * d) := by
    calc
      _ = (2 * Ileft + 2 * B) / (2 * d) := by
        field_simp [hd.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hlog])
        (mul_pos (by norm_num) hd).le
  have hcount' :
      conreyEtaThreeEdgeArgument (49 / 100) 0 (51 / 50) L (2 * Real.log L) U T /
        Real.pi - (Ileft + B) / d - 1 ≤ positiveCriticalLineSimpleZeroCount (Real.exp L) :=
    hcount
  change conreyEtaThreeEdgeArgument (49 / 100) 0 (51 / 50) L (2 * Real.log L) U T /
    Real.pi - ((T - U) * Real.log (M / (T - U)) + 2 * B) /
      (2 * Real.pi * (R / L)) - 1 ≤ positiveCriticalLineSimpleZeroCount (Real.exp L)
  rw [show 2 * Real.pi * (R / L) = 2 * d by dsimp [d]; ring]
  linarith only [hcount', hbound]

end HardyTheorem
