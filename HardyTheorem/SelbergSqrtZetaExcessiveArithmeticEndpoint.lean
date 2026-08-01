import HardyTheorem.SelbergSqrtZetaSignedActualFourierBudget
import HardyTheorem.SelbergSqrtZetaSignedLagIntegral

/-!
# Arithmetic endpoint for excessive signed Selberg windows

With threshold `eta = H / 2`, the actual signed-window second moment has the
required size once the collected model energy is at most `T / 1920` and the
uniform zeta-approximation error satisfies `6144 C^2 X^2 <= T`.  In
particular, the two remaining estimates no longer depend on the window length.
-/

open MeasureTheory Set

namespace HardyTheorem

/-- A fixed saving in the collected model energy, together with the natural
`X^2 = o(T)` approximation condition, gives the exact `T / 24` excessive-set
bound at threshold `H / 2`. -/
theorem
    exists_volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_modelEnergy_le :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H : ℝ,
        T0 ≤ T → 0 < H → H ≤ T →
        selbergSqrtZetaSignedModelL2Budget T X ≤ T / 1920 →
        6144 * C ^ 2 * (X : ℝ) ^ 2 ≤ T →
        volume.real
            (Icc T (2 * T - H) ∩
              selbergSqrtZetaExcessiveSignedMassStarts X H (H / 2)) ≤
          T / 24 := by
  obtain ⟨C, T0, hC, hT0, hsecond⟩ :=
    exists_integral_sq_selbergSqrtZetaSignedShortIntegral_le_modelL2Budget_add_error
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H hT hH hHT hmodel happrox
  have hTpos : 0 < T := zero_lt_one.trans_le (hT0.trans hT)
  have hAB : T ≤ 2 * T - H := by linarith
  have hsqrtPos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hsqrtSq : (Real.sqrt T) ^ 2 = T :=
    Real.sq_sqrt hTpos.le
  have hmodelTerm :
      10 * H ^ 2 * selbergSqrtZetaSignedModelL2Budget T X ≤
        T * H ^ 2 / 192 := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hmodel
        (show 0 ≤ 10 * H ^ 2 by positivity)
    nlinarith
  have herrorEq :
      2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 =
        32 * C ^ 2 * H ^ 2 * (X : ℝ) ^ 2 := by
    field_simp [ne_of_gt hsqrtPos]
    nlinarith [hsqrtSq]
  have herrorTerm :
      2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 ≤
        T * H ^ 2 / 192 := by
    rw [herrorEq]
    have hscaled :=
      mul_le_mul_of_nonneg_right happrox (sq_nonneg H)
    nlinarith
  have hmoment :
      (∫ t in T..2 * T - H,
          (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
        T * (H / 2) ^ 2 / 24 := by
    calc
      (∫ t in T..2 * T - H,
          (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
          10 * H ^ 2 * selbergSqrtZetaSignedModelL2Budget T X +
            2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 :=
        hsecond X hX T H hT hH hHT
      _ ≤ T * H ^ 2 / 192 + T * H ^ 2 / 192 :=
        add_le_add hmodelTerm herrorTerm
      _ = T * (H / 2) ^ 2 / 24 := by ring
  have hcheb :=
    volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_secondMoment
      X (A := T) (B := 2 * T - H) (H := H) (eta := H / 2)
        hAB (half_pos hH)
  rw [Set.inter_comm]
  refine hcheb.trans ?_
  rw [div_le_iff₀ (sq_pos_of_pos (half_pos hH))]
  calc
    (∫ t in T..2 * T - H,
        (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
        T * (H / 2) ^ 2 / 24 := hmoment
    _ = T / 24 * (H / 2) ^ 2 := by ring

end HardyTheorem
