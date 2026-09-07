import PrimeNumberTheorem.CarlsonHalfRangeParameters
import PrimeNumberTheorem.CarlsonConreyCriticalToInterior

/-! Scalar endpoint budgets for the actual integer half-range lengths.
No mean-square hypothesis occurs here: the endpoint expressions themselves
are bounded with the constants derived in the paper proof. -/

open Filter

namespace PrimeNumberTheorem.CarlsonZeroDensity

noncomputable def halfRangeCriticalConstant (C : ℝ) : ℝ :=
  2320 * Real.exp (1 / 4 : ℝ) * (C + 16 * Real.sqrt Real.pi)

noncomputable def halfRangeRightConstant : ℝ :=
  (102400 / 9 : ℝ) * Real.sqrt Real.pi * Real.exp 16

theorem halfRangeCriticalConstant_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < halfRangeCriticalConstant C := by unfold halfRangeCriticalConstant; positivity

theorem halfRangeRightConstant_pos : 0 < halfRangeRightConstant := by
  unfold halfRangeRightConstant
  positivity

private theorem gaussianMass_eq {Delta : ℝ} (hDelta : 0 < Delta) :
    Real.sqrt (Real.pi / (1 / Delta ^ 2)) = Real.sqrt Real.pi * Delta := by
  rw [div_div_eq_mul_div, div_one, Real.sqrt_mul Real.pi_pos.le,
    Real.sqrt_sq_eq_abs, abs_of_pos hDelta]

/-- Critical and right endpoint expressions have powers `19/20` and
`-29/20`, with explicit uniform constants. -/
theorem eventually_halfRange_endpoint_bounds {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ V : ℝ in atTop,
      let Y0 := halfRangeCoreCutoff V
      let Y1 := halfRangeOuterCutoff V
      let Delta := 16 * V ^ (19 / 20 : ℝ)
      let B := C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6
      carlsonConreyCriticalEndpointBound Delta Y0 Y1 B B ≤
        halfRangeCriticalConstant C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6 ∧
      carlsonConreyRightEndpointBound Delta Y0 ≤
        halfRangeRightConstant * V ^ (-29 / 20 : ℝ) := by
  filter_upwards [eventually_halfRangeCutoff_conditions] with V hparams
  obtain ⟨hV1, hY0, hY01, hY0U, hY1U, hY0L, hlogGap, hA0, hA18, hD0, hD16⟩ := hparams
  let Y0 := halfRangeCoreCutoff V
  let Y1 := halfRangeOuterCutoff V
  let P := V ^ (19 / 20 : ℝ)
  let L := 1 + Real.log V
  let Delta := 16 * P
  let B := C * P * L ^ 6
  let mass := Real.sqrt (Real.pi / (1 / Delta ^ 2))
  have hV0 : 0 < V := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hV1.le (by norm_num)
  have hP0 : 0 < P := by linarith
  have hDelta0 : 0 < Delta := by dsimp only [Delta]; positivity
  have hDelta1 : 1 ≤ Delta := by dsimp only [Delta]; linarith
  have hDeltaSq : 1 ≤ Delta ^ 2 := one_le_pow₀ hDelta1
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hV1.le]
  have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ hL1
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hmass0 : 0 ≤ mass := Real.sqrt_nonneg _
  have hmass : mass = 16 * Real.sqrt Real.pi * P := by
    dsimp only [mass]
    rw [gaussianMass_eq hDelta0]
    dsimp only [Delta]
    ring
  have hleftExp : Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) ≤ Real.exp (1 / 4 : ℝ) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (sq_pos_of_pos hDelta0)).mpr
    nlinarith
  have hrightExp : Real.exp (16 / Delta ^ 2) ≤ Real.exp 16 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (sq_pos_of_pos hDelta0)).mpr
    nlinarith
  have hcoeff : 2 * conreyOuterMultiplier Y0 Y1 ^ 2 +
      2 * conreyInnerMultiplier Y0 Y1 ^ 2 ≤ 1160 := by
    have ha := pow_le_pow_left₀ hA0 hA18 2
    have hd := pow_le_pow_left₀ hD0 hD16 2
    norm_num at ha hd
    linarith
  have hbracket : 2 * B + 2 * mass ≤
      (2 * C + 32 * Real.sqrt Real.pi) * P * L ^ 6 := by
    have hm : mass ≤ 16 * Real.sqrt Real.pi * P * L ^ 6 := by
      rw [hmass]
      exact le_mul_of_one_le_right (by positivity) hL6
    calc
      _ ≤ 2 * B + 2 * (16 * Real.sqrt Real.pi * P * L ^ 6) := by linarith
      _ = _ := by dsimp only [B]; ring
  have hcritical : carlsonConreyCriticalEndpointBound Delta Y0 Y1 B B ≤
      halfRangeCriticalConstant C * P * L ^ 6 := by
    calc
      _ = Real.exp ((1 / 2 : ℝ) ^ 2 / Delta ^ 2) *
          ((2 * conreyOuterMultiplier Y0 Y1 ^ 2 +
            2 * conreyInnerMultiplier Y0 Y1 ^ 2) * (2 * B + 2 * mass)) := by
        unfold carlsonConreyCriticalEndpointBound
        dsimp only [mass]
        ring
      _ ≤ Real.exp (1 / 4 : ℝ) *
          ((2 * conreyOuterMultiplier Y0 Y1 ^ 2 +
            2 * conreyInnerMultiplier Y0 Y1 ^ 2) * (2 * B + 2 * mass)) :=
        mul_le_mul_of_nonneg_right hleftExp (by positivity)
      _ ≤ Real.exp (1 / 4 : ℝ) * (1160 * (2 * B + 2 * mass)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff (by positivity))
          (Real.exp_nonneg _)
      _ ≤ Real.exp (1 / 4 : ℝ) *
          (1160 * ((2 * C + 32 * Real.sqrt Real.pi) * P * L ^ 6)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbracket (by norm_num)) (Real.exp_nonneg _)
      _ = _ := by unfold halfRangeCriticalConstant; ring
  have hY0pos : 0 < (Y0 : ℝ) := by exact_mod_cast (show 0 < Y0 by omega)
  have hcorePos : 0 < V ^ (2 / 5 : ℝ) := by positivity
  have htail : 1 / (Y0 : ℝ) ^ 3 ≤ 8 * V ^ (-6 / 5 : ℝ) := by
    calc
      _ ≤ 1 / (V ^ (2 / 5 : ℝ) / 2) ^ 3 :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by positivity) hY0L 3)
      _ = 8 / V ^ (6 / 5 : ℝ) := by
        rw [div_pow, div_div_eq_mul_div, ← Real.rpow_mul_natCast hV0.le]
        norm_num
      _ = _ := by
        rw [show (-6 / 5 : ℝ) = -(6 / 5) by ring, Real.rpow_neg hV0.le, div_eq_mul_inv]
  have hfar : ((10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3)) ^ 2 ≤
      ((80 / 3 : ℝ) * V ^ (-6 / 5 : ℝ)) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ (10 / 3 : ℝ) * (8 * V ^ (-6 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = _ := by ring
  have hpower : (V ^ (-6 / 5 : ℝ)) ^ 2 * P = V ^ (-29 / 20 : ℝ) := by
    dsimp only [P]
    rw [← Real.rpow_mul_natCast hV0.le, ← Real.rpow_add hV0]
    norm_num
  have hright : carlsonConreyRightEndpointBound Delta Y0 ≤
      halfRangeRightConstant * V ^ (-29 / 20 : ℝ) := by
    calc
      _ ≤ Real.exp 16 * ((80 / 3 : ℝ) * V ^ (-6 / 5 : ℝ)) ^ 2 * mass :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hrightExp hfar (sq_nonneg _) (Real.exp_nonneg _)) hmass0
      _ = halfRangeRightConstant * ((V ^ (-6 / 5 : ℝ)) ^ 2 * P) := by
        rw [hmass]
        unfold halfRangeRightConstant
        ring
      _ = _ := by rw [hpower]
  exact ⟨hcritical, hright⟩

end PrimeNumberTheorem.CarlsonZeroDensity
