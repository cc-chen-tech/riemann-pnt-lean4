import PrimeNumberTheorem.CarlsonConreyCriticalBoundaryReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact integer lengths and uniformly bounded two-scale reconstruction
coefficients for the half-range Carlson proof. -/

open Filter

namespace PrimeNumberTheorem.CarlsonZeroDensity

noncomputable def halfRangeCoreCutoff (V : ℝ) : ℕ := Nat.floor (V ^ (2 / 5 : ℝ))

noncomputable def halfRangeOuterCutoff (V : ℝ) : ℕ := Nat.floor (V ^ (9 / 20 : ℝ))

/-- Rounding retains half the core length and a logarithmic gap between the
two cutoffs.  All conditions hold at one eventual height threshold. -/
theorem eventually_halfRangeCutoff_conditions :
    ∀ᶠ V : ℝ in atTop,
      let Y0 := halfRangeCoreCutoff V
      let Y1 := halfRangeOuterCutoff V
      1 < V ∧ 2 ≤ Y0 ∧ Y0 < Y1 ∧
      (Y0 : ℝ) ≤ V ^ (2 / 5 : ℝ) ∧ (Y1 : ℝ) ≤ V ^ (9 / 20 : ℝ) ∧
      V ^ (2 / 5 : ℝ) / 2 ≤ (Y0 : ℝ) ∧
      Real.log V / 40 ≤ Real.log ((Y1 : ℝ) / (Y0 : ℝ)) ∧
      0 ≤ conreyOuterMultiplier Y0 Y1 ∧ conreyOuterMultiplier Y0 Y1 ≤ 18 ∧
      0 ≤ conreyInnerMultiplier Y0 Y1 ∧ conreyInnerMultiplier Y0 Y1 ≤ 16 := by
  have hcore : ∀ᶠ V : ℝ in atTop, (4 : ℝ) ≤ V ^ (2 / 5 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).eventually_ge_atTop 4
  have hgap : ∀ᶠ V : ℝ in atTop, (3 : ℝ) ≤ V ^ (1 / 20 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).eventually_ge_atTop 3
  have hlog : ∀ᶠ V : ℝ in atTop, 40 * Real.log 2 ≤ Real.log V :=
    Real.tendsto_log_atTop.eventually_ge_atTop (40 * Real.log 2)
  filter_upwards [hcore, hgap, hlog, eventually_ge_atTop (2 : ℝ)]
    with V hcore hgap hlog hV
  let Y0 := halfRangeCoreCutoff V
  let Y1 := halfRangeOuterCutoff V
  have hV1 : 1 < V := by linarith
  have hV0 : 0 < V := by linarith
  have hcorePos : 0 < V ^ (2 / 5 : ℝ) := by positivity
  have houterPos : 0 < V ^ (9 / 20 : ℝ) := by positivity
  have hpowOrder : V ^ (2 / 5 : ℝ) ≤ V ^ (9 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hV1.le (by norm_num)
  have hY0lower : V ^ (2 / 5 : ℝ) / 2 ≤ (Y0 : ℝ) := by
    have hfloor := Nat.sub_one_lt_floor (V ^ (2 / 5 : ℝ))
    change V ^ (2 / 5 : ℝ) / 2 ≤ (Nat.floor (V ^ (2 / 5 : ℝ)) : ℝ)
    linarith
  have hY1lower : V ^ (9 / 20 : ℝ) / 2 ≤ (Y1 : ℝ) := by
    have hfloor := Nat.sub_one_lt_floor (V ^ (9 / 20 : ℝ))
    change V ^ (9 / 20 : ℝ) / 2 ≤ (Nat.floor (V ^ (9 / 20 : ℝ)) : ℝ)
    linarith
  have hY0upper : (Y0 : ℝ) ≤ V ^ (2 / 5 : ℝ) := Nat.floor_le hcorePos.le
  have hY1upper : (Y1 : ℝ) ≤ V ^ (9 / 20 : ℝ) := Nat.floor_le houterPos.le
  have hY0 : 2 ≤ Y0 := by
    have : (2 : ℝ) ≤ Y0 := by linarith
    exact_mod_cast this
  have hgapMul : 3 * V ^ (2 / 5 : ℝ) ≤ V ^ (9 / 20 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hgap hcorePos.le
    rw [← Real.rpow_add hV0] at h
    norm_num at h
    exact h
  have hY01real : (Y0 : ℝ) < (Y1 : ℝ) := by nlinarith
  have hY01 : Y0 < Y1 := by exact_mod_cast hY01real
  have hY0pos : 0 < (Y0 : ℝ) := by exact_mod_cast (show 0 < Y0 by omega)
  have hY1pos : 0 < (Y1 : ℝ) := hY0pos.trans hY01real
  have hlogY0Upper : Real.log Y0 ≤ (2 / 5 : ℝ) * Real.log V := by
    simpa only [Real.log_rpow hV0] using Real.log_le_log hY0pos hY0upper
  have hlogY1Upper : Real.log Y1 ≤ (9 / 20 : ℝ) * Real.log V := by
    simpa only [Real.log_rpow hV0] using Real.log_le_log hY1pos hY1upper
  have hlogY1Lower : (9 / 20 : ℝ) * Real.log V - Real.log 2 ≤ Real.log Y1 := by
    have h := Real.log_le_log (div_pos houterPos (by norm_num)) hY1lower
    rw [Real.log_div houterPos.ne' (by norm_num), Real.log_rpow hV0] at h
    exact h
  have hlogGap : Real.log V / 40 ≤ Real.log ((Y1 : ℝ) / (Y0 : ℝ)) := by
    rw [Real.log_div hY1pos.ne' hY0pos.ne']
    linarith
  have hdenPos : 0 < Real.log ((Y1 : ℝ) / (Y0 : ℝ)) :=
    (div_pos (Real.log_pos hV1) (by norm_num)).trans_le hlogGap
  have hlogY0Nonneg : 0 ≤ Real.log Y0 :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y0 by omega))
  have hlogY1Nonneg : 0 ≤ Real.log Y1 :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y1 by omega))
  have houter : conreyOuterMultiplier Y0 Y1 ≤ 18 := by
    unfold conreyOuterMultiplier
    exact (div_le_iff₀ hdenPos).mpr (by linarith)
  have hinner : conreyInnerMultiplier Y0 Y1 ≤ 16 := by
    unfold conreyInnerMultiplier
    exact (div_le_iff₀ hdenPos).mpr (by linarith)
  exact ⟨hV1, hY0, hY01, hY0upper, hY1upper, hY0lower, hlogGap,
    div_nonneg hlogY1Nonneg hdenPos.le, houter,
    div_nonneg hlogY0Nonneg hdenPos.le, hinner⟩

end PrimeNumberTheorem.CarlsonZeroDensity
