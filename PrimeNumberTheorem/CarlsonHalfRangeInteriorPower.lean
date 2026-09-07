import PrimeNumberTheorem.CarlsonHalfRangeEndpointBudget
import PrimeNumberTheorem.CarlsonHalfRangeLeftStrip

/-! Uniform power-log energy on the full left auxiliary strip.  This combines
the unconditional product theorem, integer length budgets, interpolation and
Gaussian covering.  It is not yet a zero-counting theorem. -/

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem.CarlsonZeroDensity

private theorem interpolate_power_bound {V C D x : ℝ}
    (hV : 1 ≤ V) (hC : 0 < C) (hD : 0 < D)
    (hx : x ∈ Icc (1 / 2 : ℝ) (2 / 3)) :
    (C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6) ^
        (1 - (x - 1 / 2) / (4 - 1 / 2)) *
      (D * V ^ (-29 / 20 : ℝ)) ^ ((x - 1 / 2) / (4 - 1 / 2)) ≤
      (max 1 C * max 1 D) *
        V ^ ((19 / 20 : ℝ) - (12 / 5 : ℝ) * ((x - 1 / 2) / (4 - 1 / 2))) *
        (1 + Real.log V) ^ 6 := by
  let q := (x - 1 / 2) / (4 - 1 / 2)
  let p := 1 - q
  let L := (1 + Real.log V) ^ 6
  have hV0 : 0 < V := by linarith
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hx.1) (by norm_num)
  have hq1 : q ≤ 1 := by dsimp only [q]; norm_num; linarith [hx.2]
  have hp0 : 0 ≤ p := by dsimp only [p]; linarith
  have hp1 : p ≤ 1 := by dsimp only [p]; linarith
  have hL1 : 1 ≤ L := one_le_pow₀ (by linarith [Real.log_nonneg hV])
  have hL0 : 0 ≤ L := by linarith
  have hCp : C ^ p ≤ max 1 C :=
    (Real.rpow_le_rpow hC.le (le_max_right 1 C) hp0).trans
      (Real.rpow_le_self_of_one_le (le_max_left 1 C) hp1)
  have hDq : D ^ q ≤ max 1 D :=
    (Real.rpow_le_rpow hD.le (le_max_right 1 D) hq0).trans
      (Real.rpow_le_self_of_one_le (le_max_left 1 D) hq1)
  have hLp : L ^ p ≤ L := Real.rpow_le_self_of_one_le hL1 hp1
  have hleft : (C * V ^ (19 / 20 : ℝ) * L) ^ p =
      C ^ p * V ^ ((19 / 20 : ℝ) * p) * L ^ p := by
    rw [Real.mul_rpow (by positivity) hL0,
      Real.mul_rpow hC.le (Real.rpow_nonneg hV0.le _), ← Real.rpow_mul hV0.le]
  have hright : (D * V ^ (-29 / 20 : ℝ)) ^ q =
      D ^ q * V ^ ((-29 / 20 : ℝ) * q) := by
    rw [Real.mul_rpow hD.le (Real.rpow_nonneg hV0.le _), ← Real.rpow_mul hV0.le]
  have hpower : V ^ ((19 / 20 : ℝ) * p) * V ^ ((-29 / 20 : ℝ) * q) =
      V ^ ((19 / 20 : ℝ) - (12 / 5 : ℝ) * q) := by
    rw [← Real.rpow_add hV0]
    congr 1
    dsimp only [p]
    ring
  change (C * V ^ (19 / 20 : ℝ) * L) ^ p *
    (D * V ^ (-29 / 20 : ℝ)) ^ q ≤ _
  calc
    _ = (C ^ p * D ^ q) *
        (V ^ ((19 / 20 : ℝ) * p) * V ^ ((-29 / 20 : ℝ) * q)) * L ^ p := by
      rw [hleft, hright]
      ring
    _ = (C ^ p * D ^ q) * V ^ ((19 / 20 : ℝ) - (12 / 5 : ℝ) * q) * L ^ p := by
      rw [hpower]
    _ ≤ (max 1 C * max 1 D) *
        V ^ ((19 / 20 : ℝ) - (12 / 5 : ℝ) * q) * L := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hCp hDq (Real.rpow_nonneg hD.le _) (by positivity))
          (Real.rpow_nonneg hV0.le _)) hLp
        (Real.rpow_nonneg hL0 _) (by positivity)

private theorem cover_count_le {V : ℝ} (hV : 0 < V)
    (hDelta : 16 * V ^ (19 / 20 : ℝ) ≤ V) :
    ((Nat.floor (((5 * V / 2) - 2 * V) / (16 * V ^ (19 / 20 : ℝ))) + 1 : ℕ) : ℝ) ≤
      (3 / 32 : ℝ) * V ^ (1 / 20 : ℝ) := by
  let Delta := 16 * V ^ (19 / 20 : ℝ)
  have hDelta0 : 0 < Delta := by dsimp only [Delta]; positivity
  have hratio : V / V ^ (19 / 20 : ℝ) = V ^ (1 / 20 : ℝ) := by
    rw [show (1 / 20 : ℝ) = 1 - 19 / 20 by ring, Real.rpow_sub hV, Real.rpow_one]
  rw [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ (((5 * V / 2) - 2 * V) / Delta) + 1 := by
      have hf := Nat.floor_le
        (show 0 ≤ ((5 * V / 2) - 2 * V) / Delta from
          div_nonneg (by linarith) hDelta0.le)
      change ((Nat.floor (((5 * V / 2) - 2 * V) / Delta) : ℕ) : ℝ) + 1 ≤ _
      linarith
    _ ≤ ((3 / 2 : ℝ) * V) / Delta := by
      apply (le_div_iff₀ hDelta0).mpr
      rw [add_mul, div_mul_cancel₀ _ hDelta0.ne', one_mul]
      linarith
    _ = (3 / 32 : ℝ) * (V / V ^ (19 / 20 : ℝ)) := by
      dsimp only [Delta]
      ring
    _ = _ := by rw [hratio]

/-- A single constant and height threshold work for every line in the closed
auxiliary strip.  Both lengths are the specified integer floors. -/
theorem exists_eventually_halfRange_leftStrip_moment_le_powerLog :
    ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
      ∀ x ∈ Icc (1 / 2 : ℝ) (2 / 3),
      (∫ t : ℝ, (Icc (2 * V) (5 * V / 2)).indicator (fun t =>
        ‖twoScaleMollifiedZetaError (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((x : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
        K * V ^ (1 - (12 / 5 : ℝ) * ((x - 1 / 2) / (4 - 1 / 2))) *
          (1 + Real.log V) ^ 6 := by
  obtain ⟨C, hC, hmoment⟩ := exists_eventually_halfRange_leftStrip_moment_le_explicit
  let A := max 1 (halfRangeCriticalConstant C) * max 1 halfRangeRightConstant
  let K := (75 / 32 : ℝ) * Real.exp (1 / 4 : ℝ) * A
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  filter_upwards [hmoment, eventually_halfRangeCutoff_conditions,
    eventually_halfRange_endpoint_bounds hC.le, eventually_halfRangeDelta_pos_le_height]
    with V hmoment hparams hendpoints hDelta
  obtain ⟨hV1, hY0, hY01, hY0U, hY1U, _⟩ := hparams
  intro x hx
  let Y0 := halfRangeCoreCutoff V
  let Y1 := halfRangeOuterCutoff V
  let Delta := 16 * V ^ (19 / 20 : ℝ)
  let B := C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6
  let q := (x - 1 / 2) / (4 - 1 / 2)
  let L := (1 + Real.log V) ^ 6
  have hV0 : 0 < V := by linarith
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hx.1) (by norm_num)
  have hp0 : 0 ≤ 1 - q := by dsimp only [q]; norm_num; linarith [hx.2]
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hleft0 : 0 ≤ carlsonConreyCriticalEndpointBound Delta Y0 Y1 B B := by
    unfold carlsonConreyCriticalEndpointBound
    positivity
  have hright0 : 0 ≤ carlsonConreyRightEndpointBound Delta Y0 := by
    unfold carlsonConreyRightEndpointBound
    positivity
  have hlocal : carlsonConreyLeftStripLocalBound x Delta Y0 Y1 B B ≤
      A * V ^ ((19 / 20 : ℝ) - (12 / 5 : ℝ) * q) * L := by
    apply (mul_le_mul
      (Real.rpow_le_rpow hleft0 hendpoints.1 hp0)
      (Real.rpow_le_rpow hright0 hendpoints.2 hq0)
      (Real.rpow_nonneg hright0 _)
      (Real.rpow_nonneg (show 0 ≤ halfRangeCriticalConstant C *
        V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6 from
          mul_nonneg (mul_nonneg (halfRangeCriticalConstant_pos hC.le).le
            (Real.rpow_nonneg hV0.le _)) (by positivity)) _)).trans
    exact interpolate_power_bound hV1.le
      (halfRangeCriticalConstant_pos hC.le) halfRangeRightConstant_pos hx
  have hcount := cover_count_le hV0 hDelta.2
  have hpower : V ^ (1 / 20 : ℝ) *
      V ^ ((19 / 20 : ℝ) - (12 / 5 : ℝ) * q) =
      V ^ (1 - (12 / 5 : ℝ) * q) := by
    rw [← Real.rpow_add hV0]
    congr 1
    ring
  calc
    _ ≤ Real.exp (1 / 4 : ℝ) *
        (((Nat.floor (((5 * V / 2) - 2 * V) / Delta) + 1 : ℕ) : ℝ) *
          (25 * carlsonConreyLeftStripLocalBound x Delta Y0 Y1 B B)) :=
      hmoment Y0 Y1 hY0 hY01 hY1U x hx
    _ ≤ Real.exp (1 / 4 : ℝ) *
        (((Nat.floor (((5 * V / 2) - 2 * V) / Delta) + 1 : ℕ) : ℝ) *
          (25 * (A * V ^ ((19 / 20 : ℝ) - (12 / 5 : ℝ) * q) * L))) := by
      gcongr
    _ ≤ Real.exp (1 / 4 : ℝ) *
        (((3 / 32 : ℝ) * V ^ (1 / 20 : ℝ)) *
          (25 * (A * V ^ ((19 / 20 : ℝ) - (12 / 5 : ℝ) * q) * L))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcount (by dsimp only [L]; positivity))
        (Real.exp_nonneg _)
    _ = K * (V ^ (1 / 20 : ℝ) *
        V ^ ((19 / 20 : ℝ) - (12 / 5 : ℝ) * q)) * L := by dsimp only [K]; ring
    _ = _ := by rw [hpower]

end PrimeNumberTheorem.CarlsonZeroDensity
