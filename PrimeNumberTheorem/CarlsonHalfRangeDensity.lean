import PrimeNumberTheorem.CarlsonGeometricSummation
import PrimeNumberTheorem.ZeroDensityExponentCertificate

/-! Unconditional Carlson-type zero density with saving `1/400`.
The proof uses the actual two-scale mollifier, the proved half-length
critical mean square, strip interpolation, and the Carlson contour.
No other zero-density theorem or analytic gate is used. -/

open Filter Asymptotics

namespace PrimeNumberTheorem

open ZeroDensity

/-- The closed-threshold cumulative count, with actual zeta multiplicities. -/
theorem exists_eventually_carlson_halfRange_closedCount_le :
    ∃ K > (0 : ℝ), ∀ᶠ T : ℝ in atTop,
      (zeroDensityClosedCount (2 / 3) T : ℝ) ≤
        K * T ^ (8 / 9 - 1 / 400 : ℝ) * (Real.log T) ^ 6 := by
  obtain ⟨C, hC, hstep⟩ := exists_eventually_closedCount_twoThirds_step_le
  have hmono : Monotone (fun T => (zeroDensityClosedCount (2 / 3) T : ℝ)) := by
    intro U T hUT
    change (zeroDensityClosedCount (2 / 3) U : ℝ) ≤ (zeroDensityClosedCount (2 / 3) T : ℝ)
    exact_mod_cast zeroDensityClosedCount_mono_height (sigma := (2 / 3 : ℝ)) hUT
  have hstep' : ∀ᶠ U : ℝ in atTop,
      (zeroDensityClosedCount (2 / 3) ((9 / 8) * U) : ℝ) ≤
        (zeroDensityClosedCount (2 / 3) U : ℝ) +
          C * U ^ (8 / 9 - 1 / 400 : ℝ) * (1 + Real.log U) ^ 6 := by
    simpa only [div_mul_eq_mul_div] using hstep
  obtain ⟨K, hK, hbound⟩ := exists_eventually_powerLog_bound_of_geometric_step
    hmono (fun T => Nat.cast_nonneg _) (by norm_num : (1 : ℝ) < 9 / 8)
    (by norm_num : (0 : ℝ) < 8 / 9 - 1 / 400) hC hstep'
  refine ⟨64 * K, by positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (Real.exp 1)] with T hbound hT
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hl : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hT
  have hp : (1 + Real.log T) ^ 6 ≤ 64 * (Real.log T) ^ 6 := by
    have := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ 1 + Real.log T)
      (by linarith only [hl] : 1 + Real.log T ≤ 2 * Real.log T) 6
    simpa only [mul_pow, show (2 : ℝ) ^ 6 = 64 by norm_num] using this
  calc
    _ ≤ K * T ^ (8 / 9 - 1 / 400 : ℝ) * (1 + Real.log T) ^ 6 := hbound
    _ ≤ K * T ^ (8 / 9 - 1 / 400 : ℝ) * (64 * (Real.log T) ^ 6) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- The improved global theorem includes zeros exactly on `Re rho=2/3`. -/
theorem carlson_halfRange_closed_zeroDensity_isBigO :
    (fun T => (zeroDensityClosedCount (2 / 3) T : ℝ)) =O[atTop]
      (fun T => T ^ (8 / 9 - 1 / 400 : ℝ) * (Real.log T) ^ 6) := by
  obtain ⟨K, hK, hbound⟩ := exists_eventually_carlson_halfRange_closedCount_le
  refine IsBigO.of_bound K ?_
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with T hbound hT
  have hmodel : 0 ≤ T ^ (8 / 9 - 1 / 400 : ℝ) * (Real.log T) ^ 6 := by positivity
  have hcount0 : (0 : ℝ) ≤ (zeroDensityClosedCount (2 / 3) T : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hcount0,
    abs_of_nonneg hmodel, mul_assoc] using hbound

/-- Populate the existing strict-threshold density interface unconditionally. -/
theorem exists_carlson_halfRange_densityCertificate :
    Nonempty (ZeroDensityEventualMajorant (2 / 3) (8 / 9 - 1 / 400) 6) := by
  obtain ⟨K, hK, hbound⟩ := exists_eventually_carlson_halfRange_closedCount_le
  refine ⟨⟨K, hK.le, ?_⟩⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with T hbound hT
  have hmodel : 0 ≤ T ^ (8 / 9 - 1 / 400 : ℝ) * (Real.log T) ^ 6 := by positivity
  have hcount : (zeroDensityCount (2 / 3) T : ℝ) ≤ (zeroDensityClosedCount (2 / 3) T : ℝ) := by
    exact_mod_cast zeroDensityCount_le_closedCount (2 / 3) T
  simpa only [Real.norm_eq_abs, abs_of_nonneg hmodel, mul_assoc] using hcount.trans hbound

/-- Carlson-type improvement in the repository's original counting convention. -/
theorem carlson_halfRange_zeroDensity_isBigO :
    (fun T => (zeroDensityCount (2 / 3) T : ℝ)) =O[atTop]
      (fun T => T ^ (8 / 9 - 1 / 400 : ℝ) * (Real.log T) ^ 6) :=
  (Classical.choice exists_carlson_halfRange_densityCertificate).isBigO

end PrimeNumberTheorem
