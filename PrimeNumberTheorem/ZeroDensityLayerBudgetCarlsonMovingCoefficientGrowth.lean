import PrimeNumberTheorem.CarlsonAsymptotic
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingBalancedDecay

/-!
# Elementary denominator control for moving Carlson coefficients

For the nondegenerate moving strip
`(1 - 2 * delta, 1 - delta]`, the explicit fixed-`sigma` Carlson
coefficient is evaluated at `sigma = 1 - 2 * delta`.  Its potentially small
denominators reduce to

* `2 ^ (4 * delta) - 1`;
* `4 * delta`;
* `1 - 2 ^ (-1 / 2 + 2 * delta)`.

This file proves the elementary quantitative bounds needed before those
terms are assembled into a polynomial coefficient envelope.  It deliberately
does not apply the fixed-`sigma` `IsBigO` theorem along a moving `sigma`.
-/

namespace PrimeNumberTheorem

open Filter

/-- The power denominator in the moving Carlson coefficient is at least
linear in the strip gap. -/
theorem carlsonMovingPowerGap_lower {delta : ℝ} (hdelta : 0 ≤ delta) :
    4 * delta * Real.log 2 ≤ (2 : ℝ) ^ (4 * delta) - 1 := by
  have hExp := Real.add_one_le_exp (Real.log 2 * (4 * delta))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- The power denominator is positive for a positive moving gap. -/
theorem carlsonMovingPowerGap_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < (2 : ℝ) ^ (4 * delta) - 1 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlower : 0 < 4 * delta * Real.log 2 := by positivity
  exact hlower.trans_le (carlsonMovingPowerGap_lower hdelta.le)

/-- Reciprocal form of `carlsonMovingPowerGap_lower`. -/
theorem carlsonMovingPowerGap_inv_le {delta : ℝ} (hdelta : 0 < delta) :
    ((2 : ℝ) ^ (4 * delta) - 1)⁻¹ ≤
      (4 * delta * Real.log 2)⁻¹ := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlower : 0 < 4 * delta * Real.log 2 := by positivity
  exact inv_anti₀ hlower (carlsonMovingPowerGap_lower hdelta.le)

/-- A fixed positive lower bound for the negative-exponent denominator. -/
noncomputable def carlsonQuarterRpowGap : ℝ :=
  1 - (2 : ℝ) ^ (-1 / 4 : ℝ)

theorem carlsonQuarterRpowGap_pos : 0 < carlsonQuarterRpowGap := by
  dsimp [carlsonQuarterRpowGap]
  exact sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

/-- On `delta ≤ 1/8`, the moving negative-exponent denominator stays
uniformly above the fixed quarter-power gap. -/
theorem carlsonQuarterRpowGap_le_moving {delta : ℝ}
    (hdelta : delta ≤ 1 / 8) :
    carlsonQuarterRpowGap ≤
      1 - (2 : ℝ) ^ (-1 / 2 + 2 * delta) := by
  have hexponent : (-1 / 2 : ℝ) + 2 * delta ≤ -1 / 4 := by
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) hexponent
  dsimp [carlsonQuarterRpowGap]
  linarith

/-- Reciprocal control for the negative-exponent denominator. -/
theorem carlsonMovingNegativePowerGap_inv_le {delta : ℝ}
    (hdelta : delta ≤ 1 / 8) :
    (1 - (2 : ℝ) ^ (-1 / 2 + 2 * delta))⁻¹ ≤
      carlsonQuarterRpowGap⁻¹ :=
  inv_anti₀ carlsonQuarterRpowGap_pos
    (carlsonQuarterRpowGap_le_moving hdelta)

/-- The distance from the moving Carlson line to `1/2` is uniformly bounded
below when `delta ≤ 1/8`. -/
theorem carlsonMovingHalfGap_inv_le_four {delta : ℝ}
    (hdelta : delta ≤ 1 / 8) :
    ((1 - 2 * delta) - 1 / 2)⁻¹ ≤ 4 := by
  have hgap : (1 / 4 : ℝ) ≤ (1 - 2 * delta) - 1 / 2 := by
    linarith
  have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hgap
  norm_num at hinv ⊢
  exact hinv

/-- The distance from the moving Carlson line to `1` is exactly `4 delta`. -/
theorem carlsonMovingRightGap_eq {delta : ℝ} :
    2 - 2 * (1 - 2 * delta) = 4 * delta := by
  ring

end PrimeNumberTheorem
