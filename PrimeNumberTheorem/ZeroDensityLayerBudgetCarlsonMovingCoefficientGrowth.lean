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

/-- Public replica of the `sigma`-dependent sharp coefficient used internally
by `CarlsonAsymptotic`, specialized to `sigma = 1 - 2 * delta`.

The original coefficient is private to that file, so this declaration does
not claim an external Lean equality to it.  It records the exact displayed
formula needed by a future public pointwise Carlson certificate. -/
noncomputable def carlsonMovingExplicitSharpCoefficient
    (A delta : ℝ) : ℝ :=
  2 * (2 + 1 / (1 / 2 - 2 * delta)) *
      (9 * Real.exp 4 / ((2 : ℝ) ^ (4 * delta) - 1) +
        6 * Real.exp 4) +
    16 * Real.pi * (2 + 1 / (4 * delta)) *
      (144 * Real.exp 8 / ((2 : ℝ) ^ (4 * delta) - 1)) +
    4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi)) *
      ((1 + Real.exp 4 / (4 * delta)) *
        (1 - (2 : ℝ) ^ (-1 / 2 + 2 * delta))⁻¹)

/-- Explicit polynomial envelope for the moving sharp ambient coefficient.
Its worst term is quadratic in `delta⁻¹`. -/
noncomputable def carlsonMovingSharpCoefficientEnvelope
    (A delta : ℝ) : ℝ :=
  12 *
      (9 * Real.exp 4 / (4 * delta * Real.log 2) +
        6 * Real.exp 4) +
    16 * Real.pi * (2 + 1 / (4 * delta)) *
      (144 * Real.exp 8 / (4 * delta * Real.log 2)) +
    4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi)) *
      ((1 + Real.exp 4 / (4 * delta)) *
        carlsonQuarterRpowGap⁻¹)

theorem carlsonMovingExplicitSharpCoefficient_le_envelope
    {A delta : ℝ} (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8) :
    carlsonMovingExplicitSharpCoefficient A delta ≤
      carlsonMovingSharpCoefficientEnvelope A delta := by
  have hhalf := carlsonMovingHalfGap_inv_le_four hdeltaUpper
  have hpower := carlsonMovingPowerGap_inv_le hdelta
  have hnegative := carlsonMovingNegativePowerGap_inv_le hdeltaUpper
  have hpowerPos := carlsonMovingPowerGap_pos hdelta
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlinearPos : 0 < 4 * delta * Real.log 2 := by positivity
  have hrightPos : 0 < 4 * delta := by positivity
  have hfirstFactor :
      2 * (2 + 1 / (1 / 2 - 2 * delta)) ≤ 12 := by
    have hrewrite :
        (1 / 2 - 2 * delta : ℝ) = (1 - 2 * delta) - 1 / 2 := by
      ring
    have hinv : (1 / 2 - 2 * delta)⁻¹ ≤ 4 := by
      rw [hrewrite]
      exact hhalf
    rw [one_div]
    nlinarith
  have hpowerBracket :
      9 * Real.exp 4 / ((2 : ℝ) ^ (4 * delta) - 1) +
          6 * Real.exp 4 ≤
        9 * Real.exp 4 / (4 * delta * Real.log 2) +
          6 * Real.exp 4 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hmul := mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ 9 * Real.exp 4 by positivity)
    nlinarith
  have hfirstBracketNonneg :
      0 ≤ 9 * Real.exp 4 / ((2 : ℝ) ^ (4 * delta) - 1) +
        6 * Real.exp 4 := by positivity
  have hfirst :
      2 * (2 + 1 / (1 / 2 - 2 * delta)) *
          (9 * Real.exp 4 / ((2 : ℝ) ^ (4 * delta) - 1) +
            6 * Real.exp 4) ≤
        12 *
          (9 * Real.exp 4 / (4 * delta * Real.log 2) +
            6 * Real.exp 4) :=
    (mul_le_mul_of_nonneg_right hfirstFactor hfirstBracketNonneg).trans
      (mul_le_mul_of_nonneg_left hpowerBracket (by norm_num))
  have hsecondBracket :
      144 * Real.exp 8 / ((2 : ℝ) ^ (4 * delta) - 1) ≤
        144 * Real.exp 8 / (4 * delta * Real.log 2) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hpower (by positivity)
  have hsecondFactorNonneg :
      0 ≤ 16 * Real.pi * (2 + 1 / (4 * delta)) := by
    positivity
  have hsecond :
      16 * Real.pi * (2 + 1 / (4 * delta)) *
          (144 * Real.exp 8 / ((2 : ℝ) ^ (4 * delta) - 1)) ≤
        16 * Real.pi * (2 + 1 / (4 * delta)) *
          (144 * Real.exp 8 / (4 * delta * Real.log 2)) :=
    mul_le_mul_of_nonneg_left hsecondBracket hsecondFactorNonneg
  have hthirdInnerNonneg :
      0 ≤ 1 + Real.exp 4 / (4 * delta) := by positivity
  have hthirdInner :
      (1 + Real.exp 4 / (4 * delta)) *
          (1 - (2 : ℝ) ^ (-1 / 2 + 2 * delta))⁻¹ ≤
        (1 + Real.exp 4 / (4 * delta)) *
          carlsonQuarterRpowGap⁻¹ :=
    mul_le_mul_of_nonneg_left hnegative hthirdInnerNonneg
  have hthirdFactorNonneg :
      0 ≤ 4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi)) := by
    positivity
  have hthird :
      4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi)) *
          ((1 + Real.exp 4 / (4 * delta)) *
            (1 - (2 : ℝ) ^ (-1 / 2 + 2 * delta))⁻¹) ≤
        4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi)) *
          ((1 + Real.exp 4 / (4 * delta)) *
            carlsonQuarterRpowGap⁻¹) :=
    mul_le_mul_of_nonneg_left hthirdInner hthirdFactorNonneg
  unfold carlsonMovingExplicitSharpCoefficient
  exact add_le_add (add_le_add hfirst hsecond) hthird

/-- Add an arbitrary fixed, `delta`-independent part to the explicit moving
sharp coefficient.  This isolates the only coefficient growth that matters
for the moving-strip logarithmic margin. -/
noncomputable def carlsonMovingExplicitCoefficient
    (fixedPart A delta : ℝ) : ℝ :=
  fixedPart + carlsonMovingExplicitSharpCoefficient A delta

noncomputable def carlsonMovingCoefficientEnvelope
    (fixedPart A delta : ℝ) : ℝ :=
  fixedPart + carlsonMovingSharpCoefficientEnvelope A delta

theorem carlsonMovingExplicitCoefficient_le_envelope
    {fixedPart A delta : ℝ}
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8) :
    carlsonMovingExplicitCoefficient fixedPart A delta ≤
      carlsonMovingCoefficientEnvelope fixedPart A delta := by
  unfold carlsonMovingExplicitCoefficient carlsonMovingCoefficientEnvelope
  exact add_le_add_right
    (carlsonMovingExplicitSharpCoefficient_le_envelope
      hdelta hdeltaUpper) fixedPart

/-- The constant term in the Laurent expansion of the moving sharp
coefficient envelope. -/
noncomputable def carlsonMovingSharpCoefficientConstantTerm (A : ℝ) : ℝ :=
  72 * Real.exp 4 +
    4 * ((A + 4) ^ 2 * (1 + 4 * Real.pi)) *
      carlsonQuarterRpowGap⁻¹

/-- The coefficient of `delta⁻¹` in the moving sharp coefficient envelope. -/
noncomputable def carlsonMovingSharpCoefficientLinearTerm (A : ℝ) : ℝ :=
  27 * Real.exp 4 / Real.log 2 +
    1152 * Real.pi * Real.exp 8 / Real.log 2 +
    ((A + 4) ^ 2 * (1 + 4 * Real.pi)) *
      carlsonQuarterRpowGap⁻¹ * Real.exp 4

/-- The coefficient of `delta⁻²` in the moving sharp coefficient envelope. -/
noncomputable def carlsonMovingSharpCoefficientQuadraticTerm : ℝ :=
  144 * Real.pi * Real.exp 8 / Real.log 2

/-- A fixed constant dominating all three Laurent terms once `delta ≤ 1`. -/
noncomputable def carlsonMovingSharpCoefficientQuadraticConstant
    (A : ℝ) : ℝ :=
  carlsonMovingSharpCoefficientConstantTerm A +
    carlsonMovingSharpCoefficientLinearTerm A +
    carlsonMovingSharpCoefficientQuadraticTerm

theorem carlsonMovingSharpCoefficientEnvelope_laurent
    {A delta : ℝ} (hdelta : delta ≠ 0) :
    carlsonMovingSharpCoefficientEnvelope A delta =
      carlsonMovingSharpCoefficientConstantTerm A +
        carlsonMovingSharpCoefficientLinearTerm A / delta +
        carlsonMovingSharpCoefficientQuadraticTerm / delta ^ 2 := by
  have hlogTwo : Real.log 2 ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  unfold carlsonMovingSharpCoefficientEnvelope
    carlsonMovingSharpCoefficientConstantTerm
    carlsonMovingSharpCoefficientLinearTerm
    carlsonMovingSharpCoefficientQuadraticTerm
  field_simp
  ring

theorem carlsonMovingSharpCoefficientConstantTerm_nonneg (A : ℝ) :
    0 ≤ carlsonMovingSharpCoefficientConstantTerm A := by
  unfold carlsonMovingSharpCoefficientConstantTerm
  have hquarterInv : 0 ≤ carlsonQuarterRpowGap⁻¹ :=
    (inv_pos.mpr carlsonQuarterRpowGap_pos).le
  positivity

theorem carlsonMovingSharpCoefficientLinearTerm_nonneg (A : ℝ) :
    0 ≤ carlsonMovingSharpCoefficientLinearTerm A := by
  unfold carlsonMovingSharpCoefficientLinearTerm
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquarterInv : 0 ≤ carlsonQuarterRpowGap⁻¹ :=
    (inv_pos.mpr carlsonQuarterRpowGap_pos).le
  positivity

theorem carlsonMovingSharpCoefficientQuadraticTerm_nonneg :
    0 ≤ carlsonMovingSharpCoefficientQuadraticTerm := by
  unfold carlsonMovingSharpCoefficientQuadraticTerm
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- Quantitative polynomial growth: the explicit moving sharp coefficient
envelope is bounded by a fixed constant times `delta⁻²`. -/
theorem carlsonMovingSharpCoefficientEnvelope_le_quadratic
    {A delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    carlsonMovingSharpCoefficientEnvelope A delta ≤
      carlsonMovingSharpCoefficientQuadraticConstant A / delta ^ 2 := by
  have hInvOne : 1 ≤ delta⁻¹ := by
    exact (one_le_inv₀ hdelta).2 hdeltaOne
  have hInvNonneg : 0 ≤ delta⁻¹ := (inv_pos.mpr hdelta).le
  have hInvLeSq : delta⁻¹ ≤ delta⁻¹ ^ 2 := by
    nlinarith
  have hOneLeSq : 1 ≤ delta⁻¹ ^ 2 := by
    nlinarith
  have hconstant :=
    carlsonMovingSharpCoefficientConstantTerm_nonneg A
  have hlinear :=
    carlsonMovingSharpCoefficientLinearTerm_nonneg A
  rw [carlsonMovingSharpCoefficientEnvelope_laurent hdelta.ne']
  unfold carlsonMovingSharpCoefficientQuadraticConstant
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ← inv_pow]
  calc
    carlsonMovingSharpCoefficientConstantTerm A +
          carlsonMovingSharpCoefficientLinearTerm A * delta⁻¹ +
          carlsonMovingSharpCoefficientQuadraticTerm * delta⁻¹ ^ 2 ≤
        carlsonMovingSharpCoefficientConstantTerm A * delta⁻¹ ^ 2 +
          carlsonMovingSharpCoefficientLinearTerm A * delta⁻¹ ^ 2 +
          carlsonMovingSharpCoefficientQuadraticTerm * delta⁻¹ ^ 2 := by
      exact add_le_add
        (add_le_add
          (by simpa using
            mul_le_mul_of_nonneg_left hOneLeSq hconstant)
          (mul_le_mul_of_nonneg_left hInvLeSq hlinear))
        le_rfl
    _ = (carlsonMovingSharpCoefficientConstantTerm A +
          carlsonMovingSharpCoefficientLinearTerm A +
          carlsonMovingSharpCoefficientQuadraticTerm) *
          delta⁻¹ ^ 2 := by ring

/-- Logarithmic majorant corresponding exactly to `C * delta⁻²`. -/
noncomputable def carlsonMovingQuadraticLogEnvelope
    (C : ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.log C + 2 * Real.log (delta m)⁻¹

theorem exp_carlsonMovingQuadraticLogEnvelope
    {C delta : ℝ} (hC : 0 < C) (hdelta : 0 < delta) :
    Real.exp (Real.log C + 2 * Real.log delta⁻¹) =
      C / delta ^ 2 := by
  rw [Real.exp_add, Real.exp_log hC]
  have hInv : 0 < delta⁻¹ := inv_pos.mpr hdelta
  rw [show 2 * Real.log delta⁻¹ =
      Real.log delta⁻¹ + Real.log delta⁻¹ by ring]
  rw [Real.exp_add, Real.exp_log hInv]
  field_simp

/-- The precise remaining growth condition for a quadratic Carlson
coefficient: its `2 log(1 / delta)` cost must fit inside half of the balanced
strip gap. -/
def IsCarlsonMovingQuadraticLogGap
    (delta : ℕ → ℝ) : Prop :=
  Tendsto
    (fun m =>
      delta m / 2 * Real.log (m : ℝ) -
        2 * Real.log (delta m)⁻¹)
    atTop atTop

/-- Any fixed multiple of `delta⁻²` is admissible once the quadratic
logarithmic gap tends to infinity. -/
theorem carlsonMovingQuadraticLogEnvelope_admissible
    {C : ℝ} {delta : ℕ → ℝ}
    (hgap : IsCarlsonMovingQuadraticLogGap delta) :
    IsCarlsonMovingBalancedCoefficientAdmissible delta
      (carlsonMovingQuadraticLogEnvelope C delta) := by
  have hshift :=
    tendsto_atTop_add_const_right atTop (-Real.log C) hgap
  apply hshift.congr'
  filter_upwards with m
  unfold carlsonMovingBalancedCoefficientLogMargin
    carlsonMovingQuadraticLogEnvelope
  ring

/-- The balanced strip ratio still tends to zero after inserting any
quadratic moving Carlson coefficient. -/
theorem tendsto_carlsonMovingQuadraticCoefficientRatio_zero
    {alpha C : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 ≤ alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 2 ∧
        128 * alpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogGap delta) :
    Tendsto
      (carlsonMovingBalancedCoefficientRatio alpha delta
        (carlsonMovingQuadraticLogEnvelope C delta))
      atTop (nhds 0) :=
  tendsto_carlsonMovingBalancedCoefficientRatio_zero
    halpha hdelta
      (carlsonMovingQuadraticLogEnvelope_admissible hgap)

end PrimeNumberTheorem
