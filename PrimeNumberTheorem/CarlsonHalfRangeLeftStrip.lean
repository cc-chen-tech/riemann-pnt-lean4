import PrimeNumberTheorem.CarlsonGaussianLeftStrip
import PrimeNumberTheorem.CarlsonHalfRangeInterior

/-! Uniform ordinary-error energy for every left-strip line.  All critical
product inputs are supplied by the unconditional half-range theorem. -/

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem.CarlsonZeroDensity

/-- The exact closed-strip interpolation expression, retaining both integer
lengths and both endpoint constants. -/
noncomputable def carlsonConreyLeftStripLocalBound
    (x Delta : ℝ) (Y0 Y1 : ℕ) (C0 C1 : ℝ) : ℝ :=
  carlsonConreyCriticalEndpointBound Delta Y0 Y1 C0 C1 ^
      (1 - (x - 1 / 2) / (4 - 1 / 2)) *
    carlsonConreyRightEndpointBound Delta Y0 ^ ((x - 1 / 2) / (4 - 1 / 2))

private theorem localBound_nonneg {x Delta C0 C1 : ℝ} {Y0 Y1 : ℕ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    0 ≤ carlsonConreyLeftStripLocalBound x Delta Y0 Y1 C0 C1 := by
  unfold carlsonConreyLeftStripLocalBound carlsonConreyCriticalEndpointBound
    carlsonConreyRightEndpointBound
  positivity

/-- The constant and eventual threshold precede both the line and length
choices.  No AFE or critical-moment premise remains. -/
theorem exists_eventually_halfRange_leftStrip_moment_le_explicit :
    ∃ C > (0 : ℝ), ∀ᶠ V : ℝ in atTop, ∀ Y0 Y1 : ℕ,
      2 ≤ Y0 → Y0 < Y1 → (Y1 : ℝ) ≤ V ^ (9 / 20 : ℝ) →
      ∀ x ∈ Icc (1 / 2 : ℝ) (2 / 3),
      let Delta := 16 * V ^ (19 / 20 : ℝ)
      let B := C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6
      (∫ t : ℝ, (Icc (2 * V) (5 * V / 2)).indicator (fun t =>
        ‖twoScaleMollifiedZetaError Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
        Real.exp (1 / 4 : ℝ) *
          (((Nat.floor (((5 * V / 2) - 2 * V) / Delta) + 1 : ℕ) : ℝ) *
            (25 * carlsonConreyLeftStripLocalBound x Delta Y0 Y1 B B)) := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_eventually_integral_gaussian_product_le_halfRange_powerLog
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmoment, eventually_halfRangeDelta_pos_le_height,
    eventually_ge_atTop (1 : ℝ)] with V hmoment hDelta hV
  intro Y0 Y1 hY0 hY01 hY1V x hx
  dsimp only
  let Delta := 16 * V ^ (19 / 20 : ℝ)
  let B := C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6
  have hY0one : 1 ≤ Y0 := by omega
  have hY1 : 2 ≤ Y1 := by omega
  have hY0V : (Y0 : ℝ) ≤ V ^ (9 / 20 : ℝ) :=
    (show (Y0 : ℝ) ≤ (Y1 : ℝ) by exact_mod_cast hY01.le).trans hY1V
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  apply integral_indicator_Icc_twoScaleError_leftStrip_le
    hDelta.1 hY0one hY01 hx (localBound_nonneg hB hB)
  intro w hw
  obtain ⟨hwL, hwU'⟩ := carlsonGaussianCoverCenters_mem_bounds
    hDelta.1 (show 2 * V ≤ 5 * V / 2 by linarith) hw
  have hwU : w ≤ 3 * V := by linarith [hDelta.2]
  have hProdInt (X : ℕ) (hX : 2 ≤ X) :
      Integrable fun t : ℝ => carlsonGaussianWeight Delta w t *
        ‖linearLogSelbergMollifiedZetaProduct X
          (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaProduct
        (w := w) hDelta.1 hX
  have hProdBound (X : ℕ) (hX : 2 ≤ X) (hXV : (X : ℝ) ≤ V ^ (9 / 20 : ℝ)) :
      (∫ t : ℝ, carlsonGaussianWeight Delta w t *
        ‖linearLogSelbergMollifiedZetaProduct X
          (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ B := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      hmoment w X hwL hwU hX hXV
  have hcritical := norm_sq_carlsonGaussianPoleFreeLpValue_half_le_of_conrey_product_components
    hDelta.1 hY0 hY01 (hProdInt Y0 hY0) (hProdInt Y1 hY1)
    (hProdBound Y0 hY0 hY0V) (hProdBound Y1 hY1 hY1V)
  have hcriticalTotal :
      ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1 hDelta.1 hY0one hY01
        ((1 / 2 : ℝ) : ℂ)‖ ^ 2 ≤ carlsonConreyCriticalEndpointBound Delta Y0 Y1 B B := by
    rw [carlsonGaussianPoleFreeLpValueTotal_eq hDelta.1 hY0one hY01
      (by norm_num : (((1 / 2 : ℝ) : ℂ).re) ∈ Icc (1 / 2 : ℝ) 4)]
    simpa only [carlsonConreyCriticalEndpointBound] using hcritical
  have hrightTotal :
      ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1 hDelta.1 hY0one hY01
        (4 : ℂ)‖ ^ 2 ≤ carlsonConreyRightEndpointBound Delta Y0 := by
    rw [carlsonGaussianPoleFreeLpValueTotal_eq hDelta.1 hY0one hY01
      (by norm_num : (4 : ℂ).re ∈ Icc (1 / 2 : ℝ) 4)]
    exact norm_sq_carlsonGaussianPoleFreeLpValue_four_le hDelta.1 hY0one hY01
  exact norm_sq_carlsonGaussianPoleFreeLpValueTotal_le_of_endpoint_bounds
    hDelta.1 hY0one hY01 ⟨hx.1, by linarith [hx.2]⟩ hcriticalTotal hrightTotal

end PrimeNumberTheorem.CarlsonZeroDensity
