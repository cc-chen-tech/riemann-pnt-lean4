import PrimeNumberTheorem.CarlsonHalfRangeUnconditional
import PrimeNumberTheorem.CarlsonConreyCriticalToInterior

/-! Unconditional interior energy on a fixed-ratio height interval.
The actual Gaussian grid can overshoot its right endpoint by half a window;
the interval below keeps every centre in the proved product-moment range.
This is not yet a zero-count theorem on the boundary line. -/

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem.CarlsonZeroDensity

/-- The exact centre range includes a possible half-window overshoot. -/
theorem carlsonGaussianCoverCenters_mem_bounds
    {Delta U V w : ℝ} (hDelta : 0 < Delta) (hUV : U ≤ V)
    (hw : w ∈ carlsonGaussianCoverCenters Delta U V) :
    U ≤ w ∧ w ≤ V + Delta / 2 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  have hjFloor : j ≤ Nat.floor ((V - U) / Delta) :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hjReal : (j : ℝ) ≤ (V - U) / Delta :=
    (show (j : ℝ) ≤ (Nat.floor ((V - U) / Delta) : ℝ) by exact_mod_cast hjFloor).trans
      (Nat.floor_le (div_nonneg (sub_nonneg.mpr hUV) hDelta.le))
  have hjMul : (j : ℝ) * Delta ≤ V - U := (le_div_iff₀ hDelta).mp hjReal
  constructor
  · have hterm : 0 ≤ ((j : ℝ) + 1 / 2) * Delta := by positivity
    linarith
  · nlinarith

/-- The sublinear Gaussian width eventually fits in the available centre
margin; the threshold is independent of the mollifier length. -/
theorem eventually_halfRangeDelta_pos_le_height :
    ∀ᶠ V : ℝ in atTop, 0 < 16 * V ^ (19 / 20 : ℝ) ∧
      16 * V ^ (19 / 20 : ℝ) ≤ V := by
  have hscale : Tendsto (fun V : ℝ => V ^ (1 / 20 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hscale.eventually (eventually_ge_atTop (16 : ℝ))] with V hV hpow
  have hV0 : 0 < V := by linarith
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ V ^ (1 / 20 : ℝ) * V ^ (19 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = V := by rw [← Real.rpow_add hV0]; norm_num

/-- Actual two-scale interior energy, with the critical product premises
discharged by the proved weak AFE and Gaussian polynomial mean value.
Only the integer mollifier length conditions remain as inputs. -/
theorem exists_eventually_halfRange_interior_moment_le_explicit :
    ∃ C > (0 : ℝ), ∀ᶠ V : ℝ in atTop, ∀ Y0 Y1 : ℕ,
      2 ≤ Y0 → Y0 < Y1 → (Y1 : ℝ) ≤ V ^ (9 / 20 : ℝ) →
      let Delta := 16 * V ^ (19 / 20 : ℝ)
      let B := C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6
      (∫ t : ℝ, (Icc (2 * V) (5 * V / 2)).indicator (fun t =>
        ‖twoScaleMollifiedZetaError Y0 Y1
          (((2 / 3 : ℝ) : ℂ) + I * (t : ℂ))‖ ^ 2) t) ≤
        Real.exp (1 / 4 : ℝ) *
          (((Nat.floor (((5 * V / 2) - 2 * V) / Delta) + 1 : ℕ) : ℝ) *
            (25 * carlsonConreyTwoThirdsLocalBound Delta Y0 Y1 B B)) := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_eventually_integral_gaussian_product_le_halfRange_powerLog
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmoment, eventually_halfRangeDelta_pos_le_height,
    eventually_ge_atTop (1 : ℝ)] with V hmoment hDelta hV
  intro Y0 Y1 hY0 hY01 hY1V
  dsimp only
  have hY1 : 2 ≤ Y1 := by omega
  have hY0V : (Y0 : ℝ) ≤ V ^ (9 / 20 : ℝ) :=
    (show (Y0 : ℝ) ≤ (Y1 : ℝ) by exact_mod_cast hY01.le).trans hY1V
  have hB : 0 ≤ C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6 := by positivity
  have hcentres : ∀ w ∈ carlsonGaussianCoverCenters
      (16 * V ^ (19 / 20 : ℝ)) (2 * V) (5 * V / 2),
      2 * V ≤ w ∧ w ≤ 3 * V := by
    intro w hw
    obtain ⟨hL, hU⟩ := carlsonGaussianCoverCenters_mem_bounds
      hDelta.1 (show 2 * V ≤ 5 * V / 2 by linarith) hw
    exact ⟨hL, by linarith [hDelta.2]⟩
  apply integral_indicator_Icc_norm_sq_twoScaleMollifiedZetaError_two_thirds_le_of_conrey_products
    hDelta.1 hY0 hY01 hB hB
  · intro w _
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaProduct
        (w := w) hDelta.1 hY0
  · intro w _
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      integrable_gaussian_norm_sq_linearLogSelbergMollifiedZetaProduct
        (w := w) hDelta.1 hY1
  · intro w hw
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      hmoment w Y0 (hcentres w hw).1 (hcentres w hw).2 hY0 hY0V
  · intro w hw
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      hmoment w Y1 (hcentres w hw).1 (hcentres w hw).2 hY1 hY1V

end PrimeNumberTheorem.CarlsonZeroDensity
