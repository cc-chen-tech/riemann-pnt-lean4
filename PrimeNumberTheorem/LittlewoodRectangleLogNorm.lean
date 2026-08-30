import PrimeNumberTheorem.LittlewoodRectangle

/-! Detector-independent cancellation of the corner terms in Littlewood's
rectangle.  The signs are bottom minus top plus right minus left. -/

open Complex Set
open scoped Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

noncomputable def rectangleLittlewoodFourEdges
    (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℝ :=
  (∫ x in x0..x1, ((((x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ)) *
    logDeriv f ((x : ℂ) + (y0 : ℂ) * I))).im) -
  (∫ x in x0..x1, ((((x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ)) *
    logDeriv f ((x : ℂ) + (y1 : ℂ) * I))).im) +
  (∫ y in y0..y1, ((((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
    logDeriv f ((x1 : ℂ) + (y : ℂ) * I))).re) -
  (∫ y in y0..y1, ((((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
    logDeriv f ((x0 : ℂ) + (y : ℂ) * I))).re)

noncomputable def rectangleLittlewoodLogNormForm
    (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℝ :=
  (∫ x in x0..x1, (x - x0) * (logDeriv f ((x : ℂ) + (y0 : ℂ) * I)).im) -
  (∫ x in x0..x1, (x - x0) * (logDeriv f ((x : ℂ) + (y1 : ℂ) * I)).im) +
  (x1 - x0) * (∫ y in y0..y1, (logDeriv f ((x1 : ℂ) + (y : ℂ) * I)).re) +
  (∫ y in y0..y1, Real.log ‖f ((x0 : ℂ) + (y : ℂ) * I)‖) -
  (∫ y in y0..y1, Real.log ‖f ((x1 : ℂ) + (y : ℂ) * I)‖)

/-- Four oriented weighted edge integrals equal the endpoint-cancelled form.
Degenerate rectangles are allowed; nonvanishing is explicit on every edge. -/
theorem rectangleLittlewoodFourEdges_eq_logNormForm
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hx : x0 ≤ x1) (hy : y0 ≤ y1)
    (hf : AnalyticOnNhd ℂ f (Icc x0 x1 ×ℂ Icc y0 y1))
    (hleft : ∀ y ∈ Icc y0 y1, f ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Icc y0 y1, f ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Icc x0 x1, f ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Icc x0 x1, f ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    rectangleLittlewoodFourEdges f x0 x1 y0 y1 =
      rectangleLittlewoodLogNormForm f x0 x1 y0 y1 := by
  have horizontalAnalytic {y : ℝ} (hyMem : y ∈ Icc y0 y1) :
      ∀ x ∈ [[x0, x1]], AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I) := by
    intro x hxMem
    have hxIcc : x ∈ Icc x0 x1 := by simpa only [uIcc_of_le hx] using hxMem
    exact hf _ (by simpa [mem_reProdIm] using And.intro hxIcc hyMem)
  have verticalAnalytic {x : ℝ} (hxMem : x ∈ Icc x0 x1) :
      ∀ y ∈ [[y0, y1]], AnalyticAt ℂ f ((x : ℂ) + I * (y : ℂ)) := by
    intro y hyMem
    have hyIcc : y ∈ Icc y0 y1 := by simpa only [uIcc_of_le hy] using hyMem
    exact hf _ (by simpa [mem_reProdIm] using And.intro hxMem hyIcc)
  have hbottom' : ∀ x ∈ [[x0, x1]], f ((x : ℂ) + (y0 : ℂ) * I) ≠ 0 := by
    simpa only [uIcc_of_le hx] using hbottom
  have htop' : ∀ x ∈ [[x0, x1]], f ((x : ℂ) + (y1 : ℂ) * I) ≠ 0 := by
    simpa only [uIcc_of_le hx] using htop
  have hleft' : ∀ y ∈ [[y0, y1]], f ((x0 : ℂ) + I * (y : ℂ)) ≠ 0 := by
    simpa only [uIcc_of_le hy, mul_comm I] using hleft
  have hright' : ∀ y ∈ [[y0, y1]], f ((x1 : ℂ) + I * (y : ℂ)) ≠ 0 := by
    simpa only [uIcc_of_le hy, mul_comm I] using hright
  have hb := intervalIntegral_im_weighted_logDeriv_horizontal_eq_of_analytic
    (anchor := x0) (horizontalAnalytic (left_mem_Icc.mpr hy)) hbottom'
  have ht := intervalIntegral_im_weighted_logDeriv_horizontal_eq_of_analytic
    (anchor := x0) (horizontalAnalytic (right_mem_Icc.mpr hy)) htop'
  have hl := intervalIntegral_re_weighted_logDeriv_vertical_eq_of_analytic
    (anchor := x0) (verticalAnalytic (left_mem_Icc.mpr hx)) hleft'
  have hr := intervalIntegral_re_weighted_logDeriv_vertical_eq_of_analytic
    (anchor := x0) (verticalAnalytic (right_mem_Icc.mpr hx)) hright'
  simp only [mul_comm I] at hl hr
  unfold rectangleLittlewoodFourEdges rectangleLittlewoodLogNormForm
  rw [hb, ht, hl, hr]
  ring

end PrimeNumberTheorem.CarlsonZeroDensity
