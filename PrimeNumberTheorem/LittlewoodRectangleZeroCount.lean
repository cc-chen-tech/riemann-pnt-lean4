import PrimeNumberTheorem.LittlewoodRectangleLogNorm

/-! Weighted zero multiplicities equal the endpoint-cancelled Littlewood
expression.  The finite zero data imply boundary nonvanishing; all four
complex edge integrability statements are derived, not assumed. -/

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

theorem two_pi_mul_zeroMultiplicityWeightedRealSum_eq_logNormForm
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} (hx : x0 ≤ x1) (hy : y0 ≤ y1)
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f (Icc x0 x1 ×ℂ Icc y0 y1))
    (hzero : ∀ z ∈ (Icc x0 x1 ×ℂ Icc y0 y1 : Set ℂ), f z = 0 ↔ z ∈ poles)
    (horder : ∀ z ∈ poles, analyticOrderAt f z = multiplicity z)
    (hinterior : ∀ z ∈ poles, x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) :
    (2 * Real.pi) * ∑ z ∈ poles, (z.re - x0) * (multiplicity z : ℝ) =
      rectangleLittlewoodLogNormForm f x0 x1 y0 y1 := by
  have hboundary {z : ℂ} (hz : z ∈ Icc x0 x1 ×ℂ Icc y0 y1)
      (hbd : z.re = x0 ∨ z.re = x1 ∨ z.im = y0 ∨ z.im = y1) : f z ≠ 0 := by
    intro hfzero
    obtain ⟨hL, hR, hB, hT⟩ := hinterior z ((hzero z hz).mp hfzero)
    rcases hbd with h | h | h | h <;> linarith
  have hleft : ∀ y ∈ Icc y0 y1, f ((x0 : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hyMem
    apply hboundary (by simpa [mem_reProdIm] using And.intro (left_mem_Icc.mpr hx) hyMem)
    exact Or.inl (by simp)
  have hright : ∀ y ∈ Icc y0 y1, f ((x1 : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hyMem
    apply hboundary (by simpa [mem_reProdIm] using And.intro (right_mem_Icc.mpr hx) hyMem)
    exact Or.inr (Or.inl (by simp))
  have hbottom : ∀ x ∈ Icc x0 x1, f ((x : ℂ) + (y0 : ℂ) * I) ≠ 0 := by
    intro x hxMem
    apply hboundary (by simpa [mem_reProdIm] using And.intro hxMem (left_mem_Icc.mpr hy))
    exact Or.inr (Or.inr (Or.inl (by simp)))
  have htop : ∀ x ∈ Icc x0 x1, f ((x : ℂ) + (y1 : ℂ) * I) ≠ 0 := by
    intro x hxMem
    apply hboundary (by simpa [mem_reProdIm] using And.intro hxMem (right_mem_Icc.mpr hy))
    exact Or.inr (Or.inr (Or.inr (by simp)))
  have horizontalAnalytic {y : ℝ} (hyMem : y ∈ Icc y0 y1) :
      ∀ x ∈ [[x0, x1]], AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I) := by
    intro x hxMem
    have hxIcc : x ∈ Icc x0 x1 := by simpa only [uIcc_of_le hx] using hxMem
    exact hf _ (by simpa [mem_reProdIm] using And.intro hxIcc hyMem)
  have horizontalInt {y : ℝ} (hyMem : y ∈ Icc y0 y1)
      (hne : ∀ x ∈ Icc x0 x1, f ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
      IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
        logDeriv f ((x : ℂ) + (y : ℂ) * I)) volume x0 x1 := by
    have hne' : ∀ x ∈ [[x0, x1]], f ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
      simpa only [uIcc_of_le hx] using hne
    have hlog := continuousOn_logDeriv_horizontal (horizontalAnalytic hyMem) hne'
    have hweight : Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * I - (x0 : ℂ) := by fun_prop
    exact (hweight.continuousOn.mul hlog).intervalIntegrable
  have verticalInt {x : ℝ} (hxMem : x ∈ Icc x0 x1)
      (hne : ∀ y ∈ Icc y0 y1, f ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
      IntervalIntegrable (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
        logDeriv f ((x : ℂ) + (y : ℂ) * I)) volume y0 y1 := by
    have hlog : ContinuousOn (fun y : ℝ => logDeriv f ((x : ℂ) + (y : ℂ) * I))
        [[y0, y1]] := by
      intro y hyMem
      have hyIcc : y ∈ Icc y0 y1 := by simpa only [uIcc_of_le hy] using hyMem
      have ha := hf ((x : ℂ) + (y : ℂ) * I)
        (by simpa [mem_reProdIm] using And.intro hxMem hyIcc)
      have hmap : ContinuousAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) y := by fun_prop
      have hcomp : ContinuousAt (fun t : ℝ => logDeriv f ((x : ℂ) + (t : ℂ) * I)) y := by
        simpa only [Function.comp_def] using
          (ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero ha
            (hne y hyIcc)).continuousAt.comp
            (f := fun t : ℝ => (x : ℂ) + (t : ℂ) * I) hmap
      exact hcomp.continuousWithinAt
    have hweight : Continuous fun y : ℝ => (x : ℂ) + (y : ℂ) * I - (x0 : ℂ) := by fun_prop
    exact (hweight.continuousOn.mul hlog).intervalIntegrable
  have hf' : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]) := by
    simpa only [uIcc_of_le hx, uIcc_of_le hy] using hf
  have hzero' : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ), f z = 0 ↔ z ∈ poles := by
    simpa only [uIcc_of_le hx, uIcc_of_le hy] using hzero
  have hfour := two_pi_mul_zeroMultiplicityWeightedRealSum_eq_four_edges
    poles multiplicity hf' hzero' horder hinterior
    (horizontalInt (left_mem_Icc.mpr hy) hbottom)
    (horizontalInt (right_mem_Icc.mpr hy) htop)
    (verticalInt (right_mem_Icc.mpr hx) hright)
    (verticalInt (left_mem_Icc.mpr hx) hleft)
  calc
    _ = rectangleLittlewoodFourEdges f x0 x1 y0 y1 := hfour
    _ = _ := rectangleLittlewoodFourEdges_eq_logNormForm hx hy hf hleft hright hbottom htop

end PrimeNumberTheorem.CarlsonZeroDensity
