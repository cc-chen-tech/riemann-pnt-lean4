import PrimeNumberTheorem.LittlewoodLeftBoundaryLimit

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- A weighted integral with a moving left endpoint is continuous when its
fixed factor is continuous on the ambient compact interval. -/
theorem continuousOn_intervalIntegral_sub_mul_left
    {g : ℝ → ℝ} {x0 x1 : ℝ}
    (hg : ContinuousOn g [[x0, x1]]) :
    ContinuousOn
      (fun x => ∫ u in x..x1, (u - x) * g u)
      [[x0, x1]] := by
  have hgInt : IntegrableOn g [[x0, x1]] := hg.integrableOn_uIcc
  have hug : ContinuousOn (fun u : ℝ => u * g u) [[x0, x1]] :=
    continuousOn_id.mul hg
  have hugInt : IntegrableOn (fun u : ℝ => u * g u) [[x0, x1]] :=
    hug.integrableOn_uIcc
  have hfirst : ContinuousOn
      (fun x => ∫ u in x..x1, u * g u) [[x0, x1]] :=
    intervalIntegral.continuousOn_primitive_interval_left hugInt
  have hsecond : ContinuousOn
      (fun x => x * (∫ u in x..x1, g u)) [[x0, x1]] :=
    continuousOn_id.mul
      (intervalIntegral.continuousOn_primitive_interval_left hgInt)
  apply (hfirst.sub hsecond).congr
  intro x hx
  have hgInterval : IntervalIntegrable g volume x x1 :=
    hg.intervalIntegrable.mono_set (uIcc_subset_uIcc_right hx)
  have hugInterval : IntervalIntegrable (fun u : ℝ => u * g u) volume x x1 :=
    hug.intervalIntegrable.mono_set (uIcc_subset_uIcc_right hx)
  change (∫ u in x..x1, (u - x) * g u) =
    (∫ u in x..x1, u * g u) - x * (∫ u in x..x1, g u)
  calc
    (∫ u in x..x1, (u - x) * g u) =
        ∫ u in x..x1, u * g u - x * g u := by
      apply intervalIntegral.integral_congr
      intro u _
      ring
    _ = (∫ u in x..x1, u * g u) - (∫ u in x..x1, x * g u) :=
      intervalIntegral.integral_sub hugInterval (hgInterval.const_mul x)
    _ = (∫ u in x..x1, u * g u) - x * (∫ u in x..x1, g u) := by
      rw [intervalIntegral.integral_const_mul]

/-- The three non-left terms in the shifted Littlewood rectangle remainder
vary continuously with the left endpoint, provided the fixed horizontal
edges are analytic and zero-free. -/
theorem continuousOn_littlewoodRectangleNonleftRemainder
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hbottomA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y0 : ℂ) * I))
    (hbottomNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htopA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y1 : ℂ) * I))
    (htopNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    ContinuousOn
      (fun x => littlewoodRectangleNonleftRemainder f x x1 y0 y1)
      [[x0, x1]] := by
  have hbottomLog := continuousOn_logDeriv_horizontal hbottomA hbottomNe
  have htopLog := continuousOn_logDeriv_horizontal htopA htopNe
  have hbottomIm : ContinuousOn
      (fun u : ℝ => (logDeriv f ((u : ℂ) + (y0 : ℂ) * I)).im)
      [[x0, x1]] :=
    Complex.continuous_im.comp_continuousOn hbottomLog
  have htopIm : ContinuousOn
      (fun u : ℝ => (logDeriv f ((u : ℂ) + (y1 : ℂ) * I)).im)
      [[x0, x1]] :=
    Complex.continuous_im.comp_continuousOn htopLog
  have hbottom := continuousOn_intervalIntegral_sub_mul_left hbottomIm
  have htop := continuousOn_intervalIntegral_sub_mul_left htopIm
  unfold littlewoodRectangleNonleftRemainder
  exact (((continuousOn_const.neg.add hbottom).sub htop).add
    ((continuousOn_const.sub continuousOn_id).mul continuousOn_const))

/-- Along any sequence staying in the ambient interval and converging to its
left endpoint, the non-left Littlewood remainder converges to the limiting
remainder. -/
theorem tendsto_littlewoodRectangleNonleftRemainder
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hbottomA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y0 : ℂ) * I))
    (hbottomNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htopA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y1 : ℂ) * I))
    (htopNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y1 : ℂ) * I) ≠ 0)
    {x : ℕ → ℝ}
    (hxmem : ∀ n, x n ∈ [[x0, x1]])
    (hxtend : Tendsto x atTop (𝓝 x0)) :
    Tendsto
      (fun n => littlewoodRectangleNonleftRemainder f (x n) x1 y0 y1)
      atTop
      (𝓝 (littlewoodRectangleNonleftRemainder f x0 x1 y0 y1)) := by
  have hwithin : Tendsto x atTop (𝓝[ [[x0, x1]]] x0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hxtend, Eventually.of_forall hxmem⟩
  exact (continuousOn_littlewoodRectangleNonleftRemainder
    hbottomA hbottomNe htopA htopNe x0 left_mem_uIcc).tendsto.comp hwithin

end CarlsonZeroDensity
end PrimeNumberTheorem
