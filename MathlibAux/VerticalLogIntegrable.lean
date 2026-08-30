import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace MathlibAux

/-- In Lean's totalized convention `Real.log 0 = 0`, the logarithm of the norm
of an analytic function is interval integrable on a vertical segment even when
the segment contains zeros.  Mathlib's meromorphic logarithm theorem supplies
the local factorization at nontrivial zeros; the identically-zero case is also
covered by that totalized convention.  Applications to the classical
logarithmic integral should separately exclude the identically-zero function. -/
theorem intervalIntegrable_log_norm_vertical_of_analyticOnNhd
    {f : ℂ → ℂ} {x0 x1 y0 y1 sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hsigma : sigma ∈ [[x0, x1]]) :
    IntervalIntegrable
      (fun y : ℝ => Real.log ‖f ((sigma : ℂ) + I * (y : ℂ))‖)
      volume y0 y1 := by
  have hvertical : AnalyticOnNhd ℝ
      (fun y : ℝ => f ((sigma : ℂ) + I * (y : ℂ))) [[y0, y1]] := by
    intro y hy
    have hzmem : (sigma : ℂ) + I * (y : ℂ) ∈
        ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
      simpa [mem_reProdIm] using And.intro hsigma hy
    have haffine : AnalyticAt ℂ
        (fun z : ℂ => (sigma : ℂ) + I * z) (y : ℂ) := by
      fun_prop
    have hcomplex : AnalyticAt ℂ
        (fun z : ℂ => f ((sigma : ℂ) + I * z)) (y : ℂ) := by
      have hcomp : AnalyticAt ℂ
          (f ∘ fun z : ℂ => (sigma : ℂ) + I * z) (y : ℂ) :=
        AnalyticAt.comp_of_eq (g := f)
          (f := fun z : ℂ => (sigma : ℂ) + I * z)
          (hf _ hzmem) haffine rfl
      simpa [Function.comp_def] using hcomp
    have hreal := hcomplex.restrictScalars.comp
      (Complex.ofRealCLM.analyticAt y)
    simpa [Function.comp_def] using hreal
  exact hvertical.meromorphicOn.intervalIntegrable_log_norm

/-- Moving vertical logarithms converge almost everywhere when the limiting
vertical segment has only the specified finite set of zeros.  At the finitely
many exceptional ordinates no pointwise assertion is needed. -/
theorem ae_tendsto_log_norm_vertical_of_analyticOnNhd_finite_zeros
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} {poles : Finset ℂ}
    {x : ℕ → ℝ}
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (hx : Tendsto x atTop (𝓝 x0)) :
    ∀ᵐ y : ℝ ∂(volume.restrict (Set.Ioc y0 y1)),
      Tendsto
        (fun n => Real.log ‖f ((x n : ℂ) + I * (y : ℂ))‖)
        atTop
        (𝓝 (Real.log ‖f ((x0 : ℂ) + I * (y : ℂ))‖)) := by
  let heights : Finset ℝ := poles.image Complex.im
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
      heights.countable_toSet.ae_notMem
        (volume.restrict (Set.Ioc y0 y1))] with y hy hynot
  have hyle : y0 ≤ y1 := hy.1.le.trans hy.2
  have hyu : y ∈ [[y0, y1]] := by
    simpa [uIcc_of_le hyle] using
      (show y ∈ Set.Icc y0 y1 from ⟨hy.1.le, hy.2⟩)
  have hzmem : (x0 : ℂ) + I * (y : ℂ) ∈
      ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
    simpa [mem_reProdIm] using
      And.intro (left_mem_uIcc : x0 ∈ [[x0, x1]]) hyu
  have htargetNe : f ((x0 : ℂ) + I * (y : ℂ)) ≠ 0 := by
    intro htargetZero
    have hpole := (hzero _ hzmem).mp htargetZero
    have hymem : y ∈ heights := by
      dsimp only [heights]
      refine Finset.mem_image.mpr ⟨(x0 : ℂ) + I * (y : ℂ), hpole, ?_⟩
      simp
    exact hynot hymem
  have hcast : Tendsto (fun n => (x n : ℂ)) atTop (𝓝 (x0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hx
  have hpoint : Tendsto
      (fun n => (x n : ℂ) + I * (y : ℂ)) atTop
      (𝓝 ((x0 : ℂ) + I * (y : ℂ))) :=
    hcast.add tendsto_const_nhds
  have hvalue := (hf _ hzmem).continuousAt.tendsto.comp hpoint
  have hnorm := hvalue.norm
  exact (Real.continuousAt_log (norm_ne_zero_iff.mpr htargetNe)).tendsto.comp hnorm

end MathlibAux
