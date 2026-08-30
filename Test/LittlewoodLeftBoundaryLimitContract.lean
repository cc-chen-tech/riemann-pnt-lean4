import PrimeNumberTheorem.LittlewoodLeftBoundaryLimit

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open MathlibAux
open PrimeNumberTheorem.CarlsonZeroDensity

-- Lock the exact reverse-Fatou interface used at the moving left boundary.
example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ} {C δ : ℝ}
    (hδ : 0 < δ)
    (hC : Integrable (fun _ : α => C) μ)
    (hf : ∀ n, Integrable (f n) μ)
    (hg : Integrable g μ)
    (hfle : ∀ n, f n ≤ᵐ[μ] fun _ => C)
    (hgle : g ≤ᵐ[μ] fun _ => C)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∃ n, ∫ x, f n x ∂μ ≤ (∫ x, g x ∂μ) + δ := by
  exact exists_integral_le_add_of_ae_tendsto_of_le
    hδ hC hf hg hfle hgle hfg

-- Lock integrability on a vertical segment, including its totalized-log API.
example {f : ℂ → ℂ} {x0 x1 y0 y1 sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hsigma : sigma ∈ [[x0, x1]]) :
    IntervalIntegrable
      (fun y : ℝ => Real.log ‖f ((sigma : ℂ) + I * (y : ℂ))‖)
      volume y0 y1 := by
  exact intervalIntegrable_log_norm_vertical_of_analyticOnNhd hf hsigma

-- Lock the almost-everywhere convergence statement and its finite exceptional
-- set, so no zero-free hypothesis is accidentally added at the limiting edge.
example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} {poles : Finset ℂ}
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
  exact ae_tendsto_log_norm_vertical_of_analyticOnNhd_finite_zeros
    hf hzero hx

-- Lock every mathematical direction in the limiting Littlewood inequality:
-- shifted lines approach from the right, stay left of `critical`, preserve the
-- target mass, and leave the non-left remainder at the selected shifted line.
example {f : ℂ → ℂ} {x0 x1 y0 y1 critical : ℝ}
    (hx : x0 < x1) (hy : y0 < y1)
    (hcritical1 : critical < x1)
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 ≤ rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1)
    {x : ℕ → ℝ}
    (hxleft : ∀ n, x0 < x n)
    (hxcritical : ∀ n, x n < critical)
    (hxline : ∀ n y, y ∈ [[y0, y1]] →
      f ((x n : ℂ) + I * (y : ℂ)) ≠ 0)
    (hxtend : Tendsto x atTop (𝓝 x0))
    {C delta : ℝ} (hdelta : 0 < delta)
    (hlogle : ∀ sigma ∈ [[x0, x1]], ∀ y ∈ [[y0, y1]],
      Real.log ‖f ((sigma : ℂ) + I * (y : ℂ))‖ ≤ C) :
    ∃ n,
      (2 * Real.pi) * (critical - x n) *
          zeroMultiplicityMassAtOrRight poles multiplicity critical ≤
        (∫ y in y0..y1,
          Real.log ‖f ((x0 : ℂ) + I * (y : ℂ))‖) + delta +
        littlewoodRectangleNonleftRemainder f (x n) x1 y0 y1 := by
  exact exists_littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros
    hx hy hcritical1 poles multiplicity hf hzero horder hpoles
    hxleft hxcritical hxline hxtend hdelta hlogle

#print axioms exists_integral_le_add_of_ae_tendsto_of_le
#print axioms intervalIntegrable_log_norm_vertical_of_analyticOnNhd
#print axioms ae_tendsto_log_norm_vertical_of_analyticOnNhd_finite_zeros
#print axioms exists_littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros
