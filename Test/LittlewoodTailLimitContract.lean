import PrimeNumberTheorem.LittlewoodTailLimit

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open PrimeNumberTheorem.CarlsonZeroDensity

-- Mutation caught: the coefficient and non-left remainder must both be at
-- the limiting endpoint `x0`; no zero-free hypothesis is allowed there.
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
    {C : ℝ}
    (hlogle : ∀ sigma ∈ [[x0, x1]], ∀ y ∈ [[y0, y1]],
      Real.log ‖f ((sigma : ℂ) + I * (y : ℂ))‖ ≤ C) :
    (2 * Real.pi) * (critical - x0) *
        zeroMultiplicityMassAtOrRight poles multiplicity critical ≤
      (∫ y in y0..y1,
        Real.log ‖f ((x0 : ℂ) + I * (y : ℂ))‖) +
      littlewoodRectangleNonleftRemainder f x0 x1 y0 y1 := by
  exact littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros
    hx hy hcritical1 poles multiplicity hf hzero horder hpoles
    hxleft hxcritical hxline hxtend hlogle

#print axioms littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros
