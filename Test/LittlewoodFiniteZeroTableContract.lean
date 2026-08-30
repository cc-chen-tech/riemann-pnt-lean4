import PrimeNumberTheorem.LittlewoodFiniteZeroTable

/-!
The full left-boundary Littlewood bound must construct its zero-free
approach and logarithmic upper bound from the finite analytic zero table;
neither is an input. Left-edge zeros are expressly allowed.
-/

open Complex Set
open scoped BigOperators Interval
open PrimeNumberTheorem.CarlsonZeroDensity

example {f : ℂ → ℂ} {x0 x1 y0 y1 critical : ℝ}
    (hy : y0 < y1) (hc0 : x0 < critical) (hc1 : critical < x1)
    (K : Finset ℂ) (m : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ), f z = 0 ↔ z ∈ K)
    (horder : ∀ z ∈ K, analyticOrderAt f z = m z)
    (hK : ∀ z ∈ K, x0 ≤ z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) :
    (2 * Real.pi) * (critical - x0) *
        (∑ z ∈ K.filter (fun z => critical ≤ z.re), (m z : ℝ)) ≤
      (∫ t in y0..y1, Real.log ‖f ((x0 : ℂ) + I * t)‖) +
        littlewoodRectangleNonleftRemainder f x0 x1 y0 y1 := by
  exact littlewoodRectangle_mass_le_logNormEdges_of_finite_zero_table
    hy hc0 hc1 K m hf hzero horder hK

#print axioms littlewoodRectangle_mass_le_logNormEdges_of_finite_zero_table
