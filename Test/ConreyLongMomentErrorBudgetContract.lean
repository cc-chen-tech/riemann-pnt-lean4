import HardyTheorem.ConreyLongMomentErrorBudget

open Filter
open scoped Topology

namespace HardyTheorem

/- The literal exponent detects the erroneous choice eta = epsilon/2.
The final test includes the infinite dyadic sum, logarithmic counting loss,
Gaussian loss, both contour lines, and an explicit power saving. -/
example : Summable (fun j : ℕ =>
    ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 200000 - 1 / 100000)) :=
  conreyLongMoment_dyadic_summable

example : (∑' j : ℕ,
    ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 200000 - 1 / 100000)) =
    (1 - (2 : ℝ) ^ (-(1 : ℝ) / 200000))⁻¹ :=
  conreyLongMoment_dyadic_tsum

example : Tendsto (fun L : ℝ =>
    ((1 + L) ^ 3 *
      Real.exp (((7 / 2 : ℝ) * (1 / 100000) +
        (1 + 1 / 100000 + 2 * (571 / 1000)) * (1 / 100000) +
        1 / 200000 + 1 / 200000) * L) *
      (Real.exp ((-1 / 2 + 7 * (571 / 1000) / 8 : ℝ) * L) +
        Real.exp ((-1 + 7 * (571 / 1000) / 4 : ℝ) * L)) *
      ∑' j : ℕ, ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 200000 - 1 / 100000)) *
      Real.exp (L / 4000)) atTop (𝓝 0) :=
  conreyLongMoment_errorEnvelope_scaled_tendsto_zero

#print axioms conreyLongMoment_dyadic_summable
#print axioms conreyLongMoment_dyadic_tsum
#print axioms conreyLongMoment_errorEnvelope_scaled_tendsto_zero

end HardyTheorem
