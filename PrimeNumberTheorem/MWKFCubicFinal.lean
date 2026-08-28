import PrimeNumberTheorem.MWKFCubicAggregation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Filter Asymptotics MeasureTheory
open scoped Interval

namespace PrimeNumberTheorem
namespace MWKFCubic

/-- The audited reciprocal-LCM main-term constant. -/
noncomputable def cubicMainConstant (W : ℝ → ℝ) : ℝ :=
  (4 / 3 : ℝ) * ∫ u in (1 : ℝ)..2, W u

/-- The exact final `4/3` specialization of `long_mollifier_reassembly`.

The two little-o hypotheses are intentionally visible.  In particular this
statement cannot be mistaken for a formalization of the external cubic MRSTT
input itself. -/
theorem cubic_long_mollifier_asymptotic_of_exact_inputs
    (W : ℝ → ℝ) (I Q R : ℝ → ℝ)
    (hexact : ∀ T, I T = T * Q T + R T)
    (hmain : (fun T ↦ Q T - cubicMainConstant W) =o[atTop]
      (fun _T ↦ (1 : ℝ)))
    (hrem : R =o[atTop] (fun T : ℝ ↦ T)) :
    (fun T ↦ I T - cubicMainConstant W * T) =o[atTop]
      (fun T : ℝ ↦ T) := by
  exact long_mollifier_reassembly I Q R (cubicMainConstant W)
    hexact hmain hrem

end MWKFCubic
end PrimeNumberTheorem
