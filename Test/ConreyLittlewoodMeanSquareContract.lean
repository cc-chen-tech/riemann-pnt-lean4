import HardyTheorem.ConreyLittlewoodMeanSquare

open MeasureTheory

namespace HardyTheorem

/-!
# Contract for the constant-exact Conrey Littlewood mean-square bridge

This catches loss of the factor `2`, omission of interval-length
normalization, or reversal of the inequality connecting a complex boundary
function's logarithmic integral to its second moment.
-/

example {F : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b))
    (hF0 : ∀ t ∈ Set.Icc a b, F t ≠ 0) :
    2 * (∫ t in a..b, Real.log ‖F t‖) ≤
      (b - a) * Real.log ((∫ t in a..b, ‖F t‖ ^ 2) / (b - a)) :=
  complex_log_interval_integral_le_log_mean_normSq hab hF hF0

example {F : ℝ → ℂ} {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (hF : ContinuousOn F (Set.Icc a b))
    (hF0 : ∀ t ∈ Set.Icc a b, F t ≠ 0)
    (hM2 : (∫ t in a..b, ‖F t‖ ^ 2) ≤ C * (b - a)) :
    2 * (∫ t in a..b, Real.log ‖F t‖) ≤ (b - a) * Real.log C :=
  complex_log_interval_integral_le_of_normSq_integral_le hab hC hF hF0 hM2

#print axioms complex_log_interval_integral_le_log_mean_normSq
#print axioms complex_log_interval_integral_le_of_normSq_integral_le

end HardyTheorem
