import HardyTheorem.ConreyLittlewoodMeanSquare

open MeasureTheory Set
open scoped Interval

/-! These contracts fail if everywhere positivity/nonvanishing is required,
if log integrability is omitted, or if the interval length is changed. -/

example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b)
    (hlog : IntervalIntegrable (fun t => Real.log (f t)) volume a b)
    (hpos : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 < f t) :
    0 < (∫ t in a..b, f t) ∧
      (∫ t in a..b, Real.log (f t)) ≤
        (b - a) * Real.log ((∫ t in a..b, f t) / (b - a)) := by
  exact MathlibAux.integral_pos_and_log_le_length_mul_log_mean_of_ae_pos
    hab hf hlog hpos

example {F : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b))
    (hlog : IntervalIntegrable (fun t => Real.log ‖F t‖) volume a b)
    (hF0 : ∀ᵐ t ∂volume.restrict (Ioc a b), F t ≠ 0) :
    0 < (∫ t in a..b, ‖F t‖ ^ 2) ∧
      2 * (∫ t in a..b, Real.log ‖F t‖) ≤
        (b - a) * Real.log ((∫ t in a..b, ‖F t‖ ^ 2) / (b - a)) := by
  exact HardyTheorem.complex_log_interval_integral_bounds_of_ae_ne_zero hab hF hlog hF0

#print axioms MathlibAux.integral_pos_and_log_le_length_mul_log_mean_of_ae_pos
#print axioms HardyTheorem.complex_log_interval_integral_bounds_of_ae_ne_zero
