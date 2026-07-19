import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue

open MeasureTheory Set

namespace MathlibAux

/-!
# Detecting a zero from strict integral cancellation

For a continuous real function, strict inequality between the absolute value
of its signed integral and the integral of its absolute value forces both
signs to occur.  The intermediate value theorem then supplies a zero.
-/

/-- Strict cancellation in an interval integral of a continuous real
function forces a zero in that interval. -/
theorem exists_zero_of_abs_intervalIntegral_lt_intervalIntegral_abs
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hstrict : |∫ x in a..b, f x| < ∫ x in a..b, |f x|) :
    ∃ x ∈ Set.Icc a b, f x = 0 := by
  have hneg : ∃ x ∈ Set.Icc a b, f x < 0 := by
    by_contra hnot
    push Not at hnot
    have hnonneg : 0 ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_nonneg hab hnot
    have heq : (∫ x in a..b, |f x|) = ∫ x in a..b, f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact abs_of_nonneg (hnot x hx)
    rw [heq, abs_of_nonneg hnonneg] at hstrict
    exact lt_irrefl _ hstrict
  have hpos : ∃ x ∈ Set.Icc a b, 0 < f x := by
    by_contra hnot
    push Not at hnot
    have hnegint : 0 ≤ ∫ x in a..b, -f x :=
      intervalIntegral.integral_nonneg hab fun x hx =>
        neg_nonneg.mpr (hnot x hx)
    rw [intervalIntegral.integral_neg] at hnegint
    have hnonpos : (∫ x in a..b, f x) ≤ 0 := by linarith
    have heq : (∫ x in a..b, |f x|) = -∫ x in a..b, f x := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact abs_of_nonpos (hnot x hx)
    rw [heq, abs_of_nonpos hnonpos] at hstrict
    exact lt_irrefl _ hstrict
  obtain ⟨x, hx, hxneg⟩ := hneg
  obtain ⟨y, hy, hypos⟩ := hpos
  obtain ⟨z, hzmem, hz⟩ :=
    isPreconnected_Icc.intermediate_value hx hy hf.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f x) (f y) by
        exact ⟨hxneg.le, hypos.le⟩)
  exact ⟨z, hzmem, hz⟩

end MathlibAux
