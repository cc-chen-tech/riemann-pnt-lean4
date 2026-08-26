import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalAverage

open MeasureTheory Set
open scoped Interval

namespace MathlibAux

/-!
# A constant-exact logarithmic arithmetic--geometric mean inequality

The normalization by `b - a` is kept explicit because this is the form needed
when a mollified second moment is inserted into Littlewood's lemma.
-/

/-- The interval integral of the logarithm of a positive continuous function
is bounded by the logarithm of its interval average. -/
theorem integral_log_le_length_mul_log_mean
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf_pos : ∀ x ∈ Icc a b, 0 < f x) :
    (∫ x in a..b, Real.log (f x)) ≤
      (b - a) * Real.log ((∫ x in a..b, f x) / (b - a)) := by
  have hlength : 0 < b - a := sub_pos.mpr hab
  have hf_ne : ∀ x ∈ Icc a b, f x ≠ 0 :=
    fun x hx => (hf_pos x hx).ne'
  have hlog_cont : ContinuousOn (fun x => Real.log (f x)) (Icc a b) :=
    hf.log hf_ne
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    rw [uIoc_of_le hab.le]
    infer_instance
  have : NeZero (volume (uIoc a b)) := ⟨by
    simpa [uIoc_of_le hab.le, Real.volume_Ioc] using hab⟩
  have h_exp_log :
      ∀ᵐ x ∂volume.restrict (uIoc a b),
        Real.exp (Real.log (f x)) = f x := by
    rw [uIoc_of_le hab.le, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    exact Real.exp_log (hf_pos x (Ioc_subset_Icc_self hx))
  have hexp :
      Real.exp (⨍ x in a..b, Real.log (f x)) ≤
        ⨍ x in a..b, f x := by
    calc
      Real.exp (⨍ x in a..b, Real.log (f x)) ≤
          ⨍ x in a..b, Real.exp (Real.log (f x)) := by
        refine convexOn_exp.map_average_le Real.continuous_exp.continuousOn
          isClosed_univ (by simp) ?_ ?_
        · rw [uIoc_of_le hab.le]
          exact hlog_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
        · exact (integrable_congr h_exp_log).mpr <| by
            rw [uIoc_of_le hab.le]
            exact hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      _ = ⨍ x in a..b, f x := average_congr h_exp_log
  have havg :
      (⨍ x in a..b, Real.log (f x)) ≤
        Real.log (⨍ x in a..b, f x) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos _) hexp
  rw [interval_average_eq_div, interval_average_eq_div] at havg
  rw [mul_comm]
  exact (div_le_iff₀ hlength).mp havg

end MathlibAux
