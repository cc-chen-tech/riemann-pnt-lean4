import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import WeilExtremalKernels.ArchimedeanTailTransfer

/-!
# Scalar archimedean-tail budget

This module verifies the exact improper integral used in the explicit
archimedean-tail estimate of the finite Guinand-Weil dictionary:

`∫ r in Set.Ioi T, log r / (r - b) ^ 2`

equals

`log T / (T - b) + b⁻¹ * log (T / (T - b))`

when `0 < b < T` and `1 ≤ T`.

This is the scalar analytic input to an explicit matrix tail budget. It does
not yet construct the paper's rank-two matrix-valued tail, prove the required
vector-norm estimate, or transfer the finite dictionary to the full Weil
criterion.
-/

namespace WeilExtremalKernels

open Filter MeasureTheory Set
open scoped Topology

/-- An antiderivative of `log x / (x - b)²` which vanishes at `+∞`. -/
noncomputable def archimedeanTailPrimitive (b x : ℝ) : ℝ :=
  -Real.log x / (x - b) - b⁻¹ * (Real.log x - Real.log (x - b))

/-- Derivative identity behind the scalar archimedean-tail integral. -/
theorem hasDerivAt_archimedeanTailPrimitive {b x : ℝ}
    (hb : b ≠ 0) (hx : x ≠ 0) (hxb : x - b ≠ 0) :
    HasDerivAt (archimedeanTailPrimitive b)
      (Real.log x / (x - b) ^ 2) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx
  have hsub : HasDerivAt (fun y : ℝ ↦ y - b) 1 x :=
    hasDerivAt_id x |>.sub_const b
  have hlogSub :
      HasDerivAt (fun y : ℝ ↦ Real.log (y - b)) (1 / (x - b)) x :=
    hsub.log hxb
  unfold archimedeanTailPrimitive
  convert (hlog.neg.div hsub hxb).sub
    ((hlog.sub hlogSub).const_mul b⁻¹) using 1
  all_goals
    simp only [Pi.neg_apply]
    field_simp
    ring

/-- The chosen antiderivative tends to zero at positive infinity. -/
theorem tendsto_archimedeanTailPrimitive_atTop (b : ℝ) :
    Tendsto (archimedeanTailPrimitive b) atTop (𝓝 0) := by
  have hfirst :
      Tendsto (fun x : ℝ ↦ Real.log x / (x - b)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 (-b) 1 one_ne_zero
  have hsub : Tendsto (fun x : ℝ ↦ x - b) atTop atTop :=
    tendsto_atTop.2 fun a ↦ by
      filter_upwards [eventually_ge_atTop (a + b)] with x hx
      linarith
  have hdiff :
      Tendsto (fun x : ℝ ↦ Real.log x - Real.log (x - b)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_log_comp_add_sub_log b).comp hsub
  have h := hfirst.neg.sub (hdiff.const_mul b⁻¹)
  convert h using 1
  · funext x
    unfold archimedeanTailPrimitive
    ring
  · norm_num

/-- Exact scalar improper integral used in the explicit archimedean-tail
budget. The paper applies it with `b = ρ N` and `T > max (ρ N) 7`. -/
theorem integral_Ioi_log_div_sub_sq
    {b T : ℝ} (hb : 0 < b) (hT : b < T) (hT1 : 1 ≤ T) :
    ∫ r in Ioi T, Real.log r / (r - b) ^ 2 =
      Real.log T / (T - b) + b⁻¹ * Real.log (T / (T - b)) := by
  have hderiv :
      ∀ x ∈ Ici T,
        HasDerivAt (archimedeanTailPrimitive b)
          (Real.log x / (x - b) ^ 2) x := by
    intro x hx
    have hbx : b < x := lt_of_lt_of_le hT hx
    have hx0 : 0 < x := lt_trans hb hbx
    exact hasDerivAt_archimedeanTailPrimitive
      hb.ne' hx0.ne' (sub_ne_zero.mpr hbx.ne')
  have hnonneg :
      ∀ x ∈ Ioi T, 0 ≤ Real.log x / (x - b) ^ 2 := by
    intro x hx
    have hx1 : 1 < x := lt_of_le_of_lt hT1 hx
    exact div_nonneg (Real.log_nonneg (le_of_lt hx1)) (sq_nonneg _)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg'
    hderiv hnonneg (tendsto_archimedeanTailPrimitive_atTop b)]
  unfold archimedeanTailPrimitive
  rw [Real.log_div (ne_of_gt (lt_trans hb hT))
    (sub_ne_zero.mpr hT.ne')]
  ring

end WeilExtremalKernels
