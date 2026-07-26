import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace MathlibAux

/--
Setwise Cauchy--Schwarz for a real function against a nonnegative weight.
The formulation keeps the weight inside both moments, which is convenient
for polynomial-Gaussian contour kernels.
-/
theorem sq_setIntegral_abs_mul_weight_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f w : α → ℝ}
    (hs : MeasurableSet s)
    (hf : Measurable f) (hw : Measurable w)
    (hw_nonneg : ∀ x ∈ s, 0 ≤ w x)
    (hf_sq_weight : IntegrableOn (fun x => f x ^ 2 * w x) s μ)
    (hw_int : IntegrableOn w s μ) :
    (∫ x in s, |f x| * w x ∂μ) ^ 2 ≤
      (∫ x in s, f x ^ 2 * w x ∂μ) *
        ∫ x in s, w x ∂μ := by
  let F : α → ℝ := fun x => |f x| * Real.sqrt (w x)
  let G : α → ℝ := fun x => Real.sqrt (w x)
  have hF_meas : Measurable F := hf.norm.mul hw.sqrt
  have hG_meas : Measurable G := hw.sqrt
  have hF_sq : IntegrableOn (fun x => F x ^ 2) s μ := by
    apply hf_sq_weight.congr_fun _ hs
    intro x hx
    dsimp [F]
    rw [mul_pow, sq_abs, Real.sq_sqrt (hw_nonneg x hx)]
  have hG_sq : IntegrableOn (fun x => G x ^ 2) s μ := by
    apply hw_int.congr_fun _ hs
    intro x hx
    dsimp [G]
    rw [Real.sq_sqrt (hw_nonneg x hx)]
  have hF_asm : AEStronglyMeasurable F (μ.restrict s) :=
    hF_meas.aestronglyMeasurable
  have hG_asm : AEStronglyMeasurable G (μ.restrict s) :=
    hG_meas.aestronglyMeasurable
  have hF_memLp : MemLp F 2 (μ.restrict s) :=
    (memLp_two_iff_integrable_sq hF_asm).2 hF_sq
  have hG_memLp : MemLp G 2 (μ.restrict s) :=
    (memLp_two_iff_integrable_sq hG_asm).2 hG_sq
  let FLp : Lp ℝ 2 (μ.restrict s) := hF_memLp.toLp F
  let GLp : Lp ℝ 2 (μ.restrict s) := hG_memLp.toLp G
  have hcs := real_inner_mul_inner_self_le GLp FLp
  have hGF :
      ⟪GLp, FLp⟫_ℝ = ∫ x in s, |f x| * w x ∂μ := by
    rw [L2.inner_def]
    change (∫ x, FLp x * GLp x ∂(μ.restrict s)) = _
    rw [show
        (∫ x, FLp x * GLp x ∂(μ.restrict s)) =
          ∫ x, F x * G x ∂(μ.restrict s) by
      apply integral_congr_ae
      filter_upwards [hF_memLp.coeFn_toLp, hG_memLp.coeFn_toLp] with x hFx hGx
      change FLp x = F x at hFx
      change GLp x = G x at hGx
      rw [hFx, hGx]]
    apply setIntegral_congr_fun hs
    intro x hx
    dsimp [F, G]
    rw [mul_assoc, Real.mul_self_sqrt (hw_nonneg x hx)]
  have hGG :
      ⟪GLp, GLp⟫_ℝ = ∫ x in s, w x ∂μ := by
    rw [L2.inner_def]
    change (∫ x, GLp x * GLp x ∂(μ.restrict s)) = _
    rw [show
        (∫ x, GLp x * GLp x ∂(μ.restrict s)) =
          ∫ x, G x * G x ∂(μ.restrict s) by
      apply integral_congr_ae
      filter_upwards [hG_memLp.coeFn_toLp] with x hGx
      change GLp x = G x at hGx
      rw [hGx]]
    apply setIntegral_congr_fun hs
    intro x hx
    dsimp [G]
    exact Real.mul_self_sqrt (hw_nonneg x hx)
  have hFF :
      ⟪FLp, FLp⟫_ℝ =
        ∫ x in s, f x ^ 2 * w x ∂μ := by
    rw [L2.inner_def]
    change (∫ x, FLp x * FLp x ∂(μ.restrict s)) = _
    rw [show
        (∫ x, FLp x * FLp x ∂(μ.restrict s)) =
          ∫ x, F x * F x ∂(μ.restrict s) by
      apply integral_congr_ae
      filter_upwards [hF_memLp.coeFn_toLp] with x hFx
      change FLp x = F x at hFx
      rw [hFx]]
    apply setIntegral_congr_fun hs
    intro x hx
    dsimp [F]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hw_nonneg x hx)]
    rw [show |f x| * |f x| = f x ^ 2 by
      rw [← pow_two, sq_abs]]
  rw [hGF, hGG, hFF] at hcs
  simpa [pow_two, mul_comm] using hcs

end MathlibAux
