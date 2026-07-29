import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

namespace MathlibAux

private theorem norm_toLp_sq_eq_integral_sq
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  simp [pow_two]

private theorem sqrt_integral_sq_eq_norm_toLp
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ := by
  rw [← norm_toLp_sq_eq_integral_sq hf]
  exact Real.sqrt_sq (norm_nonneg _)

/--
The reverse triangle inequality for real `L²` functions, written directly
in terms of their second moments.
-/
theorem sqrt_integral_sq_sub_lower
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f p : α → ℝ}
    (hf : MemLp f 2 μ)
    (hp : MemLp p 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) -
        Real.sqrt (∫ x, p x ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, (f x - p x) ^ 2 ∂μ) := by
  have htriangle :
      ‖hf.toLp f‖ ≤
        ‖(hf.sub hp).toLp (f - p)‖ + ‖hp.toLp p‖ := by
    rw [hf.toLp_sub hp]
    calc
      ‖hf.toLp f‖ =
          ‖(hf.toLp f - hp.toLp p) + hp.toLp p‖ := by
            congr 1
            abel
      _ ≤ ‖hf.toLp f - hp.toLp p‖ + ‖hp.toLp p‖ :=
        norm_add_le _ _
  have hresidual :
      Real.sqrt (∫ x, (f x - p x) ^ 2 ∂μ) =
        ‖(hf.sub hp).toLp (f - p)‖ := by
    simpa only [Pi.sub_apply] using
      sqrt_integral_sq_eq_norm_toLp (hf.sub hp)
  rw [sqrt_integral_sq_eq_norm_toLp hf,
    sqrt_integral_sq_eq_norm_toLp hp, hresidual]
  linarith

/--
If the total second moment has coefficient at least `A`, while a model term
has coefficient at most `B < A`, then the residual has the sharp
reverse-triangle coefficient `(sqrt A - sqrt B)²`.
-/
theorem integral_sq_sub_lower_of_integral_sq_bounds
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f p : α → ℝ} {A B L : ℝ}
    (hf : MemLp f 2 μ)
    (hp : MemLp p 2 μ)
    (hL : 0 ≤ L)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hAB : B < A)
    (hF : A * L ≤ ∫ x, f x ^ 2 ∂μ)
    (hP : (∫ x, p x ^ 2 ∂μ) ≤ B * L) :
    (Real.sqrt A - Real.sqrt B) ^ 2 * L ≤
      ∫ x, (f x - p x) ^ 2 ∂μ := by
  have hrootF :
      Real.sqrt A * Real.sqrt L ≤
        Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
    rw [← Real.sqrt_mul hA]
    exact Real.sqrt_le_sqrt hF
  have hrootP :
      Real.sqrt (∫ x, p x ^ 2 ∂μ) ≤
        Real.sqrt B * Real.sqrt L := by
    rw [← Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt hP
  have hreverse := sqrt_integral_sq_sub_lower hf hp
  have hroot :
      (Real.sqrt A - Real.sqrt B) * Real.sqrt L ≤
        Real.sqrt (∫ x, (f x - p x) ^ 2 ∂μ) := by
    nlinarith
  have hdiff : 0 ≤ Real.sqrt A - Real.sqrt B := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hAB.le)
  have hresNonneg :
      0 ≤ ∫ x, (f x - p x) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (f x - p x))
  have hsquare :
      ((Real.sqrt A - Real.sqrt B) * Real.sqrt L) ^ 2 ≤
        (Real.sqrt (∫ x, (f x - p x) ^ 2 ∂μ)) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hdiff (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).2 hroot
  rw [mul_pow, Real.sq_sqrt hL, Real.sq_sqrt hresNonneg] at hsquare
  simpa [mul_assoc] using hsquare

end MathlibAux
