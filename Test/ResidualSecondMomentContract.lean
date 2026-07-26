import MathlibAux.ResidualSecondMoment

open MeasureTheory

#check MathlibAux.integral_sq_sub_lower_of_integral_sq_bounds

example
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
      ∫ x, (f x - p x) ^ 2 ∂μ :=
  MathlibAux.integral_sq_sub_lower_of_integral_sq_bounds
    hf hp hL hA hB hAB hF hP
