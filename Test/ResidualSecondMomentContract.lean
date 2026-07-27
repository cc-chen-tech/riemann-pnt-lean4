import MathlibAux.ResidualSecondMoment

open MeasureTheory

#check (MathlibAux.sqrt_integral_sq_sub_lower :
  ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α} {f p : α → ℝ},
    MemLp f 2 μ →
    MemLp p 2 μ →
    Real.sqrt (∫ x, f x ^ 2 ∂μ) -
        Real.sqrt (∫ x, p x ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, (f x - p x) ^ 2 ∂μ))

#check (MathlibAux.integral_sq_sub_lower_of_integral_sq_bounds :
  ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α} {f p : α → ℝ} {A B L : ℝ},
    MemLp f 2 μ →
    MemLp p 2 μ →
    0 ≤ L →
    0 ≤ A →
    0 ≤ B →
    B < A →
    A * L ≤ ∫ x, f x ^ 2 ∂μ →
    (∫ x, p x ^ 2 ∂μ) ≤ B * L →
    (Real.sqrt A - Real.sqrt B) ^ 2 * L ≤
      ∫ x, (f x - p x) ^ 2 ∂μ)
