import MathlibAux.LpPointwiseDerivBridge

open Filter MeasureTheory
open scoped Topology

example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℂ → α → ℂ) (hf : ∀ z, MemLp (f z) 2 μ)
    {z : ℂ} {f' : α → ℂ} (hf' : MemLp f' 2 μ)
    (hlim : Tendsto
      (fun u : ℂ => ∫ t,
        ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2 ∂μ)
      (𝓝[≠] z) (𝓝 0)) :
    HasDerivAt
      (fun u : ℂ => (hf u).toLp (f u))
      (hf'.toLp f') z :=
  hasDerivAt_memLpToLp_of_tendsto_integral_pointwiseSlope_sq
    f hf hf' hlim

#print axioms hasDerivAt_memLpToLp_of_tendsto_integral_pointwiseSlope_sq

example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℂ → α → ℂ) {z : ℂ} {f' : α → ℂ} {bound : α → ℝ}
    (hMeas : ∀ᶠ u in 𝓝[≠] z,
      AEStronglyMeasurable
        (fun t => ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2) μ)
    (hBound : ∀ᶠ u in 𝓝[≠] z, ∀ᵐ t ∂μ,
      ‖(‖pointwiseComplexSlope f z u t - f' t‖ ^ 2 : ℝ)‖ ≤ bound t)
    (hBoundInt : Integrable bound μ)
    (hDeriv : ∀ᵐ t ∂μ, HasDerivAt (fun u => f u t) (f' t) z) :
    Tendsto
      (fun u : ℂ => ∫ t,
        ‖pointwiseComplexSlope f z u t - f' t‖ ^ 2 ∂μ)
      (𝓝[≠] z) (𝓝 0) :=
  tendsto_integral_pointwiseSlope_sq_of_dominated
    f hMeas hBound hBoundInt hDeriv

#print axioms tendsto_integral_pointwiseSlope_sq_of_dominated

example {α : Type*} (f f' : ℂ → α → ℂ) {z : ℂ} {r : ℝ}
    {B : α → ℝ} (hr : 0 ≤ r)
    (hDeriv : ∀ v ∈ Metric.closedBall z r, ∀ t,
      HasDerivAt (fun u => f u t) (f' v t) v)
    (hB : ∀ t, 0 ≤ B t)
    (hDerivSq : ∀ v ∈ Metric.closedBall z r, ∀ t,
      ‖f' v t‖ ^ 2 ≤ B t) :
    ∀ u ∈ Metric.closedBall z r, u ≠ z → ∀ t,
      ‖pointwiseComplexSlope f z u t - f' z t‖ ^ 2 ≤ 4 * B t :=
  pointwiseSlope_error_sq_le_four_mul_of_deriv_sq_le
    f f' hr hDeriv hB hDerivSq

#print axioms pointwiseSlope_error_sq_le_four_mul_of_deriv_sq_le
