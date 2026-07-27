import MathlibAux.ScaledPaleyZygmund

open MeasureTheory Set

#check (MathlibAux.measure_sq_largeSet_gt_of_scaled_moments :
  ∀ {α : Type*} [MeasurableSpace α] {μ : Measure α}
      {s : Set α} {g : α → ℝ} {ε L c2 C4 θ : ℝ},
    MeasurableSet s → μ s ≠ ⊤ →
    μ.real s = ε * L →
    0 < ε → 0 < L → 0 < c2 → 0 < C4 →
    Measurable g →
    IntegrableOn (fun x => g x ^ 4) s μ →
    c2 * L < ∫ x in s, g x ^ 2 ∂μ →
    (∫ x in s, g x ^ 4 ∂μ) ≤ C4 * L →
    0 ≤ θ → θ < 1 →
    ((1 - θ) ^ 2 * c2 ^ 2 / C4) * L <
      μ.real {x ∈ s | θ * c2 / ε < g x ^ 2})
