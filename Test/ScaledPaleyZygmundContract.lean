import MathlibAux.ScaledPaleyZygmund

open MeasureTheory Set

#check MathlibAux.measure_sq_largeSet_gt_of_scaled_moments

example
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {g : α → ℝ} {ε L c2 C4 θ : ℝ}
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (hmeasure : μ.real s = ε * L)
    (hε : 0 < ε) (hL : 0 < L)
    (hc2 : 0 < c2) (hC4 : 0 < C4)
    (hg : Measurable g)
    (hg4 : IntegrableOn (fun x => g x ^ 4) s μ)
    (hsecond : c2 * L < ∫ x in s, g x ^ 2 ∂μ)
    (hfourth : (∫ x in s, g x ^ 4 ∂μ) ≤ C4 * L)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ((1 - θ) ^ 2 * c2 ^ 2 / C4) * L <
      μ.real {x ∈ s | θ * c2 / ε < g x ^ 2} :=
  MathlibAux.measure_sq_largeSet_gt_of_scaled_moments
    hs hμs hmeasure hε hL hc2 hC4 hg hg4 hsecond hfourth hθ0 hθ1
