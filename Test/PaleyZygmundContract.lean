import MathlibAux.PaleyZygmund

open MeasureTheory Set

namespace MathlibAux

#check sq_setIntegral_le_measureReal_mul_setIntegral_sq
#check paleyZygmund_mul_secondMoment_le_measure
#check paleyZygmund_measure_lower_bound
#check paleyZygmund_smallMass_measure_upper_bound
#check paleyZygmund_sq_measure_lower_bound

#print axioms sq_setIntegral_le_measureReal_mul_setIntegral_sq
#print axioms paleyZygmund_mul_secondMoment_le_measure
#print axioms paleyZygmund_measure_lower_bound
#print axioms paleyZygmund_smallMass_measure_upper_bound
#print axioms paleyZygmund_sq_measure_lower_bound

example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f : α → ℝ} {θ : ℝ}
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (hμs_pos : 0 < μ.real s)
    (hf : Measurable f) (hf_nonneg : ∀ x ∈ s, 0 ≤ f x)
    (hf_sq : IntegrableOn (fun x => f x ^ 2) s μ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (∫ x in s, f x ∂μ) ^ 2 ≤
      μ.real {x ∈ s | θ * ((∫ y in s, f y ∂μ) / μ.real s) < f x} *
        ∫ x in s, f x ^ 2 ∂μ :=
  paleyZygmund_mul_secondMoment_le_measure hs hμs hμs_pos hf hf_nonneg hf_sq hθ0 hθ1

example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f : α → ℝ} {θ : ℝ}
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (hμs_pos : 0 < μ.real s)
    (hf : Measurable f) (hf_nonneg : ∀ x ∈ s, 0 ≤ f x)
    (hf_sq : IntegrableOn (fun x => f x ^ 2) s μ)
    (hsecond : 0 < ∫ x in s, f x ^ 2 ∂μ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (∫ x in s, f x ∂μ) ^ 2 /
        (∫ x in s, f x ^ 2 ∂μ) ≤
      μ.real {x ∈ s | θ * ((∫ y in s, f y ∂μ) / μ.real s) < f x} :=
  paleyZygmund_measure_lower_bound hs hμs hμs_pos hf hf_nonneg hf_sq hsecond hθ0 hθ1

end MathlibAux
