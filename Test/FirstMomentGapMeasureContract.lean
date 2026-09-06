import MathlibAux.FirstMomentGapMeasure

open MeasureTheory Set

namespace MathlibAux

example
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s e : Set α} {A B : α → ℝ} {L R M : ℝ}
    (hs : MeasurableSet s) (he : MeasurableSet e)
    (hμe : μ e ≠ ⊤) (hes : e ⊆ s)
    (hAint : IntegrableOn A s μ) (hBint : IntegrableOn B s μ)
    (hgapSqInt : IntegrableOn (fun x => (A x - B x) ^ 2) e μ)
    (hzero : ∀ x ∈ s \ e, A x - B x = 0)
    (hfirst : L ≤ ∫ x in s, A x ∂μ)
    (hsigned : (∫ x in s, B x ∂μ) ≤ R)
    (hsecond : (∫ x in e, (A x - B x) ^ 2 ∂μ) ≤ M)
    (hgap : 0 ≤ L - R) :
    (L - R) ^ 2 ≤ μ.real e * M :=
  firstMomentGap_sq_le_measureReal_mul_secondMoment
    hs he hμe hes hAint hBint hgapSqInt hzero hfirst hsigned hsecond hgap

#print axioms firstMomentGap_sq_le_measureReal_mul_secondMoment

end MathlibAux
