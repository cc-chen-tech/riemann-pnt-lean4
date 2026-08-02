import MathlibAux.SlidingLagBudget

open MeasureTheory Set

namespace MathlibAux

example {H tau : ℝ} (hH : 0 ≤ H) (htau : tau ∈ Icc (-H) H) :
    min H (H - tau) - max 0 (-tau) = H - |tau| :=
  lagSection_length hH htau

example {E : ℝ → ℝ → ℝ} (hE : Continuous (Function.uncurry E)) {H : ℝ} :
    ContinuousOn (fun tau => ∫ v in max 0 (-tau)..min H (H - tau), E v tau)
      (Icc (0 : ℝ) H) :=
  continuousOn_lagInner_right hE

example {E : ℝ → ℝ → ℝ} (hE : Continuous (Function.uncurry E)) {H : ℝ} :
    ContinuousOn (fun tau => ∫ v in max 0 (-tau)..min H (H - tau), E v tau)
      (Icc (-H) (0 : ℝ)) :=
  continuousOn_lagInner_left hE

example {E : ℝ → ℝ → ℝ} (hE : Continuous (Function.uncurry E))
    {H : ℝ} (hH : 0 ≤ H) :
    ContinuousOn (fun tau => ∫ v in max 0 (-tau)..min H (H - tau), E v tau)
      (Icc (-H) H) :=
  continuousOn_lagInner hE hH

example {H : ℝ} (hH : 0 ≤ H) :
    (∫ tau in (-H)..H, (H - |tau|)) = H ^ 2 :=
  integral_triangleKernel_eq_sq hH

example {M : ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hM : Continuous M) (hE : Continuous (Function.uncurry E))
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ tau in (-H)..H, ∫ v in max 0 (-tau)..min H (H - tau), (M tau + E v tau)) =
      (∫ tau in (-H)..H, (H - |tau|) * M tau) +
        ∫ tau in (-H)..H, ∫ v in max 0 (-tau)..min H (H - tau), E v tau :=
  intervalIntegral_lagIntegral_add hM hE hH

example {E : ℝ → ℝ → ℝ}
    (hE : Continuous (Function.uncurry E)) {H epsilon : ℝ}
    (hH : 0 ≤ H) (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ v tau : ℝ, |E v tau| ≤ epsilon) :
    |∫ tau in (-H)..H, ∫ v in max 0 (-tau)..min H (H - tau), E v tau| ≤
      epsilon * H ^ 2 :=
  abs_lagIntegral_le_of_forall_norm_le hE hH hepsilon hbound

#print axioms lagSection_length
#print axioms continuousOn_lagInner_right
#print axioms continuousOn_lagInner_left
#print axioms continuousOn_lagInner
#print axioms integral_triangleKernel_eq_sq
#print axioms intervalIntegral_lagIntegral_add
#print axioms abs_lagIntegral_le_of_forall_norm_le

end MathlibAux
