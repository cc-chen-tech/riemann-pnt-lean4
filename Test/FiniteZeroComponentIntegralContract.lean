import MathlibAux.FiniteZeroComponentIntegral

open Set MeasureTheory
open scoped BigOperators Interval

-- The complete disjoint open partition omits only a finite set; no term may
-- be double-counted or discarded. q is the continuous real trace, not the
-- possibly nonintegrable complex logarithmic derivative.
example {ι : Type*} [Fintype ι] {a b : ι → ℝ} {q : ℝ → ℝ}
    {K : Finset ℝ} {U T : ℝ} (hUT : U < T)
    (hgeom : ∀ i, U ≤ a i ∧ a i < b i ∧ b i ≤ T)
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hcover : ∀ t ∈ Ioo U T, t ∉ K ↔ ∃ i, t ∈ Ioo (a i) (b i))
    (hq : ContinuousOn q (Icc U T)) :
    (∑ i, ∫ t in a i..b i, q t) = ∫ t in U..T, q t := by
  exact MathlibAux.sum_intervalIntegral_eq_of_finite_complement hUT hgeom hdisjoint hcover hq

#print axioms MathlibAux.sum_intervalIntegral_eq_of_finite_complement
