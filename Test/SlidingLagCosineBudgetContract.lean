import MathlibAux.SlidingLagCosineBudget

open MeasureTheory Set

namespace MathlibAux

example {E : ℝ → ℝ → ℝ} (hE : Continuous (Function.uncurry E))
    {H K c epsilon : ℝ} (hH : 0 ≤ H) (hc : c ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ v tau : ℝ, |E v tau| ≤ epsilon) :
    |∫ tau in (-H)..H,
        ∫ v in max 0 (-tau)..min H (H - tau),
          (K * Real.cos (c * tau) + E v tau)| ≤
      |K| * (4 / c ^ 2) + epsilon * H ^ 2 :=
  abs_lagIntegral_le_cosine_main_add_uniform_error hE hH hc hepsilon hbound

example {E : ℝ → ℝ → ℝ} (hE : Continuous (Function.uncurry E))
    {H K c epsilon : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) (hc : c ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ v tau : ℝ, |E v tau| ≤ epsilon) :
    |∫ tau in (-H)..H,
        ∫ v in max 0 (-tau)..min H (H - tau),
          (K * Real.cos (c * tau) + E v tau)| ≤
      K * (4 / c ^ 2) + epsilon * H ^ 2 :=
  abs_lagIntegral_le_cosine_main_add_uniform_error_of_nonneg
    hE hH hK hc hepsilon hbound

example {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    {H K c epsilon : ℝ} (hH : 0 ≤ H) (hc : c ≠ 0)
    (hbound : ∀ v ∈ Icc (0 : ℝ) H, ∀ w ∈ Icc (0 : ℝ) H,
      |F v w - K * Real.cos (c * (w - v))| ≤ epsilon) :
    |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, F v w| ≤
      |K| * (4 / c ^ 2) + epsilon * H ^ 2 :=
  abs_squareIntegral_le_cosine_difference_main_add_uniform_error
    hF hH hc hbound

end MathlibAux
