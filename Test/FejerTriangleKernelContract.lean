import MathlibAux.FejerTriangleKernel

open MeasureTheory Set

namespace MathlibAux

/-!
# Contract for the triangle-kernel identity
-/

example {f : ℝ → ℝ} (hf : Continuous f) {H : ℝ} (hH : 0 ≤ H) :
    (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, f (w - v)) =
      ∫ τ in (-H)..H, (H - |τ|) * f τ :=
  intervalIntegral_pair_sub_eq_triangle_kernel hf hH

#print axioms intervalIntegral_pair_sub_eq_triangle_kernel

end MathlibAux
