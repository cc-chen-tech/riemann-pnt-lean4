import MathlibAux.TriangleKernelFourier

open MeasureTheory Set

namespace MathlibAux

/-!
# Contract for the triangle-kernel Fourier transform
-/

example {H c : ℝ} (hH : 0 ≤ H) (hc : c ≠ 0) :
    (∫ τ in (-H)..H, (H - |τ|) * Real.cos (c * τ)) =
      2 * (1 - Real.cos (c * H)) / c ^ 2 :=
  integral_triangleKernel_mul_cos_eq hH hc

example {H c : ℝ} (hH : 0 ≤ H) (hc : c ≠ 0) :
    |∫ τ in (-H)..H, (H - |τ|) * Real.cos (c * τ)| ≤ 4 / c ^ 2 :=
  abs_triangleKernel_mul_cos_integral_le hH hc

#print axioms integral_triangleKernel_mul_cos_eq
#print axioms abs_triangleKernel_mul_cos_integral_le

end MathlibAux
