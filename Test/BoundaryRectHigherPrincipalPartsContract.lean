import MathlibAux.BoundaryRectHigherPrincipalParts

open Complex

namespace MathlibAux

example {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    boundaryRectIntegral (fun z : ℂ => z⁻¹ ^ 2) x0 x1 y0 y1 = 0 :=
  boundaryRectIntegral_inv_sq_eq_zero hx0 hx1 hy0 hy1

example {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    boundaryRectIntegral (fun z : ℂ => z⁻¹ ^ 3) x0 x1 y0 y1 = 0 :=
  boundaryRectIntegral_inv_cube_eq_zero hx0 hx1 hy0 hy1

example (A : ℂ) {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    boundaryRectIntegral (fun z : ℂ => A * z⁻¹ ^ 2) x0 x1 y0 y1 = 0 :=
  boundaryRectIntegral_const_mul_inv_sq_eq_zero A hx0 hx1 hy0 hy1

example (A : ℂ) {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    boundaryRectIntegral (fun z : ℂ => A * z⁻¹ ^ 3) x0 x1 y0 y1 = 0 :=
  boundaryRectIntegral_const_mul_inv_cube_eq_zero A hx0 hx1 hy0 hy1

end MathlibAux
