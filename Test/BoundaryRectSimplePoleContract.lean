import MathlibAux.RectangleResidue

open Complex Set
open scoped Interval

namespace MathlibAux

#check boundaryRectIntegral_sub_inv_of_mem_openRect
#check boundaryRectIntegral_eq_simple_pole_residue_of_differentiableOn
#check boundaryRectIntegral_congr_of_eqOn_boundary

example (p : ℂ) {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 < p.re) (hx1 : p.re < x1)
    (hy0 : y0 < p.im) (hy1 : p.im < y1) :
    boundaryRectIntegral (fun z : ℂ => (z - p)⁻¹) x0 x1 y0 y1 =
      2 * Real.pi * I := by
  exact boundaryRectIntegral_sub_inv_of_mem_openRect p hx0 hx1 hy0 hy1

example {g : ℂ → ℂ} {p a : ℂ} {x0 x1 y0 y1 : ℝ}
    (hg : DifferentiableOn ℂ g ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hx0 : x0 < p.re) (hx1 : p.re < x1)
    (hy0 : y0 < p.im) (hy1 : p.im < y1) :
    boundaryRectIntegral (fun z => g z + (z - p)⁻¹ * a)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) * a := by
  exact boundaryRectIntegral_eq_simple_pole_residue_of_differentiableOn
    hg hx0 hx1 hy0 hy1

end MathlibAux
