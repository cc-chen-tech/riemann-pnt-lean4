import PrimeNumberTheorem.LittlewoodRectangleLogNorm

set_option autoImplicit false

open Complex Set
open PrimeNumberTheorem.CarlsonZeroDensity

example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hx : x0 ≤ x1) (hy : y0 ≤ y1)
    (hf : AnalyticOnNhd ℂ f (Icc x0 x1 ×ℂ Icc y0 y1))
    (hleft : ∀ y ∈ Icc y0 y1, f ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Icc y0 y1, f ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Icc x0 x1, f ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Icc x0 x1, f ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    rectangleLittlewoodFourEdges f x0 x1 y0 y1 =
      rectangleLittlewoodLogNormForm f x0 x1 y0 y1 :=
  rectangleLittlewoodFourEdges_eq_logNormForm hx hy hf hleft hright hbottom htop

#print axioms rectangleLittlewoodFourEdges_eq_logNormForm
