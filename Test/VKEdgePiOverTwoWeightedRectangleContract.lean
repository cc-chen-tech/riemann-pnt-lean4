import PrimeNumberTheorem.VKEdgePiOverTwoWeightedRectangle

open Complex Set
open scoped BigOperators Interval

#check MathlibAux.rectangleBoundaryIntegral_mul_analyticWeight_eq_residue_sum
#check MathlibAux.boundaryRectIntegral_mul_analyticWeight_eq_residue_sum

example {g W : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (MathlibAux.closedRectangle c R))
    (hW : Differentiable ℂ W)
    (hpoles : ∀ p ∈ poles, p ∈ MathlibAux.openRectangle c R) :
    MathlibAux.rectangleBoundaryIntegral
        (fun z : ℂ =>
          W z * (g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p))
        c R =
      (2 * Real.pi * I) *
        ∑ p ∈ poles, W p * residue p :=
  MathlibAux.rectangleBoundaryIntegral_mul_analyticWeight_eq_residue_sum
    hR poles residue hg hW hpoles

example {g W : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g
      ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hW : Differentiable ℂ W)
    (hpoles : ∀ p ∈ poles,
      x0 < p.re ∧ p.re < x1 ∧ y0 < p.im ∧ p.im < y1) :
    MathlibAux.boundaryRectIntegral
        (fun z : ℂ =>
          W z * (g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p))
        x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ p ∈ poles, W p * residue p :=
  MathlibAux.boundaryRectIntegral_mul_analyticWeight_eq_residue_sum
    poles residue hg hW hpoles
