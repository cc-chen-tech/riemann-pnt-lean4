import PrimeNumberTheorem.VKEdgePiOverTwoZetaContour

open Complex Set Polynomial
open scoped BigOperators Interval

open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo
open PrimeNumberTheorem.ExplicitFormulaResidues

#check localizedGaussianWeight
#check differentiable_localizedGaussianWeight
#check exists_weightedExplicitFormula_boundaryRectIntegral_eq_residue_sum
#check exists_regularizedLogDeriv_boundaryRectIntegral_eq_zero_sum
#check riemannZeta_ne_zero_on_localizedContourBoundary_of_goodHeight
#check exists_regularizedLogDeriv_boundaryRectIntegral_eq_zero_sum_of_goodHeight

example (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    Differentiable ℂ (localizedGaussianWeight A w m) :=
  differentiable_localizedGaussianWeight A w m

example (W : ℂ → ℂ) (hW : Differentiable ℂ W)
    {u T : ℝ} (hu : 0 < u) (hT : 0 < T)
    (hboundary :
      ∀ z ∈ ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        ¬((-1 : ℝ) < z.re ∧ z.re < u + 2 ∧
          -T < z.im ∧ z.im < T) →
        riemannZeta z ≠ 0) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, residue p =
        if p = 1 then (1 : ℂ)
        else if p = 0 then
          -deriv riemannZeta 0 / riemannZeta 0
        else
          -(analyticOrderNatAt riemannZeta p : ℂ) / p) ∧
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            (z * W z) *
              explicitFormulaIntegrand 1 z)
          (-1) (u + 2) (-T) T =
        (2 * Real.pi * I) *
          ∑ p ∈ poles, (p * W p) * residue p :=
  exists_weightedExplicitFormula_boundaryRectIntegral_eq_residue_sum
    W hW hu hT hboundary

example (W : ℂ → ℂ) (hW : Differentiable ℂ W)
    {u T : ℝ} (hu : 0 < u) (hT : 0 < T)
    (hboundary :
      ∀ z ∈ ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        ¬((-1 : ℝ) < z.re ∧ z.re < u + 2 ∧
          -T < z.im ∧ z.im < T) →
        riemannZeta z ≠ 0) :
    ∃ zeros : Finset ℂ,
      (∀ rho ∈ zeros,
        riemannZeta rho = 0 ∧
          (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
          -T < rho.im ∧ rho.im < T) ∧
      (∀ rho ∈
          ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        riemannZeta rho = 0 → rho ∈ zeros) ∧
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            W z *
              (-logDeriv riemannZeta z - z / (z - 1)))
          (-1) (u + 2) (-T) T =
        -(2 * Real.pi * I) *
          ∑ rho ∈ zeros,
            (analyticOrderNatAt riemannZeta rho : ℂ) * W rho :=
  exists_regularizedLogDeriv_boundaryRectIntegral_eq_zero_sum
    W hW hu hT hboundary

example {u T : ℝ} (hu : 0 < u) (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∀ z ∈ ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
      ¬((-1 : ℝ) < z.re ∧ z.re < u + 2 ∧
        -T < z.im ∧ z.im < T) →
      riemannZeta z ≠ 0 :=
  riemannZeta_ne_zero_on_localizedContourBoundary_of_goodHeight
    hu hT hgood
