import PrimeNumberTheorem.VKEdgePiOverTwoConcreteContourAssembly

open Complex Polynomial Set
open scoped BigOperators Interval

open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check localizedRegularizedLogDerivIntegrand
#check exists_rightEdgeIntegral_eq_zero_sum_add_other_edges_of_goodHeight

example (A : ℂ[X]) {u v m T : ℝ}
    (hu : 0 < u) (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∃ zeros : Finset ℂ,
      (∀ rho ∈ zeros,
        riemannZeta rho = 0 ∧
          (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
          -T < rho.im ∧ rho.im < T) ∧
      (∀ rho ∈
          ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        riemannZeta rho = 0 → rho ∈ zeros) ∧
      (∫ t : ℝ in (-T)..T,
          localizedRegularizedLogDerivIntegrand A
            ((u : ℂ) + I * v) m
            (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        -(2 * Real.pi : ℂ) *
            ∑ rho ∈ zeros,
              (analyticOrderNatAt riemannZeta rho : ℂ) *
                localizedGaussianWeight A
                  ((u : ℂ) + I * v) m rho +
          I *
            ((∫ σ : ℝ in (-1)..(u + 2),
                localizedRegularizedLogDerivIntegrand A
                  ((u : ℂ) + I * v) m
                  ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
              ∫ σ : ℝ in (-1)..(u + 2),
                localizedRegularizedLogDerivIntegrand A
                  ((u : ℂ) + I * v) m
                  ((σ : ℂ) + (T : ℂ) * I)) +
          (∫ t : ℝ in (-T)..T,
            localizedRegularizedLogDerivIntegrand A
              ((u : ℂ) + I * v) m
              ((-1 : ℂ) + (t : ℂ) * I)) :=
  exists_rightEdgeIntegral_eq_zero_sum_add_other_edges_of_goodHeight
    A hu hT hgood
