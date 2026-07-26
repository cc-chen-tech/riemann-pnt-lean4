import PrimeNumberTheorem.VKEdgePiOverTwoConcreteContourAssembly

open Complex Polynomial Set
open scoped BigOperators Interval

open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check localizedRegularizedLogDerivIntegrand
#check integral_localizedRegularizedLogDerivIntegrand_verticalLine_eq
#check integrable_localizedRegularizedLogDerivIntegrand_verticalLine
#check localizedPsiGaussianAverage
#check localizedZeroResidueSum
#check localizedOtherEdgeContribution
#check localizedRightEdgeTail
#check localizedContourRemainder
#check localizedHorizontalEdgeUpperBound
#check localizedLeftEdgeUpperBound
#check localizedOtherEdgeUpperBound
#check exists_goodHeight_Icc_norm_localizedOtherEdgeContribution_le
#check tendsto_localizedRightEdgeTail_atTop
#check exists_rightEdgeIntegral_eq_zero_sum_add_other_edges_of_goodHeight
#check exists_localizedPsiGaussianAverage_eq_zeroSum_add_contourRemainder_of_goodHeight

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

example (A : ℂ[X]) {u v m T : ℝ}
    (hu : 0 < u) (hm : 0 < m) (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∃ zeros : Finset ℂ,
      (∀ rho ∈ zeros,
        riemannZeta rho = 0 ∧
          (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
          -T < rho.im ∧ rho.im < T) ∧
      (∀ rho ∈
          ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        riemannZeta rho = 0 → rho ∈ zeros) ∧
      localizedPsiGaussianAverage A ((u : ℂ) + I * v) m =
        -(2 * Real.pi : ℂ) *
            localizedZeroResidueSum A ((u : ℂ) + I * v) m zeros +
          localizedContourRemainder A ((u : ℂ) + I * v) m u T :=
  exists_localizedPsiGaussianAverage_eq_zeroSum_add_contourRemainder_of_goodHeight
    A hu hm hT hgood
