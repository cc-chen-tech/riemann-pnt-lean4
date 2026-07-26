import PrimeNumberTheorem.VKEdgePiOverTwoCenteredContour

open Complex MeasureTheory Polynomial Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check localizedRegularizedLogDerivIntegrandAtCenter
#check differentiable_localizedGaussianWeightAtCenter
#check integral_localizedRegularizedLogDerivIntegrandAtCenter_verticalLine_eq
#check localizedZeroResidueSumAtCenter
#check localizedOtherEdgeContributionAtCenter
#check localizedRightEdgeTailAtCenter
#check localizedContourRemainderAtCenter
#check exists_rightEdgeIntegralAtCenter_eq_zero_sum_add_other_edges_of_goodHeight
#check exists_localizedPsiGaussianAverageAtCenter_eq_zeroSum_add_contourRemainder_of_goodHeight
#check localizedRegularizedLogDerivIntegrandAtCenter_sixteen
#check localizedZeroResidueSumAtCenter_sixteen
#check localizedOtherEdgeContributionAtCenter_sixteen
#check localizedRightEdgeTailAtCenter_sixteen
#check localizedContourRemainderAtCenter_sixteen

example (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ) (z : ℂ) :
    localizedRegularizedLogDerivIntegrandAtCenter q A w m z =
      localizedGaussianWeightAtCenter q A w m z *
        (-logDeriv riemannZeta z - z / (z - 1)) := by
  rfl

example (q : ℝ) (A : ℂ[X]) (w : ℂ) (m u T : ℝ) :
    localizedContourRemainderAtCenter q A w m u T =
      localizedOtherEdgeContributionAtCenter q A w m u T +
        localizedRightEdgeTailAtCenter q A w m u T := by
  rfl

example (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ)
    (zeros : Finset ℂ) :
    localizedZeroResidueSumAtCenter q A w m zeros =
      ∑ rho ∈ zeros,
        (analyticOrderNatAt riemannZeta rho : ℂ) *
          localizedGaussianWeightAtCenter q A w m rho := by
  rfl

example (q : ℝ) (A : ℂ[X]) {u v m T : ℝ}
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
      localizedPsiGaussianAverageAtCenter q A
          ((u : ℂ) + I * v) m =
        -(2 * Real.pi : ℂ) *
            localizedZeroResidueSumAtCenter q A
              ((u : ℂ) + I * v) m zeros +
          localizedContourRemainderAtCenter q A
            ((u : ℂ) + I * v) m u T :=
  exists_localizedPsiGaussianAverageAtCenter_eq_zeroSum_add_contourRemainder_of_goodHeight
    q A hu hm hT hgood

example (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedRegularizedLogDerivIntegrandAtCenter 16 A w m =
      localizedRegularizedLogDerivIntegrand A w m :=
  localizedRegularizedLogDerivIntegrandAtCenter_sixteen A w m

example (A : ℂ[X]) (w : ℂ) (m : ℝ) (zeros : Finset ℂ) :
    localizedZeroResidueSumAtCenter 16 A w m zeros =
      localizedZeroResidueSum A w m zeros :=
  localizedZeroResidueSumAtCenter_sixteen A w m zeros

example (A : ℂ[X]) (w : ℂ) (m u T : ℝ) :
    localizedOtherEdgeContributionAtCenter 16 A w m u T =
      localizedOtherEdgeContribution A w m u T :=
  localizedOtherEdgeContributionAtCenter_sixteen A w m u T

example (A : ℂ[X]) (w : ℂ) (m u T : ℝ) :
    localizedRightEdgeTailAtCenter 16 A w m u T =
      localizedRightEdgeTail A w m u T :=
  localizedRightEdgeTailAtCenter_sixteen A w m u T

example (A : ℂ[X]) (w : ℂ) (m u T : ℝ) :
    localizedContourRemainderAtCenter 16 A w m u T =
      localizedContourRemainder A w m u T :=
  localizedContourRemainderAtCenter_sixteen A w m u T

end PrimeNumberTheorem.VKEdgePiOverTwo
