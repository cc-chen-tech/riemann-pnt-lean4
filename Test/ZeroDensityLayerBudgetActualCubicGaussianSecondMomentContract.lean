import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicGaussianSecondMoment

open Complex

namespace PrimeNumberTheorem

noncomputable section

example (x beta : ℝ) (rho : ℂ) :
    actualCubicRawNormalizedCoefficient x beta rho =
      -((analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho ^ 3) *
        (x : ℂ) ^ (-beta : ℂ) := rfl

example (x beta : ℝ) (rho : ℂ) :
    actualCubicPhaseFaithfulCoefficient x beta rho =
      (actualCubicTargetNormalizedCoefficientMass x beta rho : ℂ) *
        Complex.exp (Complex.I * (actualCubicRawNormalizedCoefficient x beta rho).arg) := rfl

example (x beta : ℝ) (rho : ℂ) :
    ‖actualCubicPhaseFaithfulCoefficient x beta rho‖ =
      actualCubicTargetNormalizedCoefficientMass x beta rho :=
  norm_actualCubicPhaseFaithfulCoefficient x beta rho

example (x beta sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (t width : ℝ) :
    actualCubicDyadicStripGaussianSecondMomentExcluding
        x beta sigma tau n S t width =
      MathlibAux.gaussianWeightedSecondMoment
        (actualCarlsonDyadicZeroStrip sigma tau n \ S)
        (actualCubicPhaseFaithfulCoefficient x beta)
        (actualCubicDyadicStripBackwardDrift sigma)
        (fun rho => rho.im) t width := rfl

example (x beta sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (t : ℝ)
    {width : ℝ} (hwidth : 0 < width) :
    actualCubicDyadicStripGaussianSecondMomentExcluding
        x beta sigma tau n S t width ≤
      actualCubicDyadicStripGaussianGramExcluding
        x beta sigma tau n S t width :=
  actualCubicDyadicStripGaussianSecondMomentExcluding_le_gram
    x beta sigma tau n S t hwidth

end

end PrimeNumberTheorem
