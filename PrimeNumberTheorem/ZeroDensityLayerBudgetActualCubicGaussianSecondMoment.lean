import MathlibAux.GaussianExponentialPolynomialParseval
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicLowGaussianL2Adapter

open Complex
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem

noncomputable section

/-- The actual normalized cubic zero coefficient before separating its phase and mass. -/
def actualCubicRawNormalizedCoefficient (x beta : ℝ) (rho : ℂ) : ℂ :=
  -((analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho ^ 3) *
    (x : ℂ) ^ (-beta : ℂ)

/-- The existing Carlson cubic mass equipped with the phase of the actual cubic zero term. -/
def actualCubicPhaseFaithfulCoefficient (x beta : ℝ) (rho : ℂ) : ℂ :=
  (actualCubicTargetNormalizedCoefficientMass x beta rho : ℂ) *
    Complex.exp (Complex.I * (actualCubicRawNormalizedCoefficient x beta rho).arg)

theorem norm_actualCubicPhaseFaithfulCoefficient (x beta : ℝ) (rho : ℂ) :
    ‖actualCubicPhaseFaithfulCoefficient x beta rho‖ =
      actualCubicTargetNormalizedCoefficientMass x beta rho := by
  rw [actualCubicPhaseFaithfulCoefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (actualCubicTargetNormalizedCoefficientMass_nonneg x beta rho),
    Complex.norm_exp]
  have hreal :
      (Complex.I * (actualCubicRawNormalizedCoefficient x beta rho).arg).re = 0 := by
    simp
  rw [hreal]
  simp

/-- Gaussian second moment of the phase-faithful cubic zero polynomial in one dyadic strip. -/
def actualCubicDyadicStripGaussianSecondMomentExcluding
    (x beta sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (t width : ℝ) : ℝ :=
  MathlibAux.gaussianWeightedSecondMoment
    (actualCarlsonDyadicZeroStrip sigma tau n \ S)
    (actualCubicPhaseFaithfulCoefficient x beta)
    (actualCubicDyadicStripBackwardDrift sigma)
    (fun rho => rho.im) t width

/-- Forgetting phases costs no extra constant: the actual second moment is bounded by the
positive-mass drifting Gram already controlled by Carlson capacity and occupancy. -/
theorem actualCubicDyadicStripGaussianSecondMomentExcluding_le_gram
    (x beta sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (t : ℝ)
    {width : ℝ} (hwidth : 0 < width) :
    actualCubicDyadicStripGaussianSecondMomentExcluding
        x beta sigma tau n S t width ≤
      actualCubicDyadicStripGaussianGramExcluding
        x beta sigma tau n S t width := by
  apply MathlibAux.gaussianWeightedSecondMoment_le_driftingGram
    (actualCarlsonDyadicZeroStrip sigma tau n \ S)
    (actualCubicPhaseFaithfulCoefficient x beta)
    (actualCubicTargetNormalizedCoefficientMass x beta)
    (actualCubicDyadicStripBackwardDrift sigma)
    (fun rho => rho.im) t hwidth
  intro rho hrho
  exact norm_actualCubicPhaseFaithfulCoefficient x beta rho

end

end PrimeNumberTheorem
