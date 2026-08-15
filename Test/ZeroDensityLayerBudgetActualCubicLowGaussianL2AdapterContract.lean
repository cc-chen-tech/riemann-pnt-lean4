import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicLowGaussianL2Adapter

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem

noncomputable section

example (rho : ℂ) : actualCubicDyadicUnitBucket rho = ⌊rho.im⌋₊ := rfl

example (x beta : ℝ) (rho : ℂ) :
    actualCubicTargetNormalizedCoefficientSquare x beta rho =
      x ^ (-2 * beta) *
        (((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
          (x ^ (2 * rho.re) / ‖rho‖ ^ 4)) := rfl

example (x beta : ℝ) (rho : ℂ) :
    actualCubicTargetNormalizedCoefficientMass x beta rho =
      Real.sqrt (actualCubicTargetNormalizedCoefficientSquare x beta rho) := rfl

example (sigma : ℝ) (rho : ℂ) :
    actualCubicDyadicStripBackwardDrift sigma rho = sigma - rho.re := rfl

example (x beta sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (t m : ℝ) :
    actualCubicDyadicStripGaussianGramExcluding x beta sigma tau n S t m =
      MathlibAux.dyadicDriftingGaussianGram
        (actualCarlsonDyadicZeroStrip sigma tau n \ S)
        (actualCubicTargetNormalizedCoefficientMass x beta)
        (actualCubicDyadicStripBackwardDrift sigma)
        (fun rho => rho.im) t m := rfl

example (x beta : ℝ) (rho : ℂ) (hx : 0 ≤ x) :
    0 ≤ actualCubicTargetNormalizedCoefficientSquare x beta rho :=
  actualCubicTargetNormalizedCoefficientSquare_nonneg x beta rho hx

example (x beta : ℝ) (rho : ℂ) :
    0 ≤ actualCubicTargetNormalizedCoefficientMass x beta rho :=
  actualCubicTargetNormalizedCoefficientMass_nonneg x beta rho

example (x beta : ℝ) (rho : ℂ) (hx : 0 ≤ x) :
    actualCubicTargetNormalizedCoefficientMass x beta rho ^ 2 =
      actualCubicTargetNormalizedCoefficientSquare x beta rho :=
  actualCubicTargetNormalizedCoefficientMass_sq_eq x beta rho hx

example (x beta sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (hx : 0 ≤ x) :
    (∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
        actualCubicTargetNormalizedCoefficientMass x beta rho ^ 2) =
      x ^ (-2 * beta) *
        actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S :=
  sum_actualCubicTargetNormalizedCoefficientMass_sq_eq_capacity
    x beta sigma tau n S hx

example {x beta sigma tau t m : ℝ} (n occupancy : ℕ) (S : Finset ℂ)
    (hx : 0 ≤ x) (ht : 0 ≤ t) (hm : 1 ≤ m)
    (hoccupancy :
      ∀ q ∈ (actualCarlsonDyadicZeroStrip sigma tau n \ S).image
          actualCubicDyadicUnitBucket,
        ((actualCarlsonDyadicZeroStrip sigma tau n \ S).filter fun rho =>
          actualCubicDyadicUnitBucket rho = q).card ≤ occupancy + 1) :
    actualCubicDyadicStripGaussianGramExcluding
        x beta sigma tau n S t m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ((occupancy + 1 : ℕ) : ℝ) *
          (x ^ (-2 * beta) *
            actualCubicDyadicStripSquareCapacityExcluding
              x sigma tau n S) :=
  actualCubicDyadicStripGaussianGramExcluding_le_occupancy_mul_capacity
    n occupancy S hx ht hm hoccupancy

end

end PrimeNumberTheorem
