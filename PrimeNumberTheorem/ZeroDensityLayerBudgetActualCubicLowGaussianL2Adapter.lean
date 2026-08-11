import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicLowDyadicCapacity
import PrimeNumberTheorem.HalfIsolatedZetaDyadicAdapter

/-!
# Actual cubic low-layer Gaussian L2 adapter

This module connects the actual cubic explicit-formula coefficient capacity to
the Gram/Schur interface supplied by the half-isolated development.  It works
on the genuine Carlson dyadic strip after deleting an arbitrary finite set.

The coefficient square is exactly the target-normalized third-order mass

`x^(-2 * beta) * multiplicity(rho)^2 * x^(2 Re rho) / |rho|^6`.

The only local clustering input is an explicit unit-ordinate occupancy bound.
No occupancy, separation, Gram estimate, or zero-density theorem is reproved
here.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem

noncomputable section

/-- The natural unit-ordinate bucket containing a positive-ordinate zero. -/
noncomputable def actualCubicDyadicUnitBucket (rho : ℂ) : ℕ :=
  ⌊rho.im⌋₊

/-- Exact target-normalized square of one actual cubic zero coefficient. -/
noncomputable def actualCubicTargetNormalizedCoefficientSquare
    (x beta : ℝ) (rho : ℂ) : ℝ :=
  x ^ (-2 * beta) *
    (((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
      (x ^ (2 * rho.re) / ‖rho‖ ^ 4))

/-- Nonnegative magnitude corresponding to the exact cubic coefficient
square. -/
noncomputable def actualCubicTargetNormalizedCoefficientMass
    (x beta : ℝ) (rho : ℂ) : ℝ :=
  Real.sqrt (actualCubicTargetNormalizedCoefficientSquare x beta rho)

/-- Backward real-part drift from the left endpoint of a Carlson strip. -/
def actualCubicDyadicStripBackwardDrift (sigma : ℝ) (rho : ℂ) : ℝ :=
  sigma - rho.re

/-- Actual finite Gaussian Gram energy for one cubic Carlson strip after
deleting `S`. -/
noncomputable def actualCubicDyadicStripGaussianGramExcluding
    (x beta sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (t m : ℝ) : ℝ :=
  MathlibAux.dyadicDriftingGaussianGram
    (actualCarlsonDyadicZeroStrip sigma tau n \ S)
    (actualCubicTargetNormalizedCoefficientMass x beta)
    (actualCubicDyadicStripBackwardDrift sigma)
    (fun rho => rho.im) t m

theorem actualCubicTargetNormalizedCoefficientSquare_nonneg
    (x beta : ℝ) (rho : ℂ) (hx : 0 ≤ x) :
    0 ≤ actualCubicTargetNormalizedCoefficientSquare x beta rho := by
  unfold actualCubicTargetNormalizedCoefficientSquare
  exact mul_nonneg (Real.rpow_nonneg hx _)
    (mul_nonneg
      (div_nonneg (sq_nonneg _) (sq_nonneg _))
      (div_nonneg (Real.rpow_nonneg hx _) (by positivity)))

theorem actualCubicTargetNormalizedCoefficientMass_nonneg
    (x beta : ℝ) (rho : ℂ) :
    0 ≤ actualCubicTargetNormalizedCoefficientMass x beta rho := by
  exact Real.sqrt_nonneg _

theorem actualCubicTargetNormalizedCoefficientMass_sq_eq
    (x beta : ℝ) (rho : ℂ) (hx : 0 ≤ x) :
    actualCubicTargetNormalizedCoefficientMass x beta rho ^ 2 =
      actualCubicTargetNormalizedCoefficientSquare x beta rho := by
  unfold actualCubicTargetNormalizedCoefficientMass
  exact Real.sq_sqrt
    (actualCubicTargetNormalizedCoefficientSquare_nonneg x beta rho hx)

/-- The diagonal square mass of the actual cubic Gram is exactly the
target-normalized Carlson capacity from the preceding layer. -/
theorem sum_actualCubicTargetNormalizedCoefficientMass_sq_eq_capacity
    (x beta sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (hx : 0 ≤ x) :
    (∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
        actualCubicTargetNormalizedCoefficientMass x beta rho ^ 2) =
      x ^ (-2 * beta) *
        actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S := by
  unfold actualCubicDyadicStripSquareCapacityExcluding
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [actualCubicTargetNormalizedCoefficientMass_sq_eq x beta rho hx]
  rfl

private theorem actualCubicDyadicStrip_im_pos_of_mem
    {sigma tau : ℝ} {n : ℕ} {rho : ℂ}
    (hrho : rho ∈ actualCarlsonDyadicZeroStrip sigma tau n) :
    0 < rho.im := by
  have hshell := actualCarlsonDyadicZeroStrip_subset_shell sigma tau n hrho
  have hupper := (Finset.mem_sdiff.mp hshell).1
  exact (ZeroDensity.mem_zeroDensityZerosFinset.mp hupper).2.1

private theorem actualCubicDyadicStrip_sigma_lt_re_of_mem
    {sigma tau : ℝ} {n : ℕ} {rho : ℂ}
    (hrho : rho ∈ actualCarlsonDyadicZeroStrip sigma tau n) :
    sigma < rho.re := by
  have hshell := actualCarlsonDyadicZeroStrip_subset_shell sigma tau n hrho
  have hupper := (Finset.mem_sdiff.mp hshell).1
  exact (ZeroDensity.mem_zeroDensityZerosFinset.mp hupper).2.2.2

private theorem actualCubicDyadicUnitBucket_frequency_gap
    {sigma tau : ℝ} {n : ℕ} {rho eta : ℂ}
    (hrho : rho ∈ actualCarlsonDyadicZeroStrip sigma tau n)
    (heta : eta ∈ actualCarlsonDyadicZeroStrip sigma tau n) :
    (((actualCubicDyadicUnitBucket rho).dist
        (actualCubicDyadicUnitBucket eta) - 1 : ℕ) : ℝ) ≤
      |rho.im - eta.im| := by
  exact MathlibAux.natDist_sub_one_le_abs_sub_of_mem_unit
    (Nat.floor_le (actualCubicDyadicStrip_im_pos_of_mem hrho).le)
    (Nat.lt_floor_add_one rho.im)
    (Nat.floor_le (actualCubicDyadicStrip_im_pos_of_mem heta).le)
    (Nat.lt_floor_add_one eta.im)

/-- Direct actual-zeta cubic Gaussian `L2` control for one dyadic strip.
The half-isolated side supplies only the unit-bucket occupancy hypothesis;
the diagonal capacity is exactly the finite-`S`, target-normalized cubic mass. -/
theorem actualCubicDyadicStripGaussianGramExcluding_le_occupancy_mul_capacity
    {x beta sigma tau t m : ℝ} (n occupancy : ℕ) (S : Finset ℂ)
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
              x sigma tau n S) := by
  have hgram := MathlibAux.dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq
    (actualCarlsonDyadicZeroStrip sigma tau n \ S)
    (actualCubicTargetNormalizedCoefficientMass x beta)
    (actualCubicDyadicStripBackwardDrift sigma)
    (fun rho => rho.im)
    actualCubicDyadicUnitBucket occupancy ht hm
    (fun rho _ =>
      actualCubicTargetNormalizedCoefficientMass_nonneg x beta rho)
    (fun rho hrho => by
      have hstrip := (Finset.mem_sdiff.mp hrho).1
      unfold actualCubicDyadicStripBackwardDrift
      linarith [actualCubicDyadicStrip_sigma_lt_re_of_mem hstrip])
    (fun rho hrho eta heta =>
      actualCubicDyadicUnitBucket_frequency_gap
        (Finset.mem_sdiff.mp hrho).1 (Finset.mem_sdiff.mp heta).1)
    hoccupancy
  calc
    actualCubicDyadicStripGaussianGramExcluding
        x beta sigma tau n S t m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ((occupancy + 1 : ℕ) : ℝ) *
          ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
            actualCubicTargetNormalizedCoefficientMass x beta rho ^ 2 := by
      simpa [actualCubicDyadicStripGaussianGramExcluding] using hgram
    _ = MathlibAux.gaussianBucketSchurConstant *
        ((occupancy + 1 : ℕ) : ℝ) *
          (x ^ (-2 * beta) *
            actualCubicDyadicStripSquareCapacityExcluding
              x sigma tau n S) := by
      rw [sum_actualCubicTargetNormalizedCoefficientMass_sq_eq_capacity
        x beta sigma tau n S hx]

end

end PrimeNumberTheorem
