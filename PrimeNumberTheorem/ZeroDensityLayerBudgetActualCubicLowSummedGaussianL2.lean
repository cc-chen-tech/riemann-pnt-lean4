import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicLowGaussianL2Adapter
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicLowDyadicCapacity

/-!
# Actual cubic summed low-layer Gaussian L2 capacity

This module sums the genuine reciprocal-cubic Gaussian Gram bounds over every
dyadic block below a polynomial low-height cut. A uniform unit-bucket
occupancy bound, supplied externally by the half-isolated Gram/Schur side,
controls the complete block sum by the actual target-normalized cubic energy.

The second theorem composes this estimate with the actual Carlson low-layer
capacity theorem. Thus finitely many initial blocks retain their exact zeta
zero capacities, while all later blocks incur exactly the established
Carlson `log^5` loss. No additional logarithmic or cardinality-square loss is
introduced here.

This module does not prove an occupancy estimate, redo Gram/Schur analysis,
or claim decay or oscillation.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem

noncomputable section

/-- The sum of target-normalized actual cubic Gaussian Gram forms over all
dyadic blocks through the polynomial low-height cut. -/
noncomputable def actualCubicNormalizedLowDyadicGaussianGramExcluding
    (beta sigma tau gamma : ℝ) (S : Finset ℂ)
    (t width : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
    actualCubicDyadicStripGaussianGramExcluding
      (m : ℝ) beta sigma tau n S t width

/-- A uniform unit-bucket occupancy bound controls the complete low-layer
Gaussian Gram sum by the actual target-normalized reciprocal-cubic energy. -/
theorem actualCubicNormalizedLowDyadicGaussianGramExcluding_le_occupancy_mul_energy
    {beta sigma tau gamma t width : ℝ} {S : Finset ℂ}
    {m occupancy : ℕ}
    (ht : 0 ≤ t) (hwidth : 1 ≤ width)
    (hoccupancy :
      ∀ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
        ∀ q ∈ Finset.image actualCubicDyadicUnitBucket
            (actualCarlsonDyadicZeroStrip sigma tau n \ S),
          (Finset.filter
            (fun rho => actualCubicDyadicUnitBucket rho = q)
            (actualCarlsonDyadicZeroStrip sigma tau n \ S)).card ≤
              occupancy + 1) :
    actualCubicNormalizedLowDyadicGaussianGramExcluding
        beta sigma tau gamma S t width m ≤
      MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℕ) *
        actualCubicNormalizedSmoothedStripEnergyUpTo
          beta sigma tau gamma S m := by
  unfold actualCubicNormalizedLowDyadicGaussianGramExcluding
    actualCubicNormalizedSmoothedStripEnergyUpTo
    actualCubicSmoothedStripEnergyUpTo
  have hsum :
      (∑ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
        actualCubicDyadicStripGaussianGramExcluding
          (m : ℝ) beta sigma tau n S t width) ≤
      ∑ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
        MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℕ) *
          ((m : ℝ) ^ (-2 * beta) *
            actualCubicDyadicStripSquareCapacityExcluding
              (m : ℝ) sigma tau n S) := by
    apply Finset.sum_le_sum
    intro n hn
    exact actualCubicDyadicStripGaussianGramExcluding_le_occupancy_mul_capacity
      n occupancy S (Nat.cast_nonneg m) ht hwidth (hoccupancy n hn)
  simpa [Finset.mul_sum, mul_assoc] using hsum

/-- For a genuine Carlson certificate, the summed actual cubic Gaussian Gram
has a uniform low-layer majorant: exact capacities below a fixed threshold
and the explicit Carlson `log^5` majorant above it. -/
theorem exists_actualCubicNormalizedLowDyadicGaussianGramExcluding_le_lowDyadicL2CapacityMajorant
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N : ℕ,
      ∀ (beta tau gamma : ℝ) (S : Finset ℂ)
        (t width : ℝ) (occupancy m : ℕ),
        1 ≤ m → 0 ≤ t → 1 ≤ width →
        (∀ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
          ∀ q ∈ Finset.image actualCubicDyadicUnitBucket
              (actualCarlsonDyadicZeroStrip sigma tau n \ S),
            (Finset.filter
              (fun rho => actualCubicDyadicUnitBucket rho = q)
              (actualCarlsonDyadicZeroStrip sigma tau n \ S)).card ≤
                occupancy + 1) →
        actualCubicNormalizedLowDyadicGaussianGramExcluding
            beta sigma tau gamma S t width m ≤
          MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℕ) *
            actualCubicNormalizedLowDyadicL2CapacityMajorant
              certificate B beta tau gamma N m := by
  obtain ⟨B, hB, N, henergy⟩ :=
    exists_actualCubicNormalizedSmoothedStripEnergyUpTo_le_lowDyadicL2CapacityMajorant
      certificate
  refine ⟨B, hB, N, ?_⟩
  intro beta tau gamma S t width occupancy m hm ht hwidth hoccupancy
  calc
    actualCubicNormalizedLowDyadicGaussianGramExcluding
        beta sigma tau gamma S t width m ≤
      MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℕ) *
        actualCubicNormalizedSmoothedStripEnergyUpTo
          beta sigma tau gamma S m :=
      actualCubicNormalizedLowDyadicGaussianGramExcluding_le_occupancy_mul_energy
        ht hwidth hoccupancy
    _ ≤ MathlibAux.gaussianBucketSchurConstant * (occupancy + 1 : ℕ) *
          actualCubicNormalizedLowDyadicL2CapacityMajorant
            certificate B beta tau gamma N m := by
      apply mul_le_mul_of_nonneg_left (henergy beta tau gamma S m hm)
      exact mul_nonneg MathlibAux.gaussianBucketSchurConstant_pos.le (by positivity)

end

end PrimeNumberTheorem
