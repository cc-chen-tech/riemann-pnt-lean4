import PrimeNumberTheorem.CarlsonLengthMinimax

/-!
# A first Carlson power saving using only the classical half-length range

This rational ledger isolates a weaker alternative to the Conrey--DI `4/7`
route.  A critical-line mollified mean square for every fixed length exponent
below `1/2` already suffices for a positive saving when combined with the
two-scale plateau and the proved right boundary at `R=4`.

No analytic mean-square assertion is made in this file.
-/

namespace PrimeNumberTheorem

noncomputable section

/-- Exact Moebius plateau exponent for the first half-range target. -/
def halfRangeCoreExponent : ℝ := 2 / 5

/-- Taper support exponent, strictly between the core and `1/2`. -/
def halfRangeOuterExponent : ℝ := 9 / 20

/-- The already formalized right boundary. -/
def halfRangeRightBoundary : ℝ := 4

/-- Small reserve in the critical-boundary mean square. -/
def halfRangeEpsilon : ℝ := 1 / 2000

/-- Three-lines weight at `sigma=2/3` on `[1/2,4]`. -/
def halfRangeInterpolationWeight : ℝ :=
  ((2 / 3 : ℝ) - 1 / 2) / (halfRangeRightBoundary - 1 / 2)

/-- Exact interpolation output before choosing a round target saving. -/
def halfRangeInterpolatedExponent : ℝ :=
  (1 - halfRangeInterpolationWeight) * (1 + halfRangeEpsilon) +
    halfRangeInterpolationWeight *
      (1 + 2 * halfRangeCoreExponent * (1 - halfRangeRightBoundary))

/-- Convenient density target with explicit saving `1/400`. -/
def halfRangeTargetExponent : ℝ := 8 / 9 - 1 / 400

/-- Explicit first power saving. -/
def halfRangeDelta : ℝ := 1 / 400

/-- Exponent produced by the naive moving-cutoff strategy: split the broad
critical Gaussian into independent one-cutoff pieces, apply a full-line
fixed-polynomial estimate to every piece, and sum the estimates.  The number
of relevant square-root cutoffs costs at least the outer mollifier exponent
`b`; interpolation transmits this loss with left-boundary weight `20/21`. -/
def halfRangeNaiveCutoffPartitionExponent : ℝ :=
  halfRangeInterpolatedExponent +
    (1 - halfRangeInterpolationWeight) * halfRangeOuterExponent

theorem halfRange_length_range :
    1 / 3 < halfRangeCoreExponent ∧
      halfRangeCoreExponent < halfRangeOuterExponent ∧
      halfRangeOuterExponent < 1 / 2 := by
  norm_num [halfRangeCoreExponent, halfRangeOuterExponent]

theorem halfRange_interpolation_weight_eq :
    halfRangeInterpolationWeight = 1 / 21 := by
  norm_num [halfRangeInterpolationWeight, halfRangeRightBoundary]

theorem halfRange_interpolated_exponent_eq :
    halfRangeInterpolatedExponent = 1861 / 2100 := by
  norm_num [halfRangeInterpolatedExponent, halfRangeInterpolationWeight,
    halfRangeRightBoundary, halfRangeCoreExponent, halfRangeEpsilon]

/-- The actual saving is `17/6300`; rounding down to `1/400` leaves the
positive exponent slack `1/5040`. -/
theorem halfRange_interpolated_exponent_lt_target :
    8 / 9 - halfRangeInterpolatedExponent = 17 / 6300 ∧
      halfRangeTargetExponent - halfRangeInterpolatedExponent = 1 / 5040 ∧
      halfRangeInterpolatedExponent < halfRangeTargetExponent := by
  norm_num [halfRangeTargetExponent, halfRangeInterpolatedExponent,
    halfRangeInterpolationWeight, halfRangeRightBoundary,
    halfRangeCoreExponent, halfRangeEpsilon]

theorem halfRange_target_eq_carlson_sub_delta :
    halfRangeTargetExponent = 8 / 9 - halfRangeDelta := by
  rfl

/-- Margin at `beta=14/17` if forcing keeps its old `8/9` loss. -/
theorem halfRange_fourteenSeventeenths_margin :
    (3 / 17) * halfRangeDelta = 3 / 6800 := by
  norm_num [halfRangeDelta]

/-- Exact direct exponent gap at `beta=14/17`. -/
theorem halfRange_direct_gap_at_fourteen_seventeenths :
    2 * (14 / 17 - 2 / 3) -
        (1 - 14 / 17) * (8 / 9 + halfRangeTargetExponent) = 3 / 6800 := by
  norm_num [halfRangeTargetExponent]

/-- Exact separated-density beta threshold for the first half-range target. -/
theorem halfRange_separated_threshold_eq :
    (4 / 3 + 8 / 9 + halfRangeTargetExponent) /
        (2 + 8 / 9 + halfRangeTargetExponent) = 11191 / 13591 := by
  norm_num [halfRangeTargetExponent]

/-- Exact exponent of the independent-cutoff summation at the half-range
parameters. -/
theorem halfRange_naiveCutoffPartition_exponent_eq :
    halfRangeNaiveCutoffPartitionExponent = 2761 / 2100 := by
  norm_num [halfRangeNaiveCutoffPartitionExponent,
    halfRangeInterpolatedExponent, halfRangeInterpolationWeight,
    halfRangeRightBoundary, halfRangeCoreExponent, halfRangeOuterExponent,
    halfRangeEpsilon]

/-- Independent summation over the moving AFE cutoffs is not merely too weak
for the target `1/400` saving: its exponent already exceeds the original
Carlson `8/9` exponent by `2683/6300`.  Any successful AFE formalization must
therefore retain the nested cutoffs through a maximal/orthogonality estimate
rather than bounding each cutoff fibre separately. -/
theorem halfRange_naiveCutoffPartition_no_power_saving :
    halfRangeNaiveCutoffPartitionExponent - 8 / 9 = 2683 / 6300 ∧
      8 / 9 < halfRangeNaiveCutoffPartitionExponent := by
  norm_num [halfRangeNaiveCutoffPartitionExponent,
    halfRangeInterpolatedExponent, halfRangeInterpolationWeight,
    halfRangeRightBoundary, halfRangeCoreExponent, halfRangeOuterExponent,
    halfRangeEpsilon]

end

end PrimeNumberTheorem
