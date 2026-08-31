import PrimeNumberTheorem.CarlsonTwoThirdsDIExponent

namespace PrimeNumberTheorem

example : diCoreExponent = 57 / 100 := rfl

example : diOuterExponent = 571 / 1000 := rfl
example : diRightBoundary = 1000 := rfl
example : diEpsilon = 1 / 10000 := rfl

example : diShortRightBoundary = 4 := rfl
example : diShortInterpolationWeight = 1 / 21 :=
  di_short_interpolation_weight_eq
example : diShortInterpolatedExponent = 8791 / 10500 :=
  di_short_interpolated_exponent_eq
example : diShortTargetExponent - diShortInterpolatedExponent = 13 / 7875 ∧
    diShortInterpolatedExponent < diShortTargetExponent :=
  di_short_interpolated_exponent_lt_target
example : diShortTargetExponent = 8 / 9 - diShortDelta :=
  di_short_target_eq_carlson_sub_delta
example : (3 / 17) * diShortDelta = 3 / 340 :=
  di_short_fourteenSeventeenths_margin
example :
    (4 / 3 + 8 / 9 + diShortTargetExponent) /
        (2 + 8 / 9 + diShortTargetExponent) = 551 / 671 :=
  di_short_separated_threshold_eq

example : diInterpolationWeight = 1 / 5997 :=
  di_interpolation_weight_eq

example : diCoreExponent < diOuterExponent ∧ diOuterExponent < 4 / 7 :=
  di_twoScale_length_range

example : diInterpolatedExponent = 12146849 / 14992500 :=
  di_interpolated_exponent_eq

example : diTargetExponent - diInterpolatedExponent =
    409373 / 719640000 ∧ diInterpolatedExponent < diTargetExponent :=
  di_interpolated_exponent_lt_target

example :
    carlsonLowerEndpointExponent (2 / 3) diCoreExponent = 81 / 100 ∧
      diTargetExponent -
          carlsonLowerEndpointExponent (2 / 3) diCoreExponent = 11 / 14400 ∧
      carlsonLowerEndpointExponent (2 / 3) diCoreExponent < diTargetExponent :=
  di_lower_endpoint_lt_target

example : diTargetExponent = 8 / 9 - diDelta :=
  di_target_eq_carlson_sub_delta

example : (3 / 17) * diDelta = 15 / 1088 :=
  di_fourteenSeventeenths_margin

example :
    (4 / 3 + 8 / 9 + diTargetExponent) /
        (2 + 8 / 9 + diTargetExponent) = 1747 / 2131 :=
  di_separated_threshold_eq

example :
    2 * (14 / 17 - 2 / 3) -
        (1 - 14 / 17) * (8 / 9 + diTargetExponent) = 15 / 1088 :=
  di_direct_gap_at_fourteen_seventeenths

#print axioms di_interpolation_weight_eq
#print axioms di_twoScale_length_range
#print axioms di_interpolated_exponent_eq
#print axioms di_interpolated_exponent_lt_target
#print axioms di_lower_endpoint_lt_target
#print axioms di_target_eq_carlson_sub_delta
#print axioms di_fourteenSeventeenths_margin
#print axioms di_separated_threshold_eq
#print axioms di_direct_gap_at_fourteen_seventeenths
#print axioms di_short_interpolation_weight_eq
#print axioms di_short_interpolated_exponent_eq
#print axioms di_short_interpolated_exponent_lt_target
#print axioms di_short_target_eq_carlson_sub_delta
#print axioms di_short_fourteenSeventeenths_margin
#print axioms di_short_separated_threshold_eq

end PrimeNumberTheorem
