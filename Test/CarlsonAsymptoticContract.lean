import PrimeNumberTheorem.CarlsonAsymptotic

open Complex Set Filter

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

#check carlsonMollifierLength
#check one_le_carlsonMollifierLength
#check carlsonMollifierLength_bounds
#check rpow_le_exp_mul_rpow_of_exponent_gap
#check carlson_lower_endpoint_exponent
#check carlson_upper_endpoint_exponent
#check carlson_lower_endpoint_rpow_le
#check carlson_upper_endpoint_rpow_le
#check sum_range_pow_le_pow_div_sub_one
#check sum_dyadic_rpow_le
#check sum_scaled_dyadic_rpow_le
#check sum_dyadic_rpow_le_of_neg
#check sum_scaled_dyadic_rpow_le_of_neg
#check carlson_min_scale_negative_power_le
#check sum_carlson_min_scale_negative_power_le
#check carlson_floor_product_rpow_le
#check sum_carlson_floor_product_rpow_le
#check carlson_remainder_scale_le
#check sum_carlson_remainder_scale_le
#check carlsonSharpEndpointDyadicMajorant
#check carlsonLogNormSharpEndpointExplicit_le_dyadicMajorant
#check carlsonSharpDyadicSumMajorant
#check sum_carlsonSharpEndpointDyadicMajorant_le
#check carlsonSharpGeometricCoverExplicitBound_le_dyadicSumMajorant
#check carlson_cover_log_factor_le
#check carlsonMollifierLength_le_height
#check carlsonAmbientLogCube
#check carlson_parameterized_geometric_cover_le_dyadicSumMajorant
#check scaled_dyadic_terminal_rpow_div_le
#check carlson_cover_next_scale_le
#check carlsonSharpAmbientMajorant
#check carlsonSharpDyadicSumMajorant_le_ambient
#check carlson_parameterized_geometric_cover_le_ambient
#check half_rpow_le_two_of_neg_one_le
#check carlsonMollifierLength_negative_rpow_le
#check carlson_optimized_lower_ambient_term_le
#check carlson_optimized_upper_ambient_term_le
#check carlson_auxiliary_line_fixed_gap
#check carlson_auxiliary_line_denominator_bounds
#check carlson_auxiliary_exponents_le_target_plus_gap
#check carlson_terminal_rpow_le
#check carlsonMollifierLength_positive_rpow_le
#check one_le_carlsonAmbientLogCube
#check one_le_carlson_target_rpow
#check carlson_ambient_first_bracket_le
#check carlson_ambient_second_bracket_le
#check carlson_ambient_remainder_bracket_le
#check carlsonSharpAmbientCoefficient
#check carlsonSharpAmbientMajorant_optimized_le
#check carlson_parameterized_geometric_cover_optimized_le
#check eventually_carlson_optimized_parameter_conditions
#check carlson_logPolynomial_le_ambientLinear
#check carlsonZeroLogCoefficient
#check regularizedCarlsonFactorZeroLogMajorant_bounds
#check carlsonHorizontalVariationCoefficient
#check regularizedCarlsonFactorLogVariationMajorant_le_ambientSquare
#check carlsonHorizontalMajorantCoefficient
#check regularizedCarlsonHorizontalLogDerivMajorant_le_ambientCube
#check eventually_carlson_parameter_conditions
#check exists_carlson_parameterized_count_certificate
#check carlsonAmbientLogCube_le_logCube
#check carlson_zeroDensity_isBigO

example {sigma T : ℝ} (hpower : 1 ≤ T ^ (2 * sigma - 1)) :
    T ^ (2 * sigma - 1) / 2 ≤ (carlsonMollifierLength sigma T : ℝ) ∧
      (carlsonMollifierLength sigma T : ℝ) ≤ T ^ (2 * sigma - 1) :=
  carlsonMollifierLength_bounds hpower

example {T a b C : ℝ} (hT : 0 < T)
    (hgap : (b - a) * Real.log T ≤ C) :
    T ^ b ≤ Real.exp C * T ^ a :=
  rpow_le_exp_mul_rpow_of_exponent_gap hT hgap

example (sigma : ℝ) :
    1 + (2 * sigma - 1) * (1 - 2 * sigma) =
      4 * sigma * (1 - sigma) :=
  carlson_lower_endpoint_exponent sigma

example (sigma : ℝ) :
    (1 + (2 * sigma - 1)) * (2 - 2 * sigma) =
      4 * sigma * (1 - sigma) :=
  carlson_upper_endpoint_exponent sigma

example {sigma x0 T : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 0 < T) (hlog : 0 < Real.log T)
    (hx0 : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    T ^ (1 + (2 * sigma - 1) * (1 - 2 * x0)) ≤
      Real.exp 4 * T ^ (4 * sigma * (1 - sigma)) :=
  carlson_lower_endpoint_rpow_le hsigma hsigmaOne hT hlog hx0 hgap

example {sigma x0 T : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) (hT : 0 < T) (hlog : 0 < Real.log T)
    (hx0 : x0 < sigma) (hgap : sigma - x0 < 2 / Real.log T) :
    T ^ ((1 + (2 * sigma - 1)) * (2 - 2 * x0)) ≤
      Real.exp 8 * T ^ (4 * sigma * (1 - sigma)) :=
  carlson_upper_endpoint_rpow_le hsigma hsigmaOne hT hlog hx0 hgap

example {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    ∀ᶠ T : ℝ in atTop,
      6 ≤ T ∧ 0 < Real.log T ∧
        2 / Real.log T < sigma - 1 / 2 ∧
        1 ≤ T ^ (2 * sigma - 1) :=
  eventually_carlson_parameter_conditions hsigma

example {r : ℝ} (hr : 1 < r) (n : ℕ) :
    (∑ k ∈ Finset.range n, r ^ k) ≤ r ^ n / (r - 1) :=
  sum_range_pow_le_pow_div_sub_one hr n

example {q : ℝ} (hq : 0 < q) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2 : ℝ) ^ k) ^ q) ≤
      ((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1) :=
  sum_dyadic_rpow_le hq n

example {u q : ℝ} (hu : 0 ≤ u) (hq : 0 < q) (n : ℕ) :
    (∑ k ∈ Finset.range n, (u * (2 : ℝ) ^ k) ^ q) ≤
      u ^ q * (((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1)) :=
  sum_scaled_dyadic_rpow_le hu hq n

example {q : ℝ} (hq : q < 0) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2 : ℝ) ^ k) ^ q) ≤
      (1 - (2 : ℝ) ^ q)⁻¹ :=
  sum_dyadic_rpow_le_of_neg hq n

example {u q : ℝ} (hu : 0 < u) (hq : q < 0) (n : ℕ) :
    (∑ k ∈ Finset.range n, (u * (2 : ℝ) ^ k) ^ q) ≤
      u ^ q * (1 - (2 : ℝ) ^ q)⁻¹ :=
  sum_scaled_dyadic_rpow_le_of_neg hu hq n

example {X : ℕ} {u x0 : ℝ} (hX : 1 ≤ X) (hu : 1 ≤ u)
    (hx0 : 1 / 2 < x0) :
    u * (((min X (Nat.floor (4 * u)) + 1 : ℕ) : ℝ) ^ (1 - 2 * x0)) ≤
      u ^ (2 - 2 * x0) + u * (X : ℝ) ^ (1 - 2 * x0) :=
  carlson_min_scale_negative_power_le hX hu hx0

example {X n : ℕ} {u x0 : ℝ} (hX : 1 ≤ X) (hu : 1 ≤ u)
    (hx0 : 1 / 2 < x0) (hx0One : x0 < 1) :
    (∑ k ∈ Finset.range n,
      (u * (2 : ℝ) ^ k) *
        (((min X (Nat.floor (4 * (u * (2 : ℝ) ^ k))) + 1 : ℕ) : ℝ) ^
          (1 - 2 * x0))) ≤
      u ^ (2 - 2 * x0) *
          (((2 : ℝ) ^ n) ^ (2 - 2 * x0) /
            ((2 : ℝ) ^ (2 - 2 * x0) - 1)) +
        (X : ℝ) ^ (1 - 2 * x0) * (u * (2 : ℝ) ^ n) :=
  sum_carlson_min_scale_negative_power_le hX hu hx0 hx0One

example {X : ℕ} {u q : ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q) :
    ((((Nat.floor (4 * u)) * X : ℕ) : ℝ) ^ q) ≤
      (4 * u * (X : ℝ)) ^ q :=
  carlson_floor_product_rpow_le hu hq

example {X n : ℕ} {u q : ℝ} (hu : 0 ≤ u) (hq : 0 < q) :
    (∑ k ∈ Finset.range n,
      ((((Nat.floor (4 * (u * (2 : ℝ) ^ k))) * X : ℕ) : ℝ) ^ q)) ≤
      (4 * u * (X : ℝ)) ^ q *
        (((2 : ℝ) ^ n) ^ q / ((2 : ℝ) ^ q - 1)) :=
  sum_carlson_floor_product_rpow_le hu hq

example {A a x0 : ℝ} (ha : 1 ≤ a) :
    (((A + 4) * (4 * a) ^ (-x0)) ^ 2) * (a + 4 * Real.pi) ≤
      (A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi) * a ^ (1 - 2 * x0) :=
  carlson_remainder_scale_le ha

example {n : ℕ} {A u x0 : ℝ} (hu : 1 ≤ u) (hx0 : 1 / 2 < x0) :
    (∑ k ∈ Finset.range n,
      (((A + 4) * (4 * (u * (2 : ℝ) ^ k)) ^ (-x0)) ^ 2) *
        ((u * (2 : ℝ) ^ k) + 4 * Real.pi)) ≤
      (A + 4) ^ 2 * (4 : ℝ) ^ (-2 * x0) *
        (1 + 4 * Real.pi) *
          (u ^ (1 - 2 * x0) *
            (1 - (2 : ℝ) ^ (1 - 2 * x0))⁻¹) :=
  sum_carlson_remainder_scale_le hu hx0

#print axioms one_le_carlsonMollifierLength
#print axioms carlsonMollifierLength_bounds
#print axioms rpow_le_exp_mul_rpow_of_exponent_gap
#print axioms eventually_carlson_parameter_conditions
#print axioms exists_carlson_parameterized_count_certificate
#print axioms carlsonAmbientLogCube_le_logCube
#print axioms carlson_zeroDensity_isBigO

end CarlsonZeroDensity
end PrimeNumberTheorem
