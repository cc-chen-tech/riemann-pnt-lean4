import PrimeNumberTheorem.CarlsonLengthMinimax

namespace PrimeNumberTheorem

example (σ x : ℝ) :
    carlsonLowerEndpointExponent σ x - carlsonUpperEndpointExponent σ x =
      carlsonEndpointBalance σ - x :=
  carlson_endpoint_difference σ x

example {σ x : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    carlsonEndpointOptimum σ ≤
      max (carlsonLowerEndpointExponent σ x)
        (carlsonUpperEndpointExponent σ x) :=
  carlson_endpoint_max_ge_optimum hσ hσ1

example {σ x : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    max (carlsonLowerEndpointExponent σ x)
          (carlsonUpperEndpointExponent σ x) = carlsonEndpointOptimum σ ↔
      x = carlsonEndpointBalance σ :=
  carlson_endpoint_max_eq_optimum_iff hσ hσ1

example (x : ℝ) :
    carlsonLowerEndpointExponent (2 / 3) x = 1 - x / 3 ∧
      carlsonUpperEndpointExponent (2 / 3) x = 2 / 3 + 2 * x / 3 :=
  carlson_twoThirds_endpoint_formulas x

example (x : ℝ) :
    8 / 9 ≤ max (carlsonLowerEndpointExponent (2 / 3) x)
      (carlsonUpperEndpointExponent (2 / 3) x) ∧
    (max (carlsonLowerEndpointExponent (2 / 3) x)
          (carlsonUpperEndpointExponent (2 / 3) x) = 8 / 9 ↔ x = 1 / 3) :=
  carlson_twoThirds_length_minimax x

example (σ δL δU x : ℝ) :
    carlsonSavedLowerEndpointExponent σ δL x -
        carlsonSavedUpperEndpointExponent σ δU x =
      carlsonSavedBalance σ δL δU - x :=
  carlson_saved_endpoint_difference σ δL δU x

example (σ δL δU : ℝ) :
    carlsonSavedOptimum σ δL δU =
      4 * σ * (1 - σ) - 2 * (1 - σ) * δL - (2 * σ - 1) * δU :=
  rfl

example {σ δL δU x : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    carlsonSavedOptimum σ δL δU ≤
      max (carlsonSavedLowerEndpointExponent σ δL x)
        (carlsonSavedUpperEndpointExponent σ δU x) :=
  carlson_saved_endpoint_max_ge_optimum hσ hσ1

example {σ δL δU x : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    max (carlsonSavedLowerEndpointExponent σ δL x)
          (carlsonSavedUpperEndpointExponent σ δU x) =
        carlsonSavedOptimum σ δL δU ↔
      x = carlsonSavedBalance σ δL δU :=
  carlson_saved_endpoint_max_eq_optimum_iff hσ hσ1

example (δL δU : ℝ) :
    carlsonSavedOptimum (2 / 3) δL δU =
      8 / 9 - (2 / 3) * δL - (1 / 3) * δU :=
  carlson_twoThirds_saved_optimum δL δU

#print axioms carlson_endpoint_max_ge_optimum
#print axioms carlson_endpoint_max_eq_optimum_iff
#print axioms carlson_twoThirds_length_minimax
#print axioms carlson_saved_endpoint_max_ge_optimum
#print axioms carlson_saved_endpoint_max_eq_optimum_iff
#print axioms carlson_twoThirds_saved_optimum

end PrimeNumberTheorem
