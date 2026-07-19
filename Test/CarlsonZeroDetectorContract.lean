import PrimeNumberTheorem.CarlsonZeroDetector

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example : Filter.Tendsto (fun x : ℝ => riemannZeta (x : ℂ))
    Filter.atTop (nhds 1) :=
  tendsto_riemannZeta_real_atTop

example (X : ℕ) (hX : 1 ≤ X) :
    Filter.Tendsto (fun x : ℝ => mollifiedZetaError X (x : ℂ))
      Filter.atTop (nhds 0) :=
  tendsto_mollifiedZetaError_real_atTop X hX

example (X : ℕ) (hX : 1 ≤ X) :
    Filter.Tendsto (fun x : ℝ => carlsonZeroDetector X (x : ℂ))
      Filter.atTop (nhds 1) :=
  tendsto_carlsonZeroDetector_real_atTop X hX

example (X : ℕ) (hX : 1 ≤ X) (sigma : ℝ) :
    ∃ x : ℝ, sigma < x ∧
      regularizedCarlsonZeroDetector X (x : ℂ) ≠ 0 :=
  exists_regularizedCarlsonZeroDetector_ne_zero_re_gt X hX sigma

example (X : ℕ) (hX : 1 ≤ X) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (regularizedCarlsonZeroDetector X) s ≠ ⊤ :=
  analyticOrderAt_regularizedCarlsonZeroDetector_ne_top X hX hs

example (X : ℕ) (s : ℂ) :
    carlsonZeroDetector X s = 1 - mollifiedZetaError X s ^ 2 :=
  rfl

example (X : ℕ) (s : ℂ) :
    carlsonZeroDetector X s =
      (riemannZeta s * mobiusMollifier X s) *
        (2 - riemannZeta s * mobiusMollifier X s) :=
  carlsonZeroDetector_eq_zeta_mul_mollifier_factorization X s

example {X : ℕ} {s : ℂ} (hs : riemannZeta s = 0) :
    carlsonZeroDetector X s = 0 :=
  carlsonZeroDetector_eq_zero_of_riemannZeta_eq_zero hs

example {X : ℕ} {rho : ℂ} (hX : 1 ≤ X)
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (carlsonZeroDetector X) rho :=
  analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector hX hrho

example {theta : ℝ} (htheta : 0 ≤ theta) (X : ℕ) :
    AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X)
      {s : ℂ | theta < s.re} :=
  analyticOnNhd_regularizedCarlsonZeroDetector_re_gt htheta X

example (X : ℕ) : Meromorphic (regularizedCarlsonZeroDetector X) :=
  meromorphic_regularizedCarlsonZeroDetector X

example (X : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    regularizedCarlsonZeroDetector X s =
      (s - 1) ^ 2 * carlsonZeroDetector X s :=
  regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1

example {X : ℕ} {rho : ℂ} (hX : 1 ≤ X)
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho :=
  analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector hX hrho

example (X : ℕ) (s : ℂ) :
    Real.log ‖carlsonZeroDetector X s‖ ≤
      ‖mollifiedZetaError X s‖ ^ 2 :=
  log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq X s

example {X : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hdet : carlsonZeroDetector X s ≠ 0) :
    Real.log ‖regularizedCarlsonZeroDetector X s‖ ≤
      2 * Real.log ‖s - 1‖ + ‖mollifiedZetaError X s‖ ^ 2 :=
  log_norm_regularizedCarlsonZeroDetector_le_two_log_norm_sub_one_add_error_sq
    hs0 hs1 hdet

example {X : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma ≠ 1)
    (hboundary : ∀ t ∈ Set.Icc a b,
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    (∫ t in a..b,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖) ≤
      2 * (∫ t in a..b,
        Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) +
      ∫ t in a..b,
        ‖mollifiedZetaError X
          ((sigma : ℂ) + Complex.I * t)‖ ^ 2 :=
  integral_log_norm_regularizedCarlsonZeroDetector_le_geometric_add_meanSquare
    hab hsigma0 hsigma1 hboundary

example (X : ℕ) {sigma : ℝ} (hsigma0 : 0 < sigma) :
    Continuous (fun t : ℝ =>
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)) :=
  continuous_regularizedCarlsonZeroDetector_verticalLine X hsigma0

example {X : ℕ} {sigma a b : ℝ} (hsigma0 : 0 < sigma)
    (hboundary : ∀ t ∈ Set.uIcc a b,
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    IntervalIntegrable
      (fun t : ℝ => Real.log ‖regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖)
      MeasureTheory.volume a b :=
  intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
    hsigma0 hboundary

example (X : ℕ) (sigma : ℝ) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)) :=
  continuous_mollifiedZetaError_verticalLine X sigma hsigma1

example (X : ℕ) (sigma : ℝ) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t)) :=
  continuous_carlsonZeroDetector_verticalLine X sigma hsigma1

example {X : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsigma1 : sigma ≠ 1)
    (hboundary : ∀ t ∈ Set.Icc a b,
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    ∫ t in a..b,
        Real.log ‖carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖ ≤
      ∫ t in a..b,
        ‖mollifiedZetaError X
          ((sigma : ℂ) + Complex.I * t)‖ ^ 2 :=
  integral_log_norm_carlsonZeroDetector_le_meanSquare
    hab hsigma1 hboundary

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
      (∀ t ∈ Set.Icc a b,
        carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in a..b,
            Real.log ‖carlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((C * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) :=
  exists_integral_log_norm_carlsonZeroDetector_le_endpoint

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
      (∀ t ∈ Set.Icc a b,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in a..b,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          2 * (∫ t in a..b,
            Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) +
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((C * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_endpoint

example :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (kappa : ℝ) (X : ℕ)
        (sigma a b x : ℝ),
      0 < kappa →
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b,
        |t| ≤ x / 2 ∧ x ≤ kappa * |t|) →
      (∀ t ∈ Set.Icc a b,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in a..b,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          2 * (∫ t in a..b,
            Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) +
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * (((((A + kappa) * x ^ (-sigma)) ^ 2)) *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_endpoint_of_comparable

noncomputable example (A kappa : ℝ) (X : ℕ)
    (sigma a b x : ℝ) : ℝ :=
  regularizedCarlsonLogNormEndpoint A kappa X sigma a b x

example :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma u v : ℝ),
      1 ≤ X → 1 ≤ u → u ≤ v → v ≤ 2 * u →
      1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma u v (4 * u) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_doublingInterval

example :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma u : ℝ),
      1 ≤ X → 1 ≤ u → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u (2 * u),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..(2 * u),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma u (2 * u) (4 * u) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadic

example :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc 1 ((2 : ℝ) ^ n),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in 1..((2 : ℝ) ^ n),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          ∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpoint
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSum

example :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma v : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 →
      (2 : ℝ) ^ n ≤ v → v ≤ (2 : ℝ) ^ (n + 1) →
      (∀ t ∈ Set.Icc 1 v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in 1..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          (∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpoint
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicCover

example :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma y0 v : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 → y0 ≤ 1 →
      (2 : ℝ) ^ n ≤ v → v ≤ (2 : ℝ) ^ (n + 1) →
      (∀ t ∈ Set.Icc y0 v,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in y0..v,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          (∫ t in y0..1,
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖) +
          (∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpoint
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpoint
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_low_add_dyadicCover

#print axioms carlsonZeroDetector_eq_zeta_mul_mollifier_factorization
#print axioms tendsto_riemannZeta_real_atTop
#print axioms tendsto_mollifiedZetaError_real_atTop
#print axioms tendsto_carlsonZeroDetector_real_atTop
#print axioms exists_regularizedCarlsonZeroDetector_ne_zero_re_gt
#print axioms analyticOrderAt_regularizedCarlsonZeroDetector_ne_top
#print axioms carlsonZeroDetector_eq_zero_of_riemannZeta_eq_zero
#print axioms analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector
#print axioms analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
#print axioms meromorphic_regularizedCarlsonZeroDetector
#print axioms regularizedCarlsonZeroDetector_eq_sub_one_sq_mul
#print axioms analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
#print axioms log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq
#print axioms log_norm_regularizedCarlsonZeroDetector_le_two_log_norm_sub_one_add_error_sq
#print axioms integral_log_norm_regularizedCarlsonZeroDetector_le_geometric_add_meanSquare
#print axioms continuous_regularizedCarlsonZeroDetector_verticalLine
#print axioms intervalIntegrable_log_norm_regularizedCarlsonZeroDetector
#print axioms continuous_mollifiedZetaError_verticalLine
#print axioms continuous_carlsonZeroDetector_verticalLine
#print axioms integral_log_norm_carlsonZeroDetector_le_meanSquare
#print axioms exists_integral_log_norm_carlsonZeroDetector_le_endpoint
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_endpoint
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_endpoint_of_comparable
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_doublingInterval
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadic
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSum
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicCover
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_low_add_dyadicCover

end CarlsonZeroDensity
end PrimeNumberTheorem
