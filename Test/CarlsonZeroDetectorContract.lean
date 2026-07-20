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

example {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    carlsonZeroDetector X s ≠ 0 :=
  carlsonZeroDetector_ne_zero_of_four_le_re hX hs

example {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    (56 / 81 : ℝ) ≤ (carlsonZeroDetector X s).re :=
  fiftySix_div_eightyOne_le_re_carlsonZeroDetector_of_four_le_re hX hs

example (X : ℕ) {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (carlsonZeroDetector X) s :=
  analyticAt_carlsonZeroDetector_of_ne_one X hs1

example {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    regularizedCarlsonZeroDetector X s ≠ 0 :=
  regularizedCarlsonZeroDetector_ne_zero_of_four_le_re hX hs

example {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    1 ≤ ‖regularizedCarlsonZeroDetector X s‖ :=
  one_le_norm_regularizedCarlsonZeroDetector_of_four_le_re hX hs

#check norm_log_carlsonZeroDetector_le_inv_sq_of_four_le_re

example {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    2 * Real.log ‖s - 1‖ + Real.log (56 / 81 : ℝ) ≤
      Real.log ‖regularizedCarlsonZeroDetector X s‖ :=
  log_fiftySix_div_eightyOne_le_log_norm_regularized_of_four_le_re hX hs

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

example (X : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hdet : carlsonZeroDetector X s ≠ 0) :
    logDeriv (regularizedCarlsonZeroDetector X) s =
      2 * (s - 1)⁻¹ + logDeriv (carlsonZeroDetector X) s :=
  logDeriv_regularizedCarlsonZeroDetector_eq_two_inv_add
    X hs0 hs1 hdet

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

noncomputable example (A kappa : ℝ) (X : ℕ)
    (sigma a b x : ℝ) : ℝ :=
  regularizedCarlsonLogNormEndpointExplicit A kappa X sigma a b x

#check carlsonLogNormSharpEndpointExplicit
#check log_norm_regularizedCarlsonZeroDetector_eq_two_log_norm_sub_one_add
#check exists_integral_log_norm_carlsonZeroDetector_le_sharpDoublingIntervalExplicit_of_regularizedBoundary

example {sigma u v : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hu : 1 ≤ u) (huv : u ≤ v) :
    (∫ t in u..v,
      Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) ≤
        (v - u) * Real.log (1 + v) :=
  integral_log_norm_vertical_sub_one_le_length_mul_log
    hsigma0 hsigma1 hu huv

example {A kappa sigma a b x : ℝ} {X : ℕ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    regularizedCarlsonLogNormEndpoint A kappa X sigma a b x ≤
      regularizedCarlsonLogNormEndpointExplicit A kappa X sigma a b x :=
  regularizedCarlsonLogNormEndpoint_le_explicit
    hsigma0 hsigma1 ha hab

example (X : ℕ) (s : ℂ) :
    1 - ‖mollifiedZetaError X s‖ ^ 2 ≤ ‖carlsonZeroDetector X s‖ :=
  one_sub_norm_mollifiedZetaError_sq_le_norm_carlsonZeroDetector X s

example {X : ℕ} {s : ℂ} {r : ℝ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hr : 0 ≤ r) (hr1 : r < 1)
    (herr : ‖mollifiedZetaError X s‖ ≤ r) :
    2 * Real.log ‖s - 1‖ + Real.log (1 - r ^ 2) ≤
      Real.log ‖regularizedCarlsonZeroDetector X s‖ :=
  two_log_norm_sub_one_add_log_one_sub_sq_le_log_norm_regularized
    hs0 hs1 hr hr1 herr

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
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma u : ℝ),
      1 ≤ X → 1 ≤ u → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc u (2 * u),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in u..(2 * u),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma u (2 * u) (4 * u) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicExplicit

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
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (sigma : ℝ) (n : ℕ),
      1 ≤ X → 1 / 2 < sigma → sigma < 1 →
      (∀ t ∈ Set.Icc 1 ((2 : ℝ) ^ n),
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in 1..((2 : ℝ) ^ n),
            Real.log ‖regularizedCarlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          ∑ k ∈ Finset.range n,
            regularizedCarlsonLogNormEndpointExplicit
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSumExplicit

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
            regularizedCarlsonLogNormEndpointExplicit
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicCoverExplicit

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
            regularizedCarlsonLogNormEndpointExplicit
              A 4 X sigma ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
                (4 * (2 : ℝ) ^ k)) +
          regularizedCarlsonLogNormEndpointExplicit
            A 4 X sigma ((2 : ℝ) ^ n) v (4 * (2 : ℝ) ^ n) :=
  exists_integral_log_norm_regularizedCarlsonZeroDetector_le_low_add_dyadicCoverExplicit

#print axioms carlsonZeroDetector_eq_zeta_mul_mollifier_factorization
#print axioms tendsto_riemannZeta_real_atTop
#print axioms tendsto_mollifiedZetaError_real_atTop
#print axioms tendsto_carlsonZeroDetector_real_atTop
#print axioms exists_regularizedCarlsonZeroDetector_ne_zero_re_gt
#print axioms carlsonZeroDetector_ne_zero_of_four_le_re
#print axioms fiftySix_div_eightyOne_le_re_carlsonZeroDetector_of_four_le_re
#print axioms analyticAt_carlsonZeroDetector_of_ne_one
#print axioms regularizedCarlsonZeroDetector_ne_zero_of_four_le_re
#print axioms one_le_norm_regularizedCarlsonZeroDetector_of_four_le_re
#print axioms log_fiftySix_div_eightyOne_le_log_norm_regularized_of_four_le_re
#print axioms analyticOrderAt_regularizedCarlsonZeroDetector_ne_top
#print axioms carlsonZeroDetector_eq_zero_of_riemannZeta_eq_zero
#print axioms analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector
#print axioms analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
#print axioms meromorphic_regularizedCarlsonZeroDetector
#print axioms regularizedCarlsonZeroDetector_eq_sub_one_sq_mul
#print axioms logDeriv_regularizedCarlsonZeroDetector_eq_two_inv_add
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
#print axioms integral_log_norm_vertical_sub_one_le_length_mul_log
#print axioms regularizedCarlsonLogNormEndpoint_le_explicit
#print axioms regularizedCarlsonLogNormSharpEndpoint_le_explicit
#print axioms log_norm_regularizedCarlsonZeroDetector_eq_two_log_norm_sub_one_add
#print axioms exists_integral_log_norm_carlsonZeroDetector_le_sharpDoublingIntervalExplicit_of_regularizedBoundary
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_sharpEndpoint_of_comparable
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_sharpDoublingIntervalExplicit
#print axioms one_sub_norm_mollifiedZetaError_sq_le_norm_carlsonZeroDetector
#print axioms one_sub_sq_le_norm_carlsonZeroDetector_of_norm_error_le
#print axioms two_log_norm_sub_one_add_log_one_sub_sq_le_log_norm_regularized
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_doublingInterval
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadic
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicExplicit
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSum
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicSumExplicit
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicCover
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_dyadicCoverExplicit
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_low_add_dyadicCover
#print axioms exists_integral_log_norm_regularizedCarlsonZeroDetector_le_low_add_dyadicCoverExplicit

end CarlsonZeroDensity
end PrimeNumberTheorem
