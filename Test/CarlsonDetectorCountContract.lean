import PrimeNumberTheorem.CarlsonDetectorCount

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (sigma alpha a b : ℝ) : Set ℂ :=
  carlsonDetectorRectangle sigma alpha a b

example (sigma alpha a b : ℝ) :
    IsCompact (carlsonDetectorRectangle sigma alpha a b) :=
  isCompact_carlsonDetectorRectangle sigma alpha a b

example {sigma T : ℝ} (hsigma : 1 / 2 < sigma) :
    carlsonDetectorRectangle sigma 4 T (T + 1) ⊆
      Metric.closedBall ((4 : ℂ) + I * (T + 1 / 2)) (15 / 4 : ℝ) :=
  carlsonDetectorRectangle_subset_fixedJensenInnerDisk hsigma

example (X : ℕ) (T : ℝ) :
    AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X)
      (Metric.closedBall ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ)) :=
  analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk X T

example (X : ℕ) : Meromorphic (carlsonZeroDetector X) :=
  meromorphic_carlsonZeroDetector X

noncomputable example (X : ℕ) (sigma alpha a b : ℝ) : ℕ :=
  carlsonDetectorRectangleZeroCount X sigma alpha a b

noncomputable example (X : ℕ) (sigma alpha a b : ℝ) : Finset ℂ :=
  regularizedCarlsonDetectorRectangleDivisorSupport X sigma alpha a b

noncomputable example (X : ℕ) (sigma alpha a b : ℝ) : ℕ :=
  regularizedCarlsonDetectorRectangleZeroCount X sigma alpha a b

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) :
    (regularizedCarlsonDetectorRectangleZeroCount
        X sigma alpha a b : ℝ) =
      ∑ᶠ u, (MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
        (carlsonDetectorRectangle sigma alpha a b) u : ℝ) :=
  regularizedCarlsonDetectorRectangleZeroCount_cast_eq_finsum_divisor
    hX hsigma

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b r R : ℝ} {c : ℂ}
    (hsigma : 0 < sigma) (hr : 0 < r) (hrR : r < R)
    (hsubset : carlsonDetectorRectangle sigma alpha a b ⊆
      Metric.closedBall c r)
    (hanalytic : AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X)
      (Metric.closedBall c R)) :
    (regularizedCarlsonDetectorRectangleZeroCount
        X sigma alpha a b : ℝ) ≤
      ∑ᶠ u ∈ (Metric.closedBall c r : Set ℂ),
        (MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
          (Metric.closedBall c R) u : ℝ) :=
  regularizedCarlsonDetectorRectangleZeroCount_le_innerDiskDivisorMass
    hX hsigma hr hrR hsubset hanalytic

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b r R K m : ℝ} {c : ℂ}
    (hsigma : 0 < sigma) (hr : 0 < r) (hrR : r < R)
    (hsubset : carlsonDetectorRectangle sigma alpha a b ⊆
      Metric.closedBall c r)
    (hanalytic : AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X)
      (Metric.closedBall c R))
    (hm : 0 < m) (hcenter : m ≤ ‖regularizedCarlsonZeroDetector X c‖)
    (hcircle : Real.circleAverage
      (Real.log ‖regularizedCarlsonZeroDetector X ·‖) c R ≤ K) :
    (regularizedCarlsonDetectorRectangleZeroCount
        X sigma alpha a b : ℝ) ≤
      (K - Real.log m) / Real.log (R / r) :=
  regularizedCarlsonDetectorRectangleZeroCount_le_jensen_log_div
    hX hsigma hr hrR hsubset hanalytic hm hcenter hcircle

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b r R K : ℝ} {c : ℂ}
    (hsigma : 0 < sigma) (hr : 0 < r) (hrR : r < R)
    (hsubset : carlsonDetectorRectangle sigma alpha a b ⊆
      Metric.closedBall c r)
    (hanalytic : AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X)
      (Metric.closedBall c R))
    (hc : 4 ≤ c.re)
    (hcircle : Real.circleAverage
      (Real.log ‖regularizedCarlsonZeroDetector X ·‖) c R ≤ K) :
    (regularizedCarlsonDetectorRectangleZeroCount
        X sigma alpha a b : ℝ) ≤
      K / Real.log (R / r) :=
  regularizedCarlsonDetectorRectangleZeroCount_le_jensen_log_div_of_four_le_center
    hX hsigma hr hrR hsubset hanalytic hc hcircle

example {X : ℕ} (hX : 1 ≤ X) {sigma T K : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hcircle : Real.circleAverage
      (Real.log ‖regularizedCarlsonZeroDetector X ·‖)
        ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ) ≤ K) :
    (regularizedCarlsonDetectorRectangleZeroCount
        X sigma 4 T (T + 1) : ℝ) ≤
      K / Real.log ((31 / 8 : ℝ) / (15 / 4 : ℝ)) :=
  regularizedCarlsonDetectorRectangleZeroCount_le_fixedJensenCircle
    hX hsigma hcircle

example {X : ℕ} (hX : 1 ≤ X) {sigma T M : ℝ}
    (hsigma : 1 / 2 < sigma) (hM : 1 ≤ M)
    (hsphere : ∀ z ∈ Metric.sphere
      ((4 : ℂ) + I * (T + 1 / 2)) (31 / 8 : ℝ),
        ‖regularizedCarlsonZeroDetector X z‖ ≤ M) :
    (regularizedCarlsonDetectorRectangleZeroCount
        X sigma 4 T (T + 1) : ℝ) ≤
      Real.log M / Real.log ((31 / 8 : ℝ) / (15 / 4 : ℝ)) :=
  regularizedCarlsonDetectorRectangleZeroCount_le_fixedJensenSphereNorm
    hX hsigma hM hsphere

noncomputable example (X : ℕ) (sigma alpha T : ℝ) : Finset ℝ :=
  regularizedCarlsonDetectorHorizontalZeroHeights X sigma alpha T

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    (regularizedCarlsonDetectorHorizontalZeroHeights
      X sigma alpha T).card ≤
      regularizedCarlsonDetectorRectangleZeroCount
        X sigma alpha T (T + 1) :=
  card_regularizedCarlsonDetectorHorizontalZeroHeights_le_zeroCount
    hX hsigma

noncomputable example (X : ℕ) (sigma alpha a b : ℝ) (z : ℂ) : ℂ :=
  regularizedCarlsonDetectorRectanglePrincipalPart X sigma alpha a b z

noncomputable example (X : ℕ) (sigma alpha a b : ℝ) (z : ℂ) : ℂ :=
  regularizedCarlsonDetectorRectangleRegularPart X sigma alpha a b z

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b delta : ℝ}
    (hsigma : 0 < sigma) (hdelta : 0 < delta) {z : ℂ}
    (hsep : ∀ u ∈ regularizedCarlsonDetectorRectangleDivisorSupport
        X sigma alpha a b, delta ≤ ‖z - u‖) :
    ‖regularizedCarlsonDetectorRectanglePrincipalPart
        X sigma alpha a b z‖ ≤
      (regularizedCarlsonDetectorRectangleZeroCount
        X sigma alpha a b : ℝ) / delta :=
  norm_regularizedCarlsonDetectorRectanglePrincipalPart_le_count_div
    hX hsigma hdelta hsep

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b) :
    z ∈ regularizedCarlsonDetectorRectangleDivisorSupport X sigma alpha a b ↔
      regularizedCarlsonZeroDetector X z = 0 :=
  mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
    hX hsigma hz

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) :
    AnalyticOnNhd ℂ
      (regularizedCarlsonDetectorRectangleRegularPart X sigma alpha a b)
      (carlsonDetectorRectangle sigma alpha a b) :=
  analyticOnNhd_regularizedCarlsonDetectorRectangleRegularPart hX hsigma

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b)
    (hne : regularizedCarlsonZeroDetector X z ≠ 0) :
    regularizedCarlsonDetectorRectangleRegularPart X sigma alpha a b z =
      logDeriv (regularizedCarlsonZeroDetector X) z -
        regularizedCarlsonDetectorRectanglePrincipalPart
          X sigma alpha a b z :=
  regularizedCarlsonDetectorRectangleRegularPart_eq_logDeriv_sub_principalPart
    hX hsigma hz hne

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    ∃ t : ℝ, T < t ∧ t < T + 1 ∧
      ∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0 :=
  exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
    hX hsigma (T := T)

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ z ∈ regularizedCarlsonDetectorRectangleDivisorSupport
          X sigma alpha T (T + 1),
        1 / ((4 : ℝ) *
            ((regularizedCarlsonDetectorHorizontalZeroHeights
              X sigma alpha T).card + 1)) ≤ |t - z.im|) ∧
      ∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0 :=
  exists_regularizedCarlsonZeroDetector_horizontal_quantitativelySeparated
    hX hsigma (T := T)

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      ∀ x ∈ Set.Icc sigma alpha,
        ‖regularizedCarlsonDetectorRectanglePrincipalPart
          X sigma alpha T (T + 1)
            ((x : ℂ) + (t : ℂ) * I)‖ ≤
          (regularizedCarlsonDetectorRectangleZeroCount
            X sigma alpha T (T + 1) : ℝ) /
            (1 / ((4 : ℝ) *
              ((regularizedCarlsonDetectorHorizontalZeroHeights
                X sigma alpha T).card + 1))) :=
  exists_regularizedCarlsonZeroDetector_horizontal_principalPart_le_count
    hX hsigma (T := T)

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      ∀ x ∈ Set.Icc sigma alpha,
        ‖regularizedCarlsonDetectorRectanglePrincipalPart
          X sigma alpha T (T + 1)
            ((x : ℂ) + (t : ℂ) * I)‖ ≤
          (regularizedCarlsonDetectorRectangleZeroCount
            X sigma alpha T (T + 1) : ℝ) /
            (1 / ((4 : ℝ) *
              ((regularizedCarlsonDetectorRectangleZeroCount
                X sigma alpha T (T + 1) : ℝ) + 1))) :=
  exists_regularizedCarlsonZeroDetector_horizontal_principalPart_le_zeroCount
    hX hsigma (T := T)

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha T M : ℝ}
    (hsigma : 0 < sigma)
    (hregular : ∀ t ∈ Set.Icc T (T + 1), ∀ x ∈ Set.Icc sigma alpha,
      ‖regularizedCarlsonDetectorRectangleRegularPart
        X sigma alpha T (T + 1) ((x : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      ∀ x ∈ Set.Icc sigma alpha,
        ‖logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (t : ℂ) * I)‖ ≤
          M + (regularizedCarlsonDetectorRectangleZeroCount
            X sigma alpha T (T + 1) : ℝ) /
            (1 / ((4 : ℝ) *
              ((regularizedCarlsonDetectorHorizontalZeroHeights
                X sigma alpha T).card + 1))) :=
  exists_regularizedCarlsonZeroDetector_horizontal_logDeriv_le_regular_add_count
    hX hsigma hregular

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha T M : ℝ}
    (hsigma : 0 < sigma)
    (hregular : ∀ t ∈ Set.Icc T (T + 1), ∀ x ∈ Set.Icc sigma alpha,
      ‖regularizedCarlsonDetectorRectangleRegularPart
        X sigma alpha T (T + 1) ((x : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      ∀ x ∈ Set.Icc sigma alpha,
        ‖logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (t : ℂ) * I)‖ ≤
          M + (regularizedCarlsonDetectorRectangleZeroCount
            X sigma alpha T (T + 1) : ℝ) /
            (1 / ((4 : ℝ) *
              ((regularizedCarlsonDetectorRectangleZeroCount
                X sigma alpha T (T + 1) : ℝ) + 1))) :=
  exists_regularizedCarlsonZeroDetector_horizontal_logDeriv_le_regular_add_zeroCount
    hX hsigma hregular

example {X : ℕ} (hX : 1 ≤ X) {sigma0 sigma1 a b : ℝ}
    (hsigma0 : 0 < sigma0) (hsigma : sigma0 < sigma1) :
    ∃ sigma : ℝ, sigma0 < sigma ∧ sigma < sigma1 ∧
      ∀ t ∈ Set.Icc a b,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + (t : ℂ) * I) ≠ 0 :=
  exists_regularizedCarlsonZeroDetector_vertical_ne_zero
    hX hsigma0 hsigma

example {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      sigma / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :=
  exists_regularizedCarlsonZeroDetector_goodRectangle
    hX hsigma hsigmaOne hT

example {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      1 / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :=
  exists_regularizedCarlsonZeroDetector_goodRectangle_half
    hX hsigma hsigmaOne hT

example {X : ℕ} (hX : 1 ≤ X) {theta sigma T : ℝ}
    (htheta : 0 < theta) (hthetaSigma : theta < sigma)
    (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      theta < x0 ∧ x0 < sigma ∧ x1 = 4 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :=
  exists_regularizedCarlsonZeroDetector_goodRectangle_fixedRight_of_leftWindow
    hX htheta hthetaSigma hsigmaOne hT

example {X : ℕ} (hX : 1 ≤ X) (sigma T : ℝ) :
    ZeroDensity.zeroDensityCount sigma T ≤
      carlsonDetectorRectangleZeroCount X sigma 1 0 T :=
  zeroDensityCount_le_carlsonDetectorRectangleZeroCount hX sigma T

example {X : ℕ} (hX : 1 ≤ X) (sigma T : ℝ) :
    ZeroDensity.zeroDensityCount sigma T ≤
      regularizedCarlsonDetectorRectangleZeroCount X sigma 1 0 T :=
  zeroDensityCount_le_regularizedCarlsonDetectorRectangleZeroCount hX sigma T

#print axioms isCompact_carlsonDetectorRectangle
#print axioms carlsonDetectorRectangle_subset_fixedJensenInnerDisk
#print axioms analyticOnNhd_regularizedCarlsonZeroDetector_fixedJensenOuterDisk
#print axioms meromorphic_carlsonZeroDetector
#print axioms zeroDensityCount_le_carlsonDetectorRectangleZeroCount
#print axioms zeroDensityCount_le_regularizedCarlsonDetectorRectangleZeroCount
#print axioms mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
#print axioms card_regularizedCarlsonDetectorHorizontalZeroHeights_le_zeroCount
#print axioms regularizedCarlsonDetectorRectangleZeroCount_cast_eq_finsum_divisor
#print axioms regularizedCarlsonDetectorRectangleZeroCount_le_innerDiskDivisorMass
#print axioms regularizedCarlsonDetectorRectangleZeroCount_le_jensen_log_div
#print axioms regularizedCarlsonDetectorRectangleZeroCount_le_jensen_log_div_of_four_le_center
#print axioms regularizedCarlsonDetectorRectangleZeroCount_le_fixedJensenCircle
#print axioms regularizedCarlsonDetectorRectangleZeroCount_le_fixedJensenSphereNorm
#print axioms analyticOnNhd_regularizedCarlsonDetectorRectangleRegularPart
#print axioms regularizedCarlsonDetectorRectangleRegularPart_eq_logDeriv_sub_principalPart
#print axioms norm_regularizedCarlsonDetectorRectanglePrincipalPart_le_count_div
#print axioms exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
#print axioms exists_regularizedCarlsonZeroDetector_horizontal_quantitativelySeparated
#print axioms exists_regularizedCarlsonZeroDetector_horizontal_principalPart_le_count
#print axioms exists_regularizedCarlsonZeroDetector_horizontal_logDeriv_le_regular_add_count
#print axioms exists_regularizedCarlsonZeroDetector_horizontal_principalPart_le_zeroCount
#print axioms exists_regularizedCarlsonZeroDetector_horizontal_logDeriv_le_regular_add_zeroCount
#print axioms exists_regularizedCarlsonZeroDetector_vertical_ne_zero
#print axioms exists_regularizedCarlsonZeroDetector_goodRectangle_of_leftWindow
#print axioms exists_regularizedCarlsonZeroDetector_goodRectangle
#print axioms exists_regularizedCarlsonZeroDetector_goodRectangle_half
#print axioms exists_regularizedCarlsonZeroDetector_goodRectangle_fixedRight_of_leftWindow

end CarlsonZeroDensity
end PrimeNumberTheorem
