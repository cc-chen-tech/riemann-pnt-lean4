import PrimeNumberTheorem.CarlsonLittlewood

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {X : ℕ} (hX : 1 ≤ X) {x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx01 : x0 < x1) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    MathlibAux.boundaryRectIntegral
        (fun z : ℂ => (z - (x0 : ℂ)) *
          logDeriv (regularizedCarlsonZeroDetector X) z)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 x1 y0 y1,
          (rho - (x0 : ℂ)) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℂ) :=
  boundaryRectIntegral_regularizedCarlsonZeroDetector_eq_zeroMultiplicitySum
    hX hx0 hx01 hy01 hleft hright hbottom htop

example {X : ℕ} (hX : 1 ≤ X) {x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx01 : x0 < x1) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    (2 * Real.pi) *
        ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
            X x0 x1 y0 y1,
          (rho.re - x0) *
            (analyticOrderNatAt
              (regularizedCarlsonZeroDetector X) rho : ℝ) =
      (∫ x in x0..x1,
          ((((x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ)) *
            logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (y0 : ℂ) * I))).im) -
        (∫ x in x0..x1,
          ((((x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ)) *
            logDeriv (regularizedCarlsonZeroDetector X)
              ((x : ℂ) + (y1 : ℂ) * I))).im) +
        (∫ y in y0..y1,
          ((((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv (regularizedCarlsonZeroDetector X)
              ((x1 : ℂ) + (y : ℂ) * I))).re) -
        (∫ y in y0..y1,
          ((((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv (regularizedCarlsonZeroDetector X)
              ((x0 : ℂ) + (y : ℂ) * I))).re) :=
  two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
    hX hx0 hx01 hy01 hleft hright hbottom htop

example {X : ℕ} (hX : 1 ≤ X) {sigma T x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx0sigma : x0 < sigma)
    (hx1 : 1 < x1) (hy0 : y0 < 0) (hy1 : T < y1) :
    (sigma - x0) * (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
      ∑ rho ∈ regularizedCarlsonDetectorRectangleDivisorSupport
          X x0 x1 y0 y1,
        (rho.re - x0) *
          (analyticOrderNatAt
            (regularizedCarlsonZeroDetector X) rho : ℝ) :=
  sub_mul_zeroDensityCount_le_regularizedCarlsonWeightedZeroSum
    hX hx0 hx0sigma hx1 hy0 hy1

example {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      sigma / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 :=
  exists_regularizedCarlson_goodRectangle_zeroDensity_le_fourEdges
    hX hsigma hsigmaOne hT

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
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 :=
  exists_regularizedCarlson_goodRectangle_zeroDensity_certificate
    hX hsigma hsigmaOne hT

example {X : ℕ} {x0 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) :
    (∫ y in y0..y1,
        ((((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv (regularizedCarlsonZeroDetector X)
            ((x0 : ℂ) + (y : ℂ) * I))).re) =
      y1 * Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y1 : ℂ) * I)‖ -
      y0 * Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y0 : ℂ) * I)‖ -
      ∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I)‖ :=
  regularizedCarlsonLittlewood_leftEdge_eq_logNorm hx0 hy01 hleft

example {X : ℕ} {x0 x1 y0 y1 : ℝ}
    (hx1 : 0 < x1) (hy01 : y0 < y1)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) :
    (∫ y in y0..y1,
        ((((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv (regularizedCarlsonZeroDetector X)
            ((x1 : ℂ) + (y : ℂ) * I))).re) =
      (x1 - x0) *
        (∫ y in y0..y1,
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x1 : ℂ) + (y : ℂ) * I)).re) +
      y1 * Real.log ‖regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y1 : ℂ) * I)‖ -
      y0 * Real.log ‖regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y0 : ℂ) * I)‖ -
      ∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I)‖ :=
  regularizedCarlsonLittlewood_rightEdge_eq_logNorm hx1 hy01 hright

example {X : ℕ} {x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx01 : x0 < x1) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 =
      (∫ x in x0..x1,
        (x - x0) *
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y0 : ℂ) * I)).im) -
      (∫ x in x0..x1,
        (x - x0) *
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y1 : ℂ) * I)).im) +
      (x1 - x0) *
        (∫ y in y0..y1,
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x1 : ℂ) + (y : ℂ) * I)).re) +
      (∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I)‖) -
      (∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I)‖) :=
  regularizedCarlsonLittlewoodFourEdges_eq_logNormForm
    hx0 hx01 hy01 hleft hright hbottom htop

noncomputable example (X : ℕ) (x0 x1 y0 y1 : ℝ) : ℝ :=
  regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1

noncomputable example (X : ℕ) (x0 x1 y0 y1 : ℝ) : ℝ :=
  regularizedCarlsonLittlewoodRemainingEdges X x0 x1 y0 y1

example (X : ℕ) (x0 x1 y0 y1 : ℝ) :
    regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 =
      (∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I)‖) +
      regularizedCarlsonLittlewoodRemainingEdges X x0 x1 y0 y1 :=
  regularizedCarlsonLittlewoodLogNormForm_eq_left_add_remaining
    X x0 x1 y0 y1

noncomputable example (A : ℝ) (X : ℕ) (x0 y0 y1 : ℝ) (n : ℕ) : ℝ :=
  regularizedCarlsonLeftEdgeExplicitBound A X x0 y0 y1 n

example {X : ℕ} (hX : 1 ≤ X) {y0 y1 : ℝ} (hy01 : y0 ≤ y1) :
    -(∫ y in y0..y1,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((4 : ℂ) + I * (y : ℂ))‖) ≤
      -(y1 - y0) * Real.log (56 / 81 : ℝ) :=
  neg_integral_log_norm_regularizedCarlson_fixedRight_le hX hy01

noncomputable example (X : ℕ) (y0 y1 : ℝ) : ℝ :=
  carlsonDetectorFixedRightArgumentVariation X y0 y1

example {X : ℕ} (hX : 1 ≤ X) (y0 y1 : ℝ) :
    |carlsonDetectorFixedRightArgumentVariation X y0 y1| ≤ Real.pi :=
  abs_carlsonDetectorFixedRightArgumentVariation_le_pi hX y0 y1

noncomputable example (y0 y1 : ℝ) : ℝ :=
  subOneFixedRightArgumentVariation y0 y1

example (y0 y1 : ℝ) :
    |subOneFixedRightArgumentVariation y0 y1| ≤ Real.pi :=
  abs_subOneFixedRightArgumentVariation_le_pi y0 y1

noncomputable example (X : ℕ) (y0 y1 : ℝ) : ℝ :=
  regularizedCarlsonFixedRightArgumentVariation X y0 y1

example {X : ℕ} (hX : 1 ≤ X) (y0 y1 : ℝ) :
    |regularizedCarlsonFixedRightArgumentVariation X y0 y1| ≤
      3 * Real.pi :=
  abs_regularizedCarlsonFixedRightArgumentVariation_le_three_pi
    hX y0 y1

noncomputable example (X : ℕ) (x0 y0 y1 : ℝ) : ℝ :=
  regularizedCarlsonFixedRightBoundaryContribution X x0 y0 y1

example {X : ℕ} (hX : 1 ≤ X) {x0 y0 y1 : ℝ}
    (hx0 : x0 ≤ 4) (hy01 : y0 ≤ y1) :
    regularizedCarlsonFixedRightBoundaryContribution X x0 y0 y1 ≤
      (4 - x0) * (3 * Real.pi) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) :=
  regularizedCarlsonFixedRightBoundaryContribution_le hX hx0 hy01

example (X : ℕ) (x0 y0 y1 : ℝ) :
    regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 =
      (∫ x in x0..4,
        (x - x0) *
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y0 : ℂ) * I)).im) -
      (∫ x in x0..4,
        (x - x0) *
          (logDeriv (regularizedCarlsonZeroDetector X)
            ((x : ℂ) + (y1 : ℂ) * I)).im) +
      regularizedCarlsonFixedRightBoundaryContribution X x0 y0 y1 :=
  regularizedCarlsonLittlewoodRemainingEdges_fixedRight_eq X x0 y0 y1

noncomputable example (X : ℕ) (x0 y : ℝ) : ℝ :=
  regularizedCarlsonHorizontalArgumentTerm X x0 y

example {X : ℕ} {x0 y M : ℝ}
    (hx0 : x0 ≤ 4) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y : ℂ) * I)‖ ≤ M) :
    |regularizedCarlsonHorizontalArgumentTerm X x0 y| ≤
      (4 - x0) ^ 2 * M :=
  abs_regularizedCarlsonHorizontalArgumentTerm_le_sq_mul
    hx0 hM hbound

example {X : ℕ} (hX : 1 ≤ X) {x0 y0 y1 M0 M1 : ℝ}
    (hx0 : x0 ≤ 4) (hy01 : y0 ≤ y1)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hbottom : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y0 : ℂ) * I)‖ ≤ M0)
    (htop : ∀ x ∈ Set.Icc x0 4,
      ‖logDeriv (regularizedCarlsonZeroDetector X)
        ((x : ℂ) + (y1 : ℂ) * I)‖ ≤ M1) :
    regularizedCarlsonLittlewoodRemainingEdges X x0 4 y0 y1 ≤
      (4 - x0) ^ 2 * (M0 + M1) +
        (4 - x0) * (3 * Real.pi) -
        (y1 - y0) * Real.log (56 / 81 : ℝ) :=
  regularizedCarlsonLittlewoodRemainingEdges_fixedRight_le_of_horizontalBounds
    hX hx0 hy01 hM0 hM1 hbottom htop

example {X : ℕ} {x0 x1 y0 y1 : ℝ}
    (hx0 : 0 < x0) (hx01 : x0 < x1) (hy01 : y0 < y1)
    (hleft : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Set.Icc y0 y1,
      regularizedCarlsonZeroDetector X
        ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.Icc x0 x1,
      regularizedCarlsonZeroDetector X
        ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 =
      regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 :=
  regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
    hx0 hx01 hy01 hleft hright hbottom htop

example {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      sigma / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 :=
  exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm
    hX hsigma hsigmaOne hT

example {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      1 / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodLogNormForm X x0 x1 y0 y1 :=
  exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm_half
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
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) ∧
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        regularizedCarlsonLittlewoodFourEdges X x0 x1 y0 y1 :=
  exists_regularizedCarlson_goodRectangle_fixedRight_zeroDensity_certificate_of_leftWindow
    hX htheta hthetaSigma hsigmaOne hT

#print axioms boundaryRectIntegral_regularizedCarlsonZeroDetector_eq_zeroMultiplicitySum
#print axioms two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
#print axioms sub_mul_zeroDensityCount_le_regularizedCarlsonWeightedZeroSum
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_le_fourEdges
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_certificate_of_leftWindow
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_certificate
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_certificate_half
#print axioms exists_regularizedCarlson_goodRectangle_fixedRight_zeroDensity_certificate_of_leftWindow
#print axioms regularizedCarlsonLittlewood_leftEdge_eq_logNorm
#print axioms regularizedCarlsonLittlewood_rightEdge_eq_logNorm
#print axioms neg_integral_log_norm_regularizedCarlson_fixedRight_le
#print axioms abs_carlsonDetectorFixedRightArgumentVariation_le_pi
#print axioms abs_subOneFixedRightArgumentVariation_le_pi
#print axioms abs_regularizedCarlsonFixedRightArgumentVariation_le_three_pi
#print axioms regularizedCarlsonFixedRightBoundaryContribution_le
#print axioms regularizedCarlsonLittlewoodRemainingEdges_fixedRight_eq
#print axioms abs_regularizedCarlsonHorizontalArgumentTerm_le_sq_mul
#print axioms regularizedCarlsonLittlewoodRemainingEdges_fixedRight_le_of_horizontalBounds
#print axioms regularizedCarlsonLittlewoodFourEdges_eq_logNormForm
#print axioms regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
#print axioms regularizedCarlsonLittlewoodLogNormForm_eq_left_add_remaining
#print axioms zeroDensityCount_le_leftBound_add_remaining
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm_of_leftWindow
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm_half
#check exists_regularizedCarlson_dyadicRectangle_count_and_leftEdgeExplicit
#print axioms exists_regularizedCarlson_dyadicRectangle_count_and_leftEdgeExplicit

end CarlsonZeroDensity
end PrimeNumberTheorem
