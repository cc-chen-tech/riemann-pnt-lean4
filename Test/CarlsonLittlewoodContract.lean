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

#print axioms boundaryRectIntegral_regularizedCarlsonZeroDetector_eq_zeroMultiplicitySum
#print axioms two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
#print axioms sub_mul_zeroDensityCount_le_regularizedCarlsonWeightedZeroSum
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_le_fourEdges
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_certificate
#print axioms regularizedCarlsonLittlewood_leftEdge_eq_logNorm
#print axioms regularizedCarlsonLittlewood_rightEdge_eq_logNorm
#print axioms regularizedCarlsonLittlewoodFourEdges_eq_logNormForm
#print axioms regularizedCarlsonLittlewoodFourEdges_eq_logNormFormDef
#print axioms exists_regularizedCarlson_goodRectangle_zeroDensity_le_logNormForm

end CarlsonZeroDensity
end PrimeNumberTheorem
