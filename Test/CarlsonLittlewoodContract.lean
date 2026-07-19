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

#print axioms boundaryRectIntegral_regularizedCarlsonZeroDetector_eq_zeroMultiplicitySum
#print axioms two_pi_mul_regularizedCarlsonZeroMultiplicityWeightedRealSum_eq_four_edges
#print axioms sub_mul_zeroDensityCount_le_regularizedCarlsonWeightedZeroSum

end CarlsonZeroDensity
end PrimeNumberTheorem
