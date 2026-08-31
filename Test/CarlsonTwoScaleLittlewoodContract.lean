import PrimeNumberTheorem.CarlsonTwoScaleLittlewood

set_option autoImplicit false

open Complex Set
open scoped BigOperators
open PrimeNumberTheorem.CarlsonZeroDensity

example {Y0 Y1 : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    analyticOrderNatAt (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) s =
      analyticOrderNatAt (twoScaleCarlsonZeroDetector Y0 Y1) s :=
  analyticOrderNatAt_regularizedTwoScale_eq hs0 hs1

example {Y0 Y1 : ℕ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) rho :=
  analyticOrderNatAt_riemannZeta_le_regularizedTwoScale hY0 hY01 hrho

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {x0 x1 y0 y1 : ℝ} (hx0 : 0 < x0) (hx : x0 ≤ x1) (hy : y0 ≤ y1)
    (hleft : ∀ y ∈ Icc y0 y1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Icc y0 y1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Icc x0 x1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Icc x0 x1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    (2 * Real.pi) * ∑ z ∈ regularizedTwoScaleCarlsonRectangleDivisorSupport Y0 Y1 x0 x1 y0 y1,
      (z.re - x0) * (analyticOrderNatAt (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) z : ℝ) =
      rectangleLittlewoodLogNormForm (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) x0 x1 y0 y1 :=
  two_pi_mul_twoScaleRectangleZeroSum_eq_logNormForm hY0 hY01 hx0 hx hy hleft hright hbottom htop

#print axioms analyticOrderNatAt_regularizedTwoScale_eq
#print axioms analyticOrderNatAt_riemannZeta_le_regularizedTwoScale
#print axioms two_pi_mul_twoScaleRectangleZeroSum_eq_logNormForm

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {sigma x0 x1 y0 y1 : ℝ} (hx0 : 0 < x0) (hx : x0 ≤ x1)
    (hxSigma : x0 ≤ sigma) (hx1 : 1 ≤ x1) (hy : y0 ≤ y1)
    (S : Finset ℂ)
    (hS : ∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho ∧
      sigma ≤ rho.re ∧ y0 ≤ rho.im ∧ rho.im ≤ y1)
    (hleft : ∀ y ∈ Icc y0 y1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x0 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ Icc y0 y1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x1 : ℂ) + (y : ℂ) * I) ≠ 0)
    (hbottom : ∀ x ∈ Icc x0 x1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Icc x0 x1, regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    (2 * Real.pi) * ((sigma - x0) * ∑ rho ∈ S, (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
      rectangleLittlewoodLogNormForm (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) x0 x1 y0 y1 :=
  two_pi_mul_twoScaleZetaFamilyCount_le_logNormForm hY0 hY01 hx0 hx hxSigma hx1 hy S hS
    hleft hright hbottom htop

#print axioms two_pi_mul_twoScaleZetaFamilyCount_le_logNormForm
