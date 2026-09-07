import PrimeNumberTheorem.CarlsonTwoScaleRectangle

open Complex Set
open PrimeNumberTheorem.CarlsonZeroDensity

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {sigma alpha a b : ℝ} (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b) :
    z ∈ regularizedTwoScaleCarlsonRectangleDivisorSupport Y0 Y1 sigma alpha a b ↔
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z = 0 :=
  mem_regularizedTwoScaleCarlsonRectangleDivisorSupport_iff_zero hY0 hY01 hsigma hz

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {sigma0 sigma1 a b : ℝ} (hsigma0 : 0 < sigma0) (hsigma : sigma0 < sigma1) :
    ∃ x ∈ Ioo sigma0 sigma1, ∀ t ∈ Icc a b,
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ)) ≠ 0 :=
  exists_regularizedTwoScaleCarlson_vertical_ne_zero hY0 hY01 hsigma0 hsigma

#print axioms mem_regularizedTwoScaleCarlsonRectangleDivisorSupport_iff_zero
#print axioms exists_regularizedTwoScaleCarlson_vertical_ne_zero
