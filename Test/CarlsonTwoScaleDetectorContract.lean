import PrimeNumberTheorem.CarlsonTwoScaleDetector

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (Y0 Y1 : ℕ) {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (twoScaleMollifiedZetaError Y0 Y1) s :=
  analyticAt_twoScaleMollifiedZetaError_of_ne_one Y0 Y1 hs1

example (Y0 Y1 : ℕ) (s : ℂ) :
    twoScaleCarlsonZeroDetector Y0 Y1 s =
      (riemannZeta s * HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s) *
        (2 - riemannZeta s *
          HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s) :=
  twoScaleCarlsonZeroDetector_factorization Y0 Y1 s

example {Y0 Y1 : ℕ} {s : ℂ} (hz : riemannZeta s = 0) :
    twoScaleCarlsonZeroDetector Y0 Y1 s = 0 :=
  twoScaleCarlsonZeroDetector_eq_zero_of_zeta_eq_zero hz

example {Y0 Y1 : ℕ} {rho : ℂ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (twoScaleCarlsonZeroDetector Y0 Y1) rho :=
  analyticOrderNatAt_riemannZeta_le_twoScaleCarlsonZeroDetector
    hY0 hY01 hrho

example {Y0 Y1 : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    regularizedTwoScaleCarlsonZeroDetector Y0 Y1 s =
      (s - 1) ^ 2 * twoScaleCarlsonZeroDetector Y0 Y1 s :=
  regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul hs0 hs1

example {Y0 Y1 : ℕ} {s : ℂ} (hs : 4 ≤ s.re)
    (herr : ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ≤ (1 / 3 : ℝ)) :
    1 ≤ ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 s‖ :=
  one_le_norm_regularizedTwoScaleCarlsonZeroDetector_of_four_le_re hs herr

end CarlsonZeroDensity
end PrimeNumberTheorem
