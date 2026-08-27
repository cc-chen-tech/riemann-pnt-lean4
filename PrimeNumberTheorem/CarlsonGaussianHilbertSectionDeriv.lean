import PrimeNumberTheorem.CarlsonGaussianHilbertSection
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Pointwise complex derivative of the Carlson Gaussian section

This file records the exact derivative in the complex strip parameter.  It
is the pointwise input for the later `L²(ℝ)` difference-quotient argument.
-/

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Exact pointwise derivative of the Gaussian Hilbert section with respect
to its complex strip parameter. -/
noncomputable def carlsonGaussianHilbertSectionDeriv
    (Delta w : ℝ) (H : ℂ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  let q := z + I * (t : ℂ) - I * (w : ℂ)
  Complex.exp (q ^ 2 / (2 * (Delta : ℂ) ^ 2)) *
    (q / (Delta : ℂ) ^ 2 * H (z + I * (t : ℂ)) +
      deriv H (z + I * (t : ℂ)))

/-- The displayed pointwise derivative formula is valid whenever `H` is
analytic at the translated point. -/
theorem hasDerivAt_carlsonGaussianHilbertSection
    {Delta w : ℝ} {H : ℂ → ℂ} {z : ℂ} {t : ℝ}
    (hDelta : Delta ≠ 0)
    (hH : AnalyticAt ℂ H (z + I * (t : ℂ))) :
    HasDerivAt
      (fun u : ℂ => carlsonGaussianHilbertSection Delta w H u t)
      (carlsonGaussianHilbertSectionDeriv Delta w H z t) z := by
  have hDeltaSq : (Delta : ℂ) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (ofReal_ne_zero.mpr hDelta)
  let point : ℂ → ℂ := fun u => u + I * (t : ℂ)
  let qfun : ℂ → ℂ := fun u => point u - I * (w : ℂ)
  let exponent : ℂ → ℂ := fun u =>
    qfun u ^ 2 / (2 * (Delta : ℂ) ^ 2)
  have hpoint : HasDerivAt point 1 z := by
    dsimp [point]
    simpa using (hasDerivAt_id z).add_const (I * (t : ℂ))
  have hq : HasDerivAt qfun 1 z := by
    dsimp [qfun]
    simpa using hpoint.sub_const (I * (w : ℂ))
  have hexponent :
      HasDerivAt exponent
        (qfun z / (Delta : ℂ) ^ 2) z := by
    dsimp [exponent]
    apply ((hq.pow 2).div_const (2 * (Delta : ℂ) ^ 2)).congr_deriv
    field_simp [hDeltaSq]
    ring
  have hexp :
      HasDerivAt (fun u => Complex.exp (exponent u))
        (Complex.exp (exponent z) *
          (qfun z / (Delta : ℂ) ^ 2)) z :=
    hexponent.cexp
  have hHcomp :
      HasDerivAt (fun u => H (point u))
        (deriv H (point z)) z := by
    simpa [Function.comp_def] using
      hH.differentiableAt.hasDerivAt.comp z hpoint
  change HasDerivAt
    (fun u : ℂ => Complex.exp (exponent u) * H (point u))
    (carlsonGaussianHilbertSectionDeriv Delta w H z t) z
  apply (hexp.mul hHcomp).congr_deriv
  dsimp [carlsonGaussianHilbertSectionDeriv, point, qfun, exponent]
  ring

end CarlsonZeroDensity
end PrimeNumberTheorem
