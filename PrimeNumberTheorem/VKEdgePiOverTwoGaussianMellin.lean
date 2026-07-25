import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import PrimeNumberTheorem.VKEdgePiOverTwoPolynomialGaussian

open Complex MeasureTheory Polynomial

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/--
The inverse Gaussian kernel is independent of the vertical line on which it
is evaluated.  This is the constant-polynomial core of the localized
Gaussian--Mellin transform.
-/
theorem integral_verticalGaussian_eq
    {m : ℝ} (hm : 0 < m) (c r : ℝ) :
    (∫ t : ℝ,
        Complex.exp
          ((m : ℂ) * ((c : ℂ) + I * t) ^ 2 +
            (r : ℂ) * ((c : ℂ) + I * t))) =
      (2 * Real.pi : ℂ) * (normalizedGaussian m r : ℂ) := by
  have hintegrand :
      (fun t : ℝ =>
        Complex.exp
          ((m : ℂ) * ((c : ℂ) + I * t) ^ 2 +
            (r : ℂ) * ((c : ℂ) + I * t))) =
        fun t : ℝ =>
          Complex.exp
            ((-(m : ℂ)) * (t : ℂ) ^ 2 +
              (I * (2 * m * c + r : ℝ)) * (t : ℂ) +
              (m * c ^ 2 + r * c : ℝ)) := by
    funext t
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [hintegrand]
  rw [integral_cexp_quadratic (by simp [hm])]
  have hexponent :
      ((m * c ^ 2 + r * c : ℝ) : ℂ) -
          (I * (2 * m * c + r : ℝ)) ^ 2 /
            (4 * (-(m : ℂ))) =
        (-(r ^ 2 / (4 * m)) : ℝ) := by
    push_cast
    field_simp [hm.ne']
    ring_nf
    rw [I_sq]
    ring
  rw [hexponent]
  have hsqrtCpow :
      ((Real.pi : ℂ) / (m : ℂ)) ^ (1 / 2 : ℂ) =
        (Real.sqrt (Real.pi / m) : ℂ) := by
    symm
    rw [Real.sqrt_eq_rpow]
    simpa only [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (show 0 ≤ Real.pi / m by positivity)
        (1 / 2 : ℝ))
  have hscale :
      Real.sqrt (Real.pi / m) =
        2 * Real.pi / (2 * Real.sqrt (Real.pi * m)) := by
    rw [Real.sqrt_div Real.pi_nonneg,
      Real.sqrt_mul Real.pi_nonneg]
    field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos,
      Real.sqrt_ne_zero'.mpr hm]
    nlinarith [Real.sq_sqrt Real.pi_nonneg, Real.sq_sqrt hm.le]
  simp only [neg_neg, hsqrtCpow, normalizedGaussian]
  rw [show (Real.sqrt (Real.pi / m) : ℂ) =
      (2 * Real.pi / (2 * Real.sqrt (Real.pi * m)) : ℝ) by
    exact_mod_cast hscale]
  push_cast
  ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
