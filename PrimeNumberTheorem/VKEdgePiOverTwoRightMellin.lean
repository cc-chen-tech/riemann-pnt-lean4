import PrimeNumberTheorem
import PrimeNumberTheorem.VKEdgePiOverTwoGaussianMellin
import PrimeNumberTheorem.VKEdgePiOverTwoZetaContour

open Complex MeasureTheory Polynomial Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/--
On the Euler-product half-plane, the regularized logarithmic derivative is
the Mellin transform of the cutoff Chebyshev error.
-/
theorem neg_logDeriv_sub_pole_eq_mul_mellin
    {s : ℂ} (hs : 1 < s.re) :
    -logDeriv riemannZeta s - s / (s - 1) =
      s * mellin psiErrorAboveOneComplex (-s) := by
  simpa only [logDeriv_apply, neg_div] using
    (mul_mellin_psiErrorAboveOneComplex_neg_eq_neg_logDeriv_sub_pole
      hs).symm

/--
The right edge `s = w + (2 + i t)` always lies in the Mellin half-plane
when the real part of the contour center is positive.
-/
theorem neg_logDeriv_sub_pole_rightEdge_eq_mul_mellin
    {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    -logDeriv riemannZeta
          (w + ((2 : ℂ) + I * (t : ℂ))) -
        (w + ((2 : ℂ) + I * (t : ℂ))) /
          (w + ((2 : ℂ) + I * (t : ℂ)) - 1) =
      (w + ((2 : ℂ) + I * (t : ℂ))) *
        mellin psiErrorAboveOneComplex
          (-(w + ((2 : ℂ) + I * (t : ℂ)))) := by
  apply neg_logDeriv_sub_pole_eq_mul_mellin
  have hre :
      (w + ((2 : ℂ) + I * (t : ℂ))).re =
        w.re + 2 := by
    norm_num [Complex.add_re, Complex.mul_re]
  rw [hre]
  linarith

/--
For a positive real base, the complex power on the shifted right edge
splits into the fixed Mellin factor and the Fourier-Gaussian factor.
-/
theorem ofReal_cpow_neg_add_split
    {x : ℝ} (hx : 0 < x) (w z : ℂ) :
    (x : ℂ) ^ (-(w + z + 1)) =
      (x : ℂ) ^ (-(w + 1)) *
        Complex.exp (-((Real.log x : ℝ) : ℂ) * z) := by
  have hx0 : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  rw [show -(w + z + 1) = -(w + 1) + (-z) by ring]
  rw [Complex.cpow_add _ _ hx0]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hx0]
  rw [Complex.ofReal_log hx.le]
  congr 1
  ring

/--
For fixed `x > 1`, the full right-edge Gaussian integral is exactly the
inverse Gaussian kernel and its derivative. The right edge is parameterized
as `s = w + (2 + i t)`.
-/
theorem integral_rightEdgePolynomialGaussian_cpow_eq
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        (w + ((2 : ℂ) + I * (t : ℂ))) *
          A.eval ((2 : ℂ) + I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * ((2 : ℂ) + I * (t : ℂ)) ^ 2 +
              ((16 * m : ℝ) : ℂ) *
                ((2 : ℂ) + I * (t : ℂ))) *
          (x : ℂ) ^
            (-((w + ((2 : ℂ) + I * (t : ℂ))) + 1))) =
      (2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (16 * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (16 * m - Real.log x))) := by
  let z : ℝ → ℂ := fun t => (2 : ℂ) + I * (t : ℂ)
  let r : ℝ := 16 * m - Real.log x
  have hintegrand :
      (fun t : ℝ =>
        (w + z t) * A.eval (z t) *
          Complex.exp
            ((m : ℂ) * (z t) ^ 2 +
              ((16 * m : ℝ) : ℂ) * z t) *
          (x : ℂ) ^ (-((w + z t) + 1))) =
        fun t : ℝ =>
          (x : ℂ) ^ (-(w + 1)) *
            ((w + z t) * A.eval (z t) *
              Complex.exp
                ((m : ℂ) * (z t) ^ 2 +
                  (r : ℂ) * z t)) := by
    funext t
    rw [ofReal_cpow_neg_add_split hx w (z t)]
    calc
      (w + z t) * A.eval (z t) *
            Complex.exp
              ((m : ℂ) * (z t) ^ 2 +
                ((16 * m : ℝ) : ℂ) * z t) *
            ((x : ℂ) ^ (-(w + 1)) *
              Complex.exp (-((Real.log x : ℝ) : ℂ) * z t)) =
          (x : ℂ) ^ (-(w + 1)) *
            ((w + z t) * A.eval (z t) *
              (Complex.exp
                  ((m : ℂ) * (z t) ^ 2 +
                    ((16 * m : ℝ) : ℂ) * z t) *
                Complex.exp
                  (-((Real.log x : ℝ) : ℂ) * z t))) := by
        ring
      _ =
          (x : ℂ) ^ (-(w + 1)) *
            ((w + z t) * A.eval (z t) *
              Complex.exp
                ((m : ℂ) * (z t) ^ 2 +
                  (r : ℂ) * z t)) := by
        rw [← Complex.exp_add]
        dsimp [r]
        congr 1
        push_cast
        ring
  have hinner :
      (∫ t : ℝ,
          (w + z t) * A.eval (z t) *
            Complex.exp
              ((m : ℂ) * (z t) ^ 2 +
                (r : ℂ) * z t)) =
        (2 * Real.pi : ℂ) *
          (w * polynomialGaussianKernel A m r +
            polynomialGaussianKernelDeriv A m r) := by
    simpa [z] using
      integral_verticalPolynomialGaussian_add_mul_eq
        A hm w 2 r
  change
    (∫ t : ℝ,
        (w + z t) * A.eval (z t) *
          Complex.exp
            ((m : ℂ) * (z t) ^ 2 +
              ((16 * m : ℝ) : ℂ) * z t) *
          (x : ℂ) ^ (-((w + z t) + 1))) = _
  rw [hintegrand]
  calc
    (∫ t : ℝ,
        (x : ℂ) ^ (-(w + 1)) *
          ((w + z t) * A.eval (z t) *
            Complex.exp
              ((m : ℂ) * (z t) ^ 2 +
                (r : ℂ) * z t))) =
        (x : ℂ) ^ (-(w + 1)) *
          (∫ t : ℝ,
            (w + z t) * A.eval (z t) *
              Complex.exp
                ((m : ℂ) * (z t) ^ 2 +
                  (r : ℂ) * z t)) :=
      integral_const_mul _ _
    _ =
        (x : ℂ) ^ (-(w + 1)) *
          ((2 * Real.pi : ℂ) *
            (w * polynomialGaussianKernel A m r +
              polynomialGaussianKernelDeriv A m r)) := by
      exact congrArg ((x : ℂ) ^ (-(w + 1)) * ·) hinner
    _ = _ := by
      dsimp [r]
      ring

/--
The concrete zeta integrand on the right edge is pointwise equal to the
localized Gaussian weight times the Mellin transform of `ψ(x) - x`.
-/
theorem localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge_eq
    (A : ℂ[X]) {w : ℂ} (hw : 0 < w.re)
    (m t : ℝ) :
    localizedGaussianWeight A w m
        (w + ((2 : ℂ) + I * (t : ℂ))) *
        (-logDeriv riemannZeta
            (w + ((2 : ℂ) + I * (t : ℂ))) -
          (w + ((2 : ℂ) + I * (t : ℂ))) /
            (w + ((2 : ℂ) + I * (t : ℂ)) - 1)) =
      localizedGaussianWeight A w m
          (w + ((2 : ℂ) + I * (t : ℂ))) *
        ((w + ((2 : ℂ) + I * (t : ℂ))) *
          mellin psiErrorAboveOneComplex
            (-(w + ((2 : ℂ) + I * (t : ℂ))))) := by
  rw [neg_logDeriv_sub_pole_rightEdge_eq_mul_mellin hw t]

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
