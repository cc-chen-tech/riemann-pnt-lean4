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
The Chebyshev error times its Mellin kernel is absolutely integrable on
`(1, ∞)` throughout the half-plane `Re(s) > 1`.
-/
theorem integrableOn_psiErrorAboveOneComplex_mul_cpow
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun x : ℝ =>
        psiErrorAboveOneComplex x *
          (x : ℂ) ^ (-(s + 1)))
      (Set.Ioi (1 : ℝ)) := by
  have herrorOne : PsiPowerErrorBound 1 := by
    simpa [PsiPowerErrorBound, Real.rpow_one] using
      chebyshevPsi_sub_id_isBigO_id
  have hconv :
      MellinConvergent psiErrorAboveOneComplex (-s) :=
    mellinConvergent_psiErrorAboveOneComplex_neg_of_power_error
      herrorOne hs
  rw [MellinConvergent] at hconv
  have hrestricted :=
    hconv.mono_set
      (Set.Ioi_subset_Ioi
        (show (0 : ℝ) ≤ 1 by norm_num))
  refine hrestricted.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul]
  rw [show -s - 1 = -(s + 1) by ring]
  ring

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

/-- The polynomial-Gaussian factor on the infinite right edge. -/
def rightEdgeGaussianFactor
    (A : ℂ[X]) (m : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  (w + ((2 : ℂ) + I * (t : ℂ))) *
    A.eval ((2 : ℂ) + I * (t : ℂ)) *
    Complex.exp
      ((m : ℂ) * ((2 : ℂ) + I * (t : ℂ)) ^ 2 +
        ((16 * m : ℝ) : ℂ) *
          ((2 : ℂ) + I * (t : ℂ)))

/--
The factor used in the Mellin calculation is exactly the localized contour
weight multiplied by the right-edge coordinate.
-/
theorem rightEdgeGaussianFactor_eq_localizedGaussianWeight_mul
    (A : ℂ[X]) (m : ℝ) (w : ℂ) (t : ℝ) :
    rightEdgeGaussianFactor A m w t =
      localizedGaussianWeight A w m
          (w + ((2 : ℂ) + I * (t : ℂ))) *
        (w + ((2 : ℂ) + I * (t : ℂ))) := by
  unfold rightEdgeGaussianFactor localizedGaussianWeight
  ring_nf

/--
On the concrete right edge, the regularized zeta logarithmic derivative
times the localized contour weight is the Mellin factor used below.
-/
theorem localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge_eq_factor
    (A : ℂ[X]) {w : ℂ} (hw : 0 < w.re)
    (m t : ℝ) :
    localizedGaussianWeight A w m
        (w + ((2 : ℂ) + I * (t : ℂ))) *
        (-logDeriv riemannZeta
            (w + ((2 : ℂ) + I * (t : ℂ))) -
          (w + ((2 : ℂ) + I * (t : ℂ))) /
            (w + ((2 : ℂ) + I * (t : ℂ)) - 1)) =
      rightEdgeGaussianFactor A m w t *
        mellin psiErrorAboveOneComplex
          (-(w + ((2 : ℂ) + I * (t : ℂ)))) := by
  rw [localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge_eq
    A hw m t]
  rw [rightEdgeGaussianFactor_eq_localizedGaussianWeight_mul]
  ring

/--
The measurable two-variable kernel obtained after expanding the Mellin
transform on the right edge. Complex powers of the positive real variable
are written as exponentials so measurability is explicit.
-/
def rightEdgeMellinProduct
    (A : ℂ[X]) (m : ℝ) (w : ℂ)
    (p : ℝ × ℝ) : ℂ :=
  rightEdgeGaussianFactor A m w p.1 *
    psiErrorAboveOneComplex p.2 *
    Complex.exp
      (((Real.log p.2 : ℝ) : ℂ) *
        (-(w + ((2 : ℂ) + I * (p.1 : ℂ)) + 1)))

/--
The expanded right-edge Mellin kernel is absolutely integrable on
`ℝ × (1, ∞)`. This is the Tonelli-Fubini input for the concrete zeta
right-edge transform.
-/
theorem integrable_rightEdgeMellinProduct
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : 0 < w.re) :
    Integrable
      (rightEdgeMellinProduct A m w)
      (volume.prod (volume.restrict (Set.Ioi (1 : ℝ)))) := by
  let s0 : ℂ := ((w.re + 2 : ℝ) : ℂ)
  let P : ℝ → ℂ := rightEdgeGaussianFactor A m w
  let Q : ℝ → ℂ := fun x =>
    psiErrorAboveOneComplex x *
      Complex.exp
        (((Real.log x : ℝ) : ℂ) * (-(s0 + 1)))
  have hP : Integrable P := by
    dsimp [P, rightEdgeGaussianFactor]
    convert
      integrable_verticalPolynomialGaussian_add_mul
        A hm w 2 (16 * m) using 1 <;>
      push_cast
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hQcpow :=
    integrableOn_psiErrorAboveOneComplex_mul_cpow hs0
  have hQ :
      Integrable Q (volume.restrict (Set.Ioi (1 : ℝ))) := by
    refine hQcpow.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := zero_lt_one.trans hx
    dsimp [Q]
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr hxpos.ne')]
    rw [Complex.ofReal_log hxpos.le]
  have hproductMeasurable :
      AEStronglyMeasurable
        (rightEdgeMellinProduct A m w)
        (volume.prod (volume.restrict (Set.Ioi (1 : ℝ)))) := by
    have hPsi :
        AEStronglyMeasurable psiErrorAboveOneComplex
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
      exact
        locallyIntegrableOn_psiErrorAboveOneComplex.aestronglyMeasurable.mono_measure
          (Measure.restrict_mono
            (Set.Ioi_subset_Ioi
              (show (0 : ℝ) ≤ 1 by norm_num))
            le_rfl)
    have hphase :
        AEStronglyMeasurable
          (fun p : ℝ × ℝ =>
            Complex.exp
              (((Real.log p.2 : ℝ) : ℂ) *
                (-(w + ((2 : ℂ) + I * (p.1 : ℂ)) + 1))))
          (volume.prod (volume.restrict (Set.Ioi (1 : ℝ)))) := by
      exact (by fun_prop : Measurable
        (fun p : ℝ × ℝ =>
          Complex.exp
            (((Real.log p.2 : ℝ) : ℂ) *
              (-(w + ((2 : ℂ) + I * (p.1 : ℂ)) + 1))))).aestronglyMeasurable
    exact
      ((hP.aestronglyMeasurable.comp_fst.mul hPsi.comp_snd).mul
        hphase)
  have hdom :
      Integrable
        (fun p : ℝ × ℝ => ‖P p.1‖ * ‖Q p.2‖)
        (volume.prod (volume.restrict (Set.Ioi (1 : ℝ)))) :=
    hP.norm.mul_prod hQ.norm
  refine hdom.mono' hproductMeasurable ?_
  filter_upwards with p
  dsimp [rightEdgeMellinProduct, P, Q]
  simp only [norm_mul]
  congr 2
  rw [Complex.norm_exp, Complex.norm_exp]
  dsimp [s0]
  norm_num [Complex.mul_re, Complex.add_re]
  rw [mul_assoc]

/--
The fixed-`x` right-edge transform in the exponential form used by the
measurable product kernel.
-/
theorem integral_rightEdgeGaussianFactor_exp_eq
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        rightEdgeGaussianFactor A m w t *
          Complex.exp
            (((Real.log x : ℝ) : ℂ) *
              (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) =
      (2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (16 * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (16 * m - Real.log x))) := by
  calc
    (∫ t : ℝ,
        rightEdgeGaussianFactor A m w t *
          Complex.exp
            (((Real.log x : ℝ) : ℂ) *
              (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) =
        ∫ t : ℝ,
          rightEdgeGaussianFactor A m w t *
            (x : ℂ) ^
              (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)) := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr hx.ne')]
      rw [Complex.ofReal_log hx.le]
    _ = _ := by
      simpa [rightEdgeGaussianFactor] using
        integral_rightEdgePolynomialGaussian_cpow_eq
          A hm w hx

/--
Integrating the product kernel first in the Chebyshev variable recovers
the Mellin transform on the right edge.
-/
theorem integral_rightEdgeMellinProduct_snd_eq
    (A : ℂ[X]) (m : ℝ) {w : ℂ} (t : ℝ) :
    (∫ x in Set.Ioi (1 : ℝ),
        rightEdgeMellinProduct A m w (t, x)) =
      rightEdgeGaussianFactor A m w t *
        mellin psiErrorAboveOneComplex
          (-(w + ((2 : ℂ) + I * (t : ℂ)))) := by
  rw [mellin_psiErrorAboveOneComplex_neg_eq_integral]
  rw [show
      (fun x : ℝ =>
        rightEdgeMellinProduct A m w (t, x)) =
        fun x : ℝ =>
          rightEdgeGaussianFactor A m w t *
            (psiErrorAboveOneComplex x *
              Complex.exp
                (((Real.log x : ℝ) : ℂ) *
                  (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) by
    funext x
    unfold rightEdgeMellinProduct
    ring]
  calc
    (∫ x in Set.Ioi (1 : ℝ),
        rightEdgeGaussianFactor A m w t *
          (psiErrorAboveOneComplex x *
            Complex.exp
              (((Real.log x : ℝ) : ℂ) *
                (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))))) =
        rightEdgeGaussianFactor A m w t *
          (∫ x in Set.Ioi (1 : ℝ),
            psiErrorAboveOneComplex x *
              Complex.exp
                (((Real.log x : ℝ) : ℂ) *
                  (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) :=
      integral_const_mul _ _
    _ = rightEdgeGaussianFactor A m w t *
          (∫ x in Set.Ioi (1 : ℝ),
            ((chebyshevPsi x - x : ℝ) : ℂ) *
              (x : ℂ) ^
                (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))) := by
      congr 1
      apply integral_congr_ae
      refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro x hx
      have hxpos : 0 < x := zero_lt_one.trans hx
      have hxone : (1 : ℝ) ≤ x := le_of_lt hx
      change
        psiErrorAboveOneComplex x *
            Complex.exp
              (((Real.log x : ℝ) : ℂ) *
                (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))) =
          ((chebyshevPsi x - x : ℝ) : ℂ) *
            (x : ℂ) ^
              (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr hxpos.ne')]
      rw [Complex.ofReal_log hxpos.le]
      simp [psiErrorAboveOneComplex, psiErrorAboveOne,
        hxone]

/--
Integrating the product kernel first on the right edge produces the
Gaussian inverse kernel and its derivative.
-/
theorem integral_rightEdgeMellinProduct_fst_eq
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        rightEdgeMellinProduct A m w (t, x)) =
      psiErrorAboveOneComplex x *
        ((2 * Real.pi : ℂ) *
          ((x : ℂ) ^ (-(w + 1)) *
            (w * polynomialGaussianKernel A m
                (16 * m - Real.log x) +
              polynomialGaussianKernelDeriv A m
                (16 * m - Real.log x)))) := by
  rw [show
      (fun t : ℝ =>
        rightEdgeMellinProduct A m w (t, x)) =
        fun t : ℝ =>
          psiErrorAboveOneComplex x *
            (rightEdgeGaussianFactor A m w t *
              Complex.exp
                (((Real.log x : ℝ) : ℂ) *
                  (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) by
    funext t
    unfold rightEdgeMellinProduct
    ring]
  calc
    (∫ t : ℝ,
        psiErrorAboveOneComplex x *
          (rightEdgeGaussianFactor A m w t *
            Complex.exp
              (((Real.log x : ℝ) : ℂ) *
                (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))))) =
        psiErrorAboveOneComplex x *
          (∫ t : ℝ,
            rightEdgeGaussianFactor A m w t *
              Complex.exp
                (((Real.log x : ℝ) : ℂ) *
                  (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) :=
      integral_const_mul _ _
    _ = _ := by
      rw [integral_rightEdgeGaussianFactor_exp_eq A hm w hx]

/--
Fubini's theorem identifies the infinite right-edge zeta/Mellin integral
with the Gaussian average of the Chebyshev error.
-/
theorem integral_rightEdgeGaussianFactor_mul_mellin_eq
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : 0 < w.re) :
    (∫ t : ℝ,
        rightEdgeGaussianFactor A m w t *
          mellin psiErrorAboveOneComplex
            (-(w + ((2 : ℂ) + I * (t : ℂ))))) =
      ∫ x in Set.Ioi (1 : ℝ),
        psiErrorAboveOneComplex x *
          ((2 * Real.pi : ℂ) *
            ((x : ℂ) ^ (-(w + 1)) *
              (w * polynomialGaussianKernel A m
                  (16 * m - Real.log x) +
                polynomialGaussianKernelDeriv A m
                  (16 * m - Real.log x)))) := by
  have hproduct :=
    integrable_rightEdgeMellinProduct A hm hw
  calc
    (∫ t : ℝ,
        rightEdgeGaussianFactor A m w t *
          mellin psiErrorAboveOneComplex
            (-(w + ((2 : ℂ) + I * (t : ℂ))))) =
        ∫ t : ℝ, ∫ x in Set.Ioi (1 : ℝ),
          rightEdgeMellinProduct A m w (t, x) := by
      apply integral_congr_ae
      filter_upwards with t
      exact (integral_rightEdgeMellinProduct_snd_eq
        A m t).symm
    _ =
        ∫ x in Set.Ioi (1 : ℝ), ∫ t : ℝ,
          rightEdgeMellinProduct A m w (t, x) := by
      exact integral_integral_swap hproduct
    _ = _ := by
      apply integral_congr_ae
      refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro x hx
      exact integral_rightEdgeMellinProduct_fst_eq
        A hm w (zero_lt_one.trans hx)

/--
The full concrete zeta integral on the infinite right edge is exactly the
Gaussian average of the Chebyshev error.  The pole at `s = 1` has already
been removed in the regularized logarithmic derivative.
-/
theorem integral_localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge_eq
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : 0 < w.re) :
    (∫ t : ℝ,
        localizedGaussianWeight A w m
            (w + ((2 : ℂ) + I * (t : ℂ))) *
          (-logDeriv riemannZeta
              (w + ((2 : ℂ) + I * (t : ℂ))) -
            (w + ((2 : ℂ) + I * (t : ℂ))) /
              (w + ((2 : ℂ) + I * (t : ℂ)) - 1))) =
      ∫ x in Set.Ioi (1 : ℝ),
        psiErrorAboveOneComplex x *
          ((2 * Real.pi : ℂ) *
            ((x : ℂ) ^ (-(w + 1)) *
              (w * polynomialGaussianKernel A m
                  (16 * m - Real.log x) +
                polynomialGaussianKernelDeriv A m
                  (16 * m - Real.log x)))) := by
  calc
    (∫ t : ℝ,
        localizedGaussianWeight A w m
            (w + ((2 : ℂ) + I * (t : ℂ))) *
          (-logDeriv riemannZeta
              (w + ((2 : ℂ) + I * (t : ℂ))) -
            (w + ((2 : ℂ) + I * (t : ℂ))) /
              (w + ((2 : ℂ) + I * (t : ℂ)) - 1))) =
        ∫ t : ℝ,
          rightEdgeGaussianFactor A m w t *
            mellin psiErrorAboveOneComplex
              (-(w + ((2 : ℂ) + I * (t : ℂ)))) := by
      apply integral_congr_ae
      filter_upwards with t
      exact
        localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge_eq_factor
          A hw m t
    _ = _ :=
      integral_rightEdgeGaussianFactor_mul_mellin_eq A hm hw

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
