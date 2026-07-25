import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import PrimeNumberTheorem.VKEdgePiOverTwoPolynomialGaussian

open Complex MeasureTheory Polynomial
open scoped FourierTransform

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

private theorem contDiff_normalizedGaussian_top
    {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ⊤ (normalizedGaussian m) := by
  unfold normalizedGaussian
  fun_prop

private theorem iteratedDeriv_ofReal
    {g : ℝ → ℝ} (hsmooth : ContDiff ℝ ⊤ g) (k : ℕ) :
    iteratedDeriv k
        (fun r : ℝ => (g r : ℂ)) =
      fun r : ℝ =>
        ((iteratedDeriv k g r : ℝ) : ℂ) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show k + 1 = Nat.succ k by omega]
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext r
      have hdifferentiableAt :
          DifferentiableAt ℝ (iteratedDeriv k g) r :=
        (hsmooth.differentiable_iteratedDeriv k (by simp)).differentiableAt
      have hreal :
          HasDerivAt (iteratedDeriv k g)
            (deriv (iteratedDeriv k g) r) r :=
        hdifferentiableAt.hasDerivAt
      exact hreal.ofReal_comp.deriv

private theorem integrable_pow_smul_complexGaussian
    {m : ℝ} (hm : 0 < m) (k : ℕ) :
    Integrable
      (fun t : ℝ =>
        t ^ k • Complex.exp (-(m : ℂ) * (t : ℂ) ^ 2)) := by
  have hreal :
      Integrable
        (fun t : ℝ =>
          t ^ (k : ℝ) * Real.exp (-m * t ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hm
      (show (-1 : ℝ) < (k : ℝ) by
        exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k))
  have hcast :
      Integrable
        (fun t : ℝ =>
          ((t ^ (k : ℝ) * Real.exp (-m * t ^ 2) : ℝ) : ℂ)) :=
    hreal.ofReal
  convert hcast using 1
  funext t
  rw [Real.rpow_natCast]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_exp, Complex.ofReal_neg]
  push_cast
  simp only [Complex.real_smul, Complex.ofReal_pow]

private theorem fourier_complexGaussian_eq
    {m : ℝ} (hm : 0 < m) :
    𝓕 (fun t : ℝ =>
        Complex.exp (-(m : ℂ) * (t : ℂ) ^ 2)) =
      fun w : ℝ =>
        (2 * Real.pi : ℂ) *
          (normalizedGaussian m (-2 * Real.pi * w) : ℂ) := by
  funext w
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_verticalGaussian_eq hm 0 (-2 * Real.pi * w)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/--
The `k`-th vertical Gaussian moment is the `k`-th derivative of the
normalized inverse Gaussian. This is the monomial core of the
polynomial-weighted Gaussian--Mellin transform.
-/
theorem integral_verticalGaussian_monomial_zero_eq
    {m : ℝ} (hm : 0 < m) (k : ℕ) (r : ℝ) :
    (∫ t : ℝ,
        (I * (t : ℂ)) ^ k *
          Complex.exp
            ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
              (r : ℂ) * (I * (t : ℂ)))) =
      (2 * Real.pi : ℂ) *
        ((iteratedDeriv k (normalizedGaussian m) r : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp (-(m : ℂ) * (t : ℂ) ^ 2)
  let w : ℝ := -r / (2 * Real.pi)
  have hmoment :
      ∀ n : ℕ, (n : ℕ∞) ≤ ⊤ →
        Integrable (fun t : ℝ => t ^ n • f t) := by
    intro n _
    exact integrable_pow_smul_complexGaussian hm n
  have hderivFourier :=
    congrFun
      (Real.iteratedDeriv_fourier hmoment
        (show (k : ℕ∞) ≤ ⊤ by simp)) w
  have hfourier :
      𝓕 f =
        fun q : ℝ =>
          (2 * Real.pi : ℂ) *
            (normalizedGaussian m (-2 * Real.pi * q) : ℂ) := by
    exact fourier_complexGaussian_eq hm
  rw [hfourier] at hderivFourier
  rw [Real.fourier_real_eq_integral_exp_smul] at hderivFourier
  let g : ℝ → ℝ := fun q =>
    normalizedGaussian m (-2 * Real.pi * q)
  have hgSmooth : ContDiff ℝ ⊤ g := by
    dsimp [g]
    exact
      (contDiff_normalizedGaussian_top hm).comp
        (by fun_prop)
  have hcastDeriv :
      iteratedDeriv k
          (fun q : ℝ =>
            (normalizedGaussian m (-2 * Real.pi * q) : ℂ)) =
        fun q : ℝ =>
          ((iteratedDeriv k
              (fun q : ℝ =>
                normalizedGaussian m (-2 * Real.pi * q)) q : ℝ) : ℂ) := by
    simpa [g] using iteratedDeriv_ofReal hgSmooth k
  have hconstDeriv :
      iteratedDeriv k
          (fun q : ℝ =>
            (2 * Real.pi : ℂ) *
              (normalizedGaussian m (-2 * Real.pi * q) : ℂ)) =
        fun q : ℝ =>
          (2 * Real.pi : ℂ) *
            iteratedDeriv k
              (fun q : ℝ =>
                (normalizedGaussian m (-2 * Real.pi * q) : ℂ)) q := by
    funext q
    exact
      iteratedDeriv_const_mul_field
        (2 * Real.pi : ℂ)
        (fun q : ℝ =>
          (normalizedGaussian m (-2 * Real.pi * q) : ℂ))
  rw [hconstDeriv, hcastDeriv] at hderivFourier
  have hscaled :
      iteratedDeriv k
          (fun q : ℝ =>
            normalizedGaussian m (-2 * Real.pi * q)) w =
        (-2 * Real.pi) ^ k *
          iteratedDeriv k (normalizedGaussian m)
            (-2 * Real.pi * w) := by
    exact
      congrFun
        (iteratedDeriv_comp_const_mul
          (n := k) (f := normalizedGaussian m)
          ((contDiff_normalizedGaussian_top hm).of_le (by simp))
          (-2 * Real.pi)) w
  simp only at hderivFourier
  rw [hscaled] at hderivFourier
  have hw : -2 * Real.pi * w = r := by
    dsimp [w]
    field_simp [Real.pi_ne_zero]
  rw [hw] at hderivFourier
  have hfactor : ((-2 * Real.pi : ℝ) : ℂ) ^ k ≠ 0 := by
    exact pow_ne_zero _ (by
      exact_mod_cast
        (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) Real.pi_ne_zero))
  apply (mul_left_cancel₀ hfactor)
  calc
    ((-2 * Real.pi : ℝ) : ℂ) ^ k *
          (∫ t : ℝ,
            (I * (t : ℂ)) ^ k *
              Complex.exp
                ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
                  (r : ℂ) * (I * (t : ℂ)))) =
        ∫ t : ℝ,
          ((-2 * Real.pi : ℝ) : ℂ) ^ k *
            ((I * (t : ℂ)) ^ k *
              Complex.exp
                ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
                  (r : ℂ) * (I * (t : ℂ)))) := by
        exact (integral_const_mul _ _).symm
    _ =
        ∫ t : ℝ,
          Complex.exp
              (((-(2 * Real.pi * t * w) : ℝ) : ℂ) * I) *
            (((-2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)) ^ k *
              f t := by
        apply integral_congr_ae
        filter_upwards with t
        have hexp :
            Complex.exp
                ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
                  (r : ℂ) * (I * (t : ℂ))) =
              Complex.exp
                  (((-(2 * Real.pi * t * w) : ℝ) : ℂ) * I) *
                f t := by
          dsimp [f]
          rw [← Complex.exp_add]
          congr 1
          rw [← hw]
          push_cast
          ring_nf
          rw [I_sq]
          ring
        rw [hexp]
        push_cast
        ring
    _ =
        (2 * Real.pi : ℂ) *
          ((((-2 * Real.pi : ℝ) ^ k *
            iteratedDeriv k (normalizedGaussian m) r : ℝ)) : ℂ) := by
        convert hderivFourier.symm using 1
        apply integral_congr_ae
        filter_upwards with t
        simp only [smul_eq_mul]
        push_cast
        ring
    _ = ((-2 * Real.pi : ℝ) : ℂ) ^ k *
          ((2 * Real.pi : ℂ) *
            ((iteratedDeriv k (normalizedGaussian m) r : ℝ) : ℂ)) := by
        push_cast
        ring
    _ = ((-2 * Real.pi : ℝ) : ℂ) ^ k *
          ((2 * Real.pi : ℂ) *
            ((iteratedDeriv k (normalizedGaussian m) r : ℝ) : ℂ)) := rfl

private theorem integrable_verticalGaussian_monomial_zero
    {m : ℝ} (hm : 0 < m) (k : ℕ) (r : ℝ) :
    Integrable
      (fun t : ℝ =>
        (I * (t : ℂ)) ^ k *
          Complex.exp
            ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
              (r : ℂ) * (I * (t : ℂ)))) := by
  have hbase0 := integrable_pow_smul_complexGaussian hm k
  have hbase :
      Integrable
        (fun t : ℝ =>
          (I * (t : ℂ)) ^ k *
            Complex.exp (-(m : ℂ) * (t : ℂ) ^ 2)) := by
    convert hbase0.const_mul (I ^ k) using 1
    funext t
    rw [Complex.real_smul]
    push_cast
    ring
  let phase : ℝ → ℂ := fun t =>
    Complex.exp ((r : ℂ) * (I * (t : ℂ)))
  have hphaseMeasurable : AEStronglyMeasurable phase := by
    exact (by fun_prop : Continuous phase).aestronglyMeasurable
  have hphaseNorm : ∀ᵐ t : ℝ, ‖phase t‖ ≤ (1 : ℝ) := by
    filter_upwards with t
    dsimp [phase]
    rw [Complex.norm_exp]
    simp
  have hproduct :=
    hbase.mul_bdd hphaseMeasurable hphaseNorm
  convert hproduct using 1
  funext t
  dsimp [phase]
  have hexp :
      Complex.exp
          ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
            (r : ℂ) * (I * (t : ℂ))) =
        Complex.exp (-(m : ℂ) * (t : ℂ) ^ 2) *
          Complex.exp ((r : ℂ) * (I * (t : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [hexp]
  ring

/--
On the central vertical line, a fixed polynomial multiplier becomes the
same polynomial in the real derivative operator applied to the normalized
inverse Gaussian.
-/
theorem integral_verticalPolynomialGaussian_zero_eq
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m) (r : ℝ) :
    (∫ t : ℝ,
        A.eval (I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
              (r : ℂ) * (I * (t : ℂ)))) =
      (2 * Real.pi : ℂ) * polynomialGaussianKernel A m r := by
  classical
  have hintegrable :
      ∀ k ∈ A.support,
        Integrable
          (fun t : ℝ =>
            A.coeff k *
              ((I * (t : ℂ)) ^ k *
                Complex.exp
                  ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
                    (r : ℂ) * (I * (t : ℂ))))) := by
    intro k _
    exact
      (integrable_verticalGaussian_monomial_zero hm k r).const_mul _
  rw [show
      (fun t : ℝ =>
        A.eval (I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
              (r : ℂ) * (I * (t : ℂ)))) =
        fun t : ℝ =>
          ∑ k ∈ A.support,
            A.coeff k *
              ((I * (t : ℂ)) ^ k *
                Complex.exp
                  ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
                    (r : ℂ) * (I * (t : ℂ)))) by
    funext t
    rw [A.eval_eq_sum]
    simp only [Polynomial.sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring]
  rw [integral_finset_sum A.support hintegrable]
  unfold polynomialGaussianKernel Polynomial.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (∫ a : ℝ,
        A.coeff k *
          ((I * (a : ℂ)) ^ k *
            Complex.exp
              ((m : ℂ) * (I * (a : ℂ)) ^ 2 +
                (r : ℂ) * (I * (a : ℂ))))) =
        A.coeff k *
          (∫ a : ℝ,
            (I * (a : ℂ)) ^ k *
              Complex.exp
                ((m : ℂ) * (I * (a : ℂ)) ^ 2 +
                  (r : ℂ) * (I * (a : ℂ)))) :=
      integral_const_mul _ _
    _ = A.coeff k *
          ((2 * Real.pi : ℂ) *
            ((iteratedDeriv k
              (normalizedGaussian m) r : ℝ) : ℂ)) := by
        rw [integral_verticalGaussian_monomial_zero_eq hm k r]
    _ = (2 * Real.pi : ℂ) *
          (A.coeff k *
            ((iteratedDeriv k
              (normalizedGaussian m) r : ℝ) : ℂ)) := by
        ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
