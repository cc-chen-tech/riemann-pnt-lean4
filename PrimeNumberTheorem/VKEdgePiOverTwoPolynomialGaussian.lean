import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import PrimeNumberTheorem.VKEdgePiOverTwoGaussianMean

open Filter MeasureTheory Polynomial

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The Gaussian kernel obtained by applying a fixed polynomial in the
derivative operator. -/
def polynomialGaussianKernel (A : ℂ[X]) (m t : ℝ) : ℂ :=
  A.sum fun k a =>
    a * ((iteratedDeriv k (normalizedGaussian m) t : ℝ) : ℂ)

/-- The termwise derivative of `polynomialGaussianKernel`. -/
def polynomialGaussianKernelDeriv (A : ℂ[X]) (m t : ℝ) : ℂ :=
  A.sum fun k a =>
    a *
      ((iteratedDeriv (k + 1) (normalizedGaussian m) t : ℝ) : ℂ)

/-- The Hermite-type polynomial multiplying the standard Gaussian after
`k` derivatives. -/
private def gaussianDerivativePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | k + 1 =>
      (gaussianDerivativePolynomial k).derivative -
        C (1 / 2 : ℝ) * X * gaussianDerivativePolynomial k

private theorem iteratedDeriv_normalizedGaussian_one
    (k : ℕ) (t : ℝ) :
    iteratedDeriv k (normalizedGaussian 1) t =
      (gaussianDerivativePolynomial k).eval t *
        normalizedGaussian 1 t := by
  induction k generalizing t with
  | zero =>
      simp [gaussianDerivativePolynomial]
  | succ k ih =>
      rw [show k + 1 = Nat.succ k by omega, iteratedDeriv_succ]
      have hfun :
          iteratedDeriv k (normalizedGaussian 1) =
            fun x =>
              (gaussianDerivativePolynomial k).eval x *
                normalizedGaussian 1 x := by
        funext x
        exact ih x
      rw [hfun]
      have hderiv :=
        ((gaussianDerivativePolynomial k).hasDerivAt t).mul
          (hasDerivAt_normalizedGaussian
            (show (0 : ℝ) < 1 by norm_num) t)
      rw [show
          deriv
              (fun x =>
                (gaussianDerivativePolynomial k).eval x *
                  normalizedGaussian 1 x) t =
            (gaussianDerivativePolynomial k).derivative.eval t *
                normalizedGaussian 1 t +
              (gaussianDerivativePolynomial k).eval t *
                normalizedGaussianDeriv 1 t by
        simpa only [Pi.mul_apply] using hderiv.deriv]
      simp only [gaussianDerivativePolynomial, eval_sub, eval_mul, eval_C,
        eval_X, normalizedGaussianDeriv]
      ring

private theorem integrable_pow_mul_normalizedGaussian_one (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k * normalizedGaussian 1 t) := by
  have hbase :
      Integrable
        (fun t : ℝ =>
          t ^ (k : ℝ) * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) := by
    exact integrable_rpow_mul_exp_neg_mul_sq
      (show (0 : ℝ) < 1 / 4 by norm_num)
      (show (-1 : ℝ) < (k : ℝ) by
        exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k))
  have hscaled := hbase.div_const (2 * Real.sqrt Real.pi)
  apply hscaled.congr
  filter_upwards with t
  rw [Real.rpow_natCast]
  simp only [normalizedGaussian]
  norm_num
  ring

private theorem integrable_polynomial_mul_normalizedGaussian_one
    (p : ℝ[X]) :
    Integrable (fun t : ℝ => p.eval t * normalizedGaussian 1 t) := by
  rw [show (fun t : ℝ => p.eval t * normalizedGaussian 1 t) =
      fun t : ℝ =>
        ∑ k ∈ p.support,
          p.coeff k * (t ^ k * normalizedGaussian 1 t) by
    funext t
    rw [p.eval_eq_sum]
    simp only [Polynomial.sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring]
  exact integrable_finset_sum p.support fun k _ =>
    (integrable_pow_mul_normalizedGaussian_one k).const_mul _

private theorem integrable_iteratedDeriv_normalizedGaussian_one (k : ℕ) :
    Integrable (iteratedDeriv k (normalizedGaussian 1)) := by
  convert
    integrable_polynomial_mul_normalizedGaussian_one
      (gaussianDerivativePolynomial k) using 1
  funext t
  exact iteratedDeriv_normalizedGaussian_one k t

private theorem contDiff_normalizedGaussian_one (k : ℕ) :
    ContDiff ℝ k (normalizedGaussian 1) := by
  unfold normalizedGaussian
  fun_prop

private theorem normalizedGaussian_eq_scaled
    {m : ℝ} (hm : 0 < m) :
    normalizedGaussian m =
      fun t =>
        (Real.sqrt m)⁻¹ *
          normalizedGaussian 1 ((Real.sqrt m)⁻¹ * t) := by
  funext t
  have hsqrtPos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsqrtNe : Real.sqrt m ≠ 0 := hsqrtPos.ne'
  have hsqrtSq : (Real.sqrt m) ^ 2 = m :=
    Real.sq_sqrt hm.le
  have hsqrtPiMul :
      Real.sqrt (Real.pi * m) =
        Real.sqrt Real.pi * Real.sqrt m := by
    rw [Real.sqrt_mul Real.pi_pos.le]
  unfold normalizedGaussian
  rw [hsqrtPiMul]
  have hexponent :
      -t ^ 2 / (4 * m) =
        -((Real.sqrt m)⁻¹ * t) ^ 2 / (4 * 1) := by
    field_simp [hsqrtNe]
    nlinarith [hsqrtSq]
  rw [hexponent]
  field_simp [hsqrtNe, Real.sqrt_ne_zero'.mpr Real.pi_pos]

private theorem iteratedDeriv_normalizedGaussian_eq_scaled
    {m : ℝ} (hm : 0 < m) (k : ℕ) :
    iteratedDeriv k (normalizedGaussian m) =
      fun t =>
        (Real.sqrt m)⁻¹ ^ (k + 1) *
          iteratedDeriv k (normalizedGaussian 1)
            ((Real.sqrt m)⁻¹ * t) := by
  rw [normalizedGaussian_eq_scaled hm]
  funext t
  rw [iteratedDeriv_const_mul_field]
  rw [show
      iteratedDeriv k
          (fun t => normalizedGaussian 1 ((Real.sqrt m)⁻¹ * t)) =
        fun t =>
          (Real.sqrt m)⁻¹ ^ k *
            iteratedDeriv k (normalizedGaussian 1)
              ((Real.sqrt m)⁻¹ * t) by
    exact iteratedDeriv_comp_const_mul
      (contDiff_normalizedGaussian_one k) (Real.sqrt m)⁻¹]
  rw [pow_succ]
  ring

/-- The absolute Hermite moment controlling the `k`-th derivative of the
standard normalized Gaussian. -/
def gaussianDerivativeL1 (k : ℕ) : ℝ :=
  ∫ t : ℝ, |iteratedDeriv k (normalizedGaussian 1) t|

theorem gaussianDerivativeL1_nonneg (k : ℕ) :
    0 ≤ gaussianDerivativeL1 k := by
  exact integral_nonneg fun _ => abs_nonneg _

theorem integral_abs_iteratedDeriv_normalizedGaussian
    {m : ℝ} (hm : 0 < m) (k : ℕ) :
    (∫ t : ℝ, |iteratedDeriv k (normalizedGaussian m) t|) =
      (Real.sqrt m)⁻¹ ^ k * gaussianDerivativeL1 k := by
  have hsqrtPos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsqrtNe : Real.sqrt m ≠ 0 := hsqrtPos.ne'
  rw [iteratedDeriv_normalizedGaussian_eq_scaled hm k]
  simp only [abs_mul, abs_pow, abs_inv, abs_of_pos hsqrtPos]
  rw [MeasureTheory.integral_const_mul]
  have harg :
      (fun a : ℝ =>
        |iteratedDeriv k (normalizedGaussian 1)
          ((Real.sqrt m)⁻¹ * a)|) =
        fun a : ℝ =>
          |iteratedDeriv k (normalizedGaussian 1)
            (a / Real.sqrt m)| := by
    funext a
    congr 2
    simp [div_eq_mul_inv, mul_comm]
  rw [harg,
    Measure.integral_comp_div
      (fun y : ℝ =>
        |iteratedDeriv k (normalizedGaussian 1) y|)
      (Real.sqrt m)]
  simp only [abs_of_pos hsqrtPos, smul_eq_mul]
  unfold gaussianDerivativeL1
  rw [pow_succ]
  field_simp [hsqrtNe]

private theorem integrable_iteratedDeriv_normalizedGaussian
    {m : ℝ} (hm : 0 < m) (k : ℕ) :
    Integrable (iteratedDeriv k (normalizedGaussian m)) := by
  rw [iteratedDeriv_normalizedGaussian_eq_scaled hm k]
  exact
    ((integrable_iteratedDeriv_normalizedGaussian_one k).comp_mul_left'
      (inv_ne_zero (Real.sqrt_ne_zero'.mpr hm))).const_mul _

private theorem integrable_complex_iteratedDeriv_term
    {m : ℝ} (hm : 0 < m) (a : ℂ) (k : ℕ) :
    Integrable
      (fun t : ℝ =>
        a * ((iteratedDeriv k (normalizedGaussian m) t : ℝ) : ℂ)) :=
  ((integrable_iteratedDeriv_normalizedGaussian hm k).ofReal).const_mul a

private theorem integral_norm_iteratedDeriv_sum_le
    (s : Finset ℕ) (a : ℕ → ℂ) (d : ℕ → ℕ)
    {m : ℝ} (hm : 0 < m) :
    (∫ t : ℝ,
        ‖∑ k ∈ s,
          a k *
            ((iteratedDeriv (d k)
              (normalizedGaussian m) t : ℝ) : ℂ)‖) ≤
      ∑ k ∈ s,
        ‖a k‖ *
          ((Real.sqrt m)⁻¹ ^ (d k) * gaussianDerivativeL1 (d k)) := by
  let term : ℕ → ℝ → ℂ := fun k t =>
    a k *
      ((iteratedDeriv (d k) (normalizedGaussian m) t : ℝ) : ℂ)
  have htermInt :
      ∀ k ∈ s, Integrable (term k) := by
    intro k _
    exact integrable_complex_iteratedDeriv_term hm (a k) (d k)
  have hnormSumInt :
      Integrable (fun t : ℝ => ‖∑ k ∈ s, term k t‖) :=
    (integrable_finset_sum s htermInt).norm
  have hsumNormInt :
      Integrable (fun t : ℝ => ∑ k ∈ s, ‖term k t‖) :=
    integrable_finset_sum s fun k hk => (htermInt k hk).norm
  calc
    (∫ t : ℝ, ‖∑ k ∈ s, term k t‖) ≤
        ∫ t : ℝ, ∑ k ∈ s, ‖term k t‖ := by
          exact integral_mono hnormSumInt hsumNormInt fun t =>
            norm_sum_le _ _
    _ = ∑ k ∈ s, ∫ t : ℝ, ‖term k t‖ := by
          rw [integral_finset_sum s fun k hk => (htermInt k hk).norm]
    _ = ∑ k ∈ s,
        ‖a k‖ *
          ((Real.sqrt m)⁻¹ ^ (d k) * gaussianDerivativeL1 (d k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [term, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          rw [integral_const_mul,
            integral_abs_iteratedDeriv_normalizedGaussian hm (d k)]

private theorem inv_sqrt_pow_le_inv_sqrt
    {m : ℝ} (hm : 1 ≤ m) {k : ℕ} (hk : k ≠ 0) :
    (Real.sqrt m)⁻¹ ^ k ≤ (Real.sqrt m)⁻¹ := by
  have hsqrtOne : 1 ≤ Real.sqrt m := by
    simpa using Real.sqrt_le_sqrt hm
  have hinvNonneg : 0 ≤ (Real.sqrt m)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg m)
  have hinvLeOne : (Real.sqrt m)⁻¹ ≤ 1 := by
    exact
      (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hsqrtOne)).2 hsqrtOne
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ]
  exact mul_le_of_le_one_left hinvNonneg (pow_le_one₀ hinvNonneg hinvLeOne)

private theorem integral_norm_iteratedDeriv_sum_le_inv_sqrt
    (s : Finset ℕ) (a : ℕ → ℂ) (d : ℕ → ℕ)
    (hzero : ∀ k ∈ s, d k ≠ 0)
    {m : ℝ} (hm : 1 ≤ m) :
    (∫ t : ℝ,
        ‖∑ k ∈ s,
          a k *
            ((iteratedDeriv (d k)
              (normalizedGaussian m) t : ℝ) : ℂ)‖) ≤
      (∑ k ∈ s, ‖a k‖ * gaussianDerivativeL1 (d k)) /
        Real.sqrt m := by
  have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  refine (integral_norm_iteratedDeriv_sum_le s a d hmPos).trans ?_
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hmoment := gaussianDerivativeL1_nonneg (d k)
  have hcoeff : 0 ≤ ‖a k‖ := norm_nonneg _
  calc
    ‖a k‖ *
          ((Real.sqrt m)⁻¹ ^ (d k) * gaussianDerivativeL1 (d k)) =
        (‖a k‖ * gaussianDerivativeL1 (d k)) *
          (Real.sqrt m)⁻¹ ^ (d k) := by ring
    _ ≤ (‖a k‖ * gaussianDerivativeL1 (d k)) *
          (Real.sqrt m)⁻¹ := by
        exact mul_le_mul_of_nonneg_left
          (inv_sqrt_pow_le_inv_sqrt hm (hzero k hk))
          (mul_nonneg hcoeff hmoment)

private def gaussianDerivativeExpBound (k : ℕ) : ℝ :=
  ∑ j ∈ (gaussianDerivativePolynomial k).support,
    |(gaussianDerivativePolynomial k).coeff j| * (j.factorial : ℝ)

private theorem gaussianDerivativeExpBound_nonneg (k : ℕ) :
    0 ≤ gaussianDerivativeExpBound k := by
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

private theorem abs_gaussianDerivativePolynomial_eval_le_exp
    (k : ℕ) (x : ℝ) :
    |(gaussianDerivativePolynomial k).eval x| ≤
      gaussianDerivativeExpBound k * Real.exp |x| := by
  rw [Polynomial.eval_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [gaussianDerivativeExpBound, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul, abs_pow]
  have hfactPos : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hpow :
      |x| ^ j ≤ (j.factorial : ℝ) * Real.exp |x| := by
    simpa [mul_comm] using
      (div_le_iff₀ hfactPos).mp
        (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) j)
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left hpow
      (abs_nonneg ((gaussianDerivativePolynomial k).coeff j))

private theorem iteratedDeriv_normalizedGaussian_eq_polynomial_mul
    {m : ℝ} (hm : 0 < m) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (normalizedGaussian m) t =
      (Real.sqrt m)⁻¹ ^ k *
        (gaussianDerivativePolynomial k).eval
          ((Real.sqrt m)⁻¹ * t) *
        normalizedGaussian m t := by
  rw [iteratedDeriv_normalizedGaussian_eq_scaled hm k]
  dsimp only
  rw [show iteratedDeriv k (normalizedGaussian 1)
        ((Real.sqrt m)⁻¹ * t) =
      (gaussianDerivativePolynomial k).eval
          ((Real.sqrt m)⁻¹ * t) *
        normalizedGaussian 1 ((Real.sqrt m)⁻¹ * t) by
      exact iteratedDeriv_normalizedGaussian_one k _]
  rw [normalizedGaussian_eq_scaled hm]
  ring

private theorem abs_iteratedDeriv_normalizedGaussian_le_exp_abs_mul
    {m : ℝ} (hm : 1 ≤ m) (k : ℕ) (t : ℝ) :
    |iteratedDeriv k (normalizedGaussian m) t| ≤
      gaussianDerivativeExpBound k * Real.exp |t| *
        normalizedGaussian m t := by
  have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hsqrtOne : 1 ≤ Real.sqrt m := by
    simpa using Real.sqrt_le_sqrt hm
  have hinvNonneg : 0 ≤ (Real.sqrt m)⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg m)
  have hinvLeOne : (Real.sqrt m)⁻¹ ≤ 1 :=
    (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hsqrtOne)).2 hsqrtOne
  have hscaledAbs :
      |(Real.sqrt m)⁻¹ * t| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg hinvNonneg]
    nlinarith [abs_nonneg t]
  have hpoly :=
    abs_gaussianDerivativePolynomial_eval_le_exp k
      ((Real.sqrt m)⁻¹ * t)
  have hexp :
      Real.exp |(Real.sqrt m)⁻¹ * t| ≤ Real.exp |t| :=
    Real.exp_le_exp.mpr hscaledAbs
  have hpow :
      (Real.sqrt m)⁻¹ ^ k ≤ 1 := by
    exact pow_le_one₀ hinvNonneg hinvLeOne
  have hgaussianNonneg : 0 ≤ normalizedGaussian m t :=
    (normalizedGaussian_pos hmPos t).le
  have hboundNonneg : 0 ≤ gaussianDerivativeExpBound k :=
    gaussianDerivativeExpBound_nonneg k
  rw [iteratedDeriv_normalizedGaussian_eq_polynomial_mul hmPos,
    abs_mul, abs_mul, abs_pow, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg m),
    abs_of_pos (normalizedGaussian_pos hmPos t)]
  calc
    (Real.sqrt m)⁻¹ ^ k *
          |(gaussianDerivativePolynomial k).eval
            ((Real.sqrt m)⁻¹ * t)| *
          normalizedGaussian m t ≤
        1 *
          (gaussianDerivativeExpBound k *
            Real.exp |(Real.sqrt m)⁻¹ * t|) *
          normalizedGaussian m t := by
      apply mul_le_mul_of_nonneg_right _ hgaussianNonneg
      exact mul_le_mul hpow hpoly (abs_nonneg _) (by norm_num)
    _ ≤ gaussianDerivativeExpBound k * Real.exp |t| *
          normalizedGaussian m t := by
      apply mul_le_mul_of_nonneg_right _ hgaussianNonneg
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_left hexp hboundNonneg

/--
For a fixed polynomial, both its Gaussian kernel and the termwise
derivative satisfy a common pointwise envelope
`C_A exp(|t|) G_m(t)`, uniformly for `m ≥ 1`.

The deliberately loose exponential envelope is strong enough for the
distance-`12m` localization tails and avoids exposing Hermite coefficients
in downstream contour code.
-/
theorem exists_polynomialGaussianKernel_add_deriv_norm_le_exp_abs_mul
    (A : ℂ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℝ, 1 ≤ m → ∀ t : ℝ,
        ‖polynomialGaussianKernel A m t‖ +
            ‖polynomialGaussianKernelDeriv A m t‖ ≤
          C * Real.exp |t| * normalizedGaussian m t := by
  let C_A : ℝ :=
    (∑ k ∈ A.support,
      ‖A.coeff k‖ * gaussianDerivativeExpBound k) +
    ∑ k ∈ A.support,
      ‖A.coeff k‖ * gaussianDerivativeExpBound (k + 1)
  refine ⟨C_A, ?_, ?_⟩
  · dsimp [C_A]
    exact add_nonneg
      (Finset.sum_nonneg fun k _ =>
        mul_nonneg (norm_nonneg _)
          (gaussianDerivativeExpBound_nonneg k))
      (Finset.sum_nonneg fun k _ =>
        mul_nonneg (norm_nonneg _)
          (gaussianDerivativeExpBound_nonneg (k + 1)))
  · intro m hm t
    have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
    have hkernel :
        ‖polynomialGaussianKernel A m t‖ ≤
          (∑ k ∈ A.support,
            ‖A.coeff k‖ * gaussianDerivativeExpBound k) *
            Real.exp |t| * normalizedGaussian m t := by
      unfold polynomialGaussianKernel Polynomial.sum
      calc
        ‖∑ k ∈ A.support,
            A.coeff k *
              ((iteratedDeriv k
                (normalizedGaussian m) t : ℝ) : ℂ)‖ ≤
            ∑ k ∈ A.support,
              ‖A.coeff k *
                ((iteratedDeriv k
                  (normalizedGaussian m) t : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ k ∈ A.support,
              (‖A.coeff k‖ * gaussianDerivativeExpBound k) *
                Real.exp |t| * normalizedGaussian m t := by
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left
              (abs_iteratedDeriv_normalizedGaussian_le_exp_abs_mul
                hm k t)
              (norm_nonneg (A.coeff k))
        _ = _ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hderiv :
        ‖polynomialGaussianKernelDeriv A m t‖ ≤
          (∑ k ∈ A.support,
            ‖A.coeff k‖ * gaussianDerivativeExpBound (k + 1)) *
            Real.exp |t| * normalizedGaussian m t := by
      unfold polynomialGaussianKernelDeriv Polynomial.sum
      calc
        ‖∑ k ∈ A.support,
            A.coeff k *
              ((iteratedDeriv (k + 1)
                (normalizedGaussian m) t : ℝ) : ℂ)‖ ≤
            ∑ k ∈ A.support,
              ‖A.coeff k *
                ((iteratedDeriv (k + 1)
                  (normalizedGaussian m) t : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ k ∈ A.support,
              (‖A.coeff k‖ *
                  gaussianDerivativeExpBound (k + 1)) *
                Real.exp |t| * normalizedGaussian m t := by
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left
              (abs_iteratedDeriv_normalizedGaussian_le_exp_abs_mul
                hm (k + 1) t)
              (norm_nonneg (A.coeff k))
        _ = _ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
    dsimp [C_A]
    linarith

theorem continuous_polynomialGaussianKernel
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m) :
    Continuous (polynomialGaussianKernel A m) := by
  have hsmooth : ContDiff ℝ ⊤ (normalizedGaussian m) := by
    unfold normalizedGaussian
    fun_prop
  unfold polynomialGaussianKernel Polynomial.sum
  apply continuous_finset_sum
  intro k hk
  apply continuous_const.mul
  exact Complex.continuous_ofReal.comp
    (hsmooth.continuous_iteratedDeriv k (by simp))

theorem continuous_polynomialGaussianKernelDeriv
    (A : ℂ[X]) {m : ℝ} (hm : 0 < m) :
    Continuous (polynomialGaussianKernelDeriv A m) := by
  have hsmooth : ContDiff ℝ ⊤ (normalizedGaussian m) := by
    unfold normalizedGaussian
    fun_prop
  unfold polynomialGaussianKernelDeriv Polynomial.sum
  apply continuous_finset_sum
  intro k hk
  apply continuous_const.mul
  exact Complex.continuous_ofReal.comp
    (hsmooth.continuous_iteratedDeriv (k + 1) (by simp))

private theorem polynomialGaussianKernel_sub_eq_sum_erase_zero
    (A : ℂ[X]) (hA : A.eval 0 = 1) (m t : ℝ) :
    polynomialGaussianKernel A m t -
        (normalizedGaussian m t : ℂ) =
      ∑ k ∈ A.support.erase 0,
        A.coeff k *
          ((iteratedDeriv k (normalizedGaussian m) t : ℝ) : ℂ) := by
  have hcoeffZero : A.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]
    exact hA
  have hzeroMem : 0 ∈ A.support := by
    rw [mem_support_iff]
    simp [hcoeffZero]
  unfold polynomialGaussianKernel Polynomial.sum
  rw [← Finset.sum_erase_add _ _ hzeroMem]
  simp [hcoeffZero]

/--
For a fixed polynomial `A` with `A(0)=1`, applying `A(d/dt)` changes the
normalized Gaussian by `O_A(m⁻¹ᐟ²)` in `L¹`, uniformly for `m ≥ 1`.
-/
theorem exists_polynomialGaussianKernel_sub_l1_bound
    (A : ℂ[X]) (hA : A.eval 0 = 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℝ, 1 ≤ m →
        (∫ t : ℝ,
          ‖polynomialGaussianKernel A m t -
            (normalizedGaussian m t : ℂ)‖) ≤
          C / Real.sqrt m := by
  let C_A : ℝ :=
    ∑ k ∈ A.support.erase 0,
      ‖A.coeff k‖ * gaussianDerivativeL1 k
  refine ⟨C_A, ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (gaussianDerivativeL1_nonneg k)
  · intro m hm
    rw [show
        (fun t : ℝ =>
          ‖polynomialGaussianKernel A m t -
            (normalizedGaussian m t : ℂ)‖) =
          fun t : ℝ =>
            ‖∑ k ∈ A.support.erase 0,
              A.coeff k *
                ((iteratedDeriv k
                  (normalizedGaussian m) t : ℝ) : ℂ)‖ by
      funext t
      rw [polynomialGaussianKernel_sub_eq_sum_erase_zero A hA]]
    exact integral_norm_iteratedDeriv_sum_le_inv_sqrt
      (A.support.erase 0) A.coeff id
      (fun k hk => by
        intro h
        exact (Finset.mem_erase.mp hk).1
          (by simpa only [id_eq] using h))
      hm

/--
The termwise derivative of a fixed polynomial-weighted Gaussian is
`O_A(m⁻¹ᐟ²)` in `L¹`, uniformly for `m ≥ 1`.
-/
theorem exists_polynomialGaussianKernelDeriv_l1_bound
    (A : ℂ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℝ, 1 ≤ m →
        (∫ t : ℝ, ‖polynomialGaussianKernelDeriv A m t‖) ≤
          C / Real.sqrt m := by
  let C_A : ℝ :=
    ∑ k ∈ A.support,
      ‖A.coeff k‖ * gaussianDerivativeL1 (k + 1)
  refine ⟨C_A, ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _)
        (gaussianDerivativeL1_nonneg (k + 1))
  · intro m hm
    unfold polynomialGaussianKernelDeriv Polynomial.sum
    exact integral_norm_iteratedDeriv_sum_le_inv_sqrt
      A.support A.coeff (fun k => k + 1)
      (fun _ _ => Nat.succ_ne_zero _)
      hm

/--
Multiplication of the contour polynomial by `X` becomes one additional
real derivative of the inverse Gaussian kernel.
-/
theorem polynomialGaussianKernel_X_mul
    (A : ℂ[X]) (m t : ℝ) :
    polynomialGaussianKernel (X * A) m t =
      polynomialGaussianKernelDeriv A m t := by
  induction A using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [mul_add]
      unfold polynomialGaussianKernel
        polynomialGaussianKernelDeriv at hp hq
      simp only [polynomialGaussianKernel,
        polynomialGaussianKernelDeriv]
      rw [Polynomial.sum_add_index, Polynomial.sum_add_index]
      · exact congrArg₂ (· + ·) hp hq
      · intro k
        simp
      · intro k a b
        ring
      · intro k
        simp
      · intro k a b
        ring
  | monomial n a =>
      rw [X_mul_monomial]
      simp [polynomialGaussianKernel,
        polynomialGaussianKernelDeriv]

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
