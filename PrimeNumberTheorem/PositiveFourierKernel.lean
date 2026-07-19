import PrimeNumberTheorem.DirichletPolynomialMeanSquare
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- Fourier kernel with the convention matching `finiteExponentialSum`. -/
noncomputable def fourierKernel (g : ℝ → ℝ) (xi : ℝ) : ℂ :=
  ∫ t, (g t : ℂ) * Complex.exp (Complex.I * (xi * t))

/-- Positive dilation of a weight divides its Fourier frequency and contributes
the reciprocal Jacobian. -/
theorem fourierKernel_scale_pos
    {g : ℝ → ℝ} {delta xi : ℝ} (hdelta : 0 < delta) :
    fourierKernel (fun t => g (delta * t)) xi =
      ((delta⁻¹ : ℝ) : ℂ) * fourierKernel g (xi / delta) := by
  let F : ℝ → ℂ := fun y =>
    (g y : ℂ) * Complex.exp
      (Complex.I * (((xi / delta) * y : ℝ) : ℂ))
  have hphase (t : ℝ) : (xi / delta) * (delta * t) = xi * t := by
    field_simp
  unfold fourierKernel
  calc
    (∫ t, (g (delta * t) : ℂ) *
        Complex.exp (Complex.I * (xi * t))) =
        ∫ t, F (delta * t) := by
      congr 1
      funext t
      simp only [F, ← ofReal_mul, hphase]
    _ = |delta⁻¹| • ∫ y, F y :=
      Measure.integral_comp_mul_left F delta
    _ = ((delta⁻¹ : ℝ) : ℂ) * ∫ y, F y := by
      rw [abs_of_pos (inv_pos.mpr hdelta), Complex.real_smul]
    _ = ((delta⁻¹ : ℝ) : ℂ) * fourierKernel g (xi / delta) := by
      unfold fourierKernel
      simp only [F, ofReal_mul]

/-- The finite quadratic form induced by a Fourier kernel. -/
noncomputable def finiteFourierKernelForm {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) (g : ℝ → ℝ) : ℂ :=
  ∑ m ∈ S, ∑ n ∈ S,
    conj (c m) * c n * fourierKernel g (omega n - omega m)

private theorem integrable_fourierKernel_integrand
    {g : ℝ → ℝ} (hg : Integrable g) (xi : ℝ) :
    Integrable (fun t : ℝ =>
      (g t : ℂ) * Complex.exp (Complex.I * (xi * t))) := by
  apply hg.ofReal.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with t
    simp [Complex.norm_exp]

/-- The Fourier kernel is additive with respect to subtraction of integrable
real weights. -/
theorem fourierKernel_sub
    {g h : ℝ → ℝ} (hg : Integrable g) (hh : Integrable h) {xi : ℝ} :
    fourierKernel (fun t => g t - h t) xi =
      fourierKernel g xi - fourierKernel h xi := by
  unfold fourierKernel
  rw [← integral_sub (integrable_fourierKernel_integrand hg xi)
    (integrable_fourierKernel_integrand hh xi)]
  congr 1
  funext t
  push_cast
  ring

/-- A finite Fourier-kernel form is the integral of the weight times the
squared norm of the corresponding finite exponential sum. -/
theorem finiteFourierKernelForm_eq_integral_normSq
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {c : ι → ℂ} {omega : ι → ℝ} {g : ℝ → ℝ}
    (hg : Integrable g) :
    finiteFourierKernelForm S c omega g =
      ((∫ t, g t * ‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ) := by
  unfold finiteFourierKernelForm fourierKernel
  simp only [ofReal_sub]
  calc
    (∑ m ∈ S, ∑ n ∈ S,
        conj (c m) * c n *
          (∫ t, (g t : ℂ) *
            Complex.exp (Complex.I *
              (((omega n : ℂ) - (omega m : ℂ)) * (t : ℂ))))) =
        ∑ m ∈ S, ∑ n ∈ S,
          ∫ t, (conj (c m) * c n) *
            ((g t : ℂ) *
              Complex.exp (Complex.I *
                (((omega n : ℂ) - (omega m : ℂ)) * (t : ℂ)))) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact (integral_const_mul (conj (c m) * c n) _).symm
    _ = ∫ t, ∑ m ∈ S, ∑ n ∈ S,
          (conj (c m) * c n) *
            ((g t : ℂ) *
              Complex.exp (Complex.I *
                (((omega n : ℂ) - (omega m : ℂ)) * (t : ℂ)))) := by
      rw [MeasureTheory.integral_finset_sum S]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [MeasureTheory.integral_finset_sum S]
        intro n hn
        simpa only [ofReal_sub] using
          (integrable_fourierKernel_integrand hg
            (omega n - omega m)).const_mul (conj (c m) * c n)
      · intro m hm
        exact integrable_finset_sum S fun n hn => by
          simpa only [ofReal_sub] using
            (integrable_fourierKernel_integrand hg
              (omega n - omega m)).const_mul (conj (c m) * c n)
    _ = ∫ t, (((g t * ‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ)) := by
      congr 1
      funext t
      calc
        (∑ m ∈ S, ∑ n ∈ S,
            (conj (c m) * c n) *
              ((g t : ℂ) *
                Complex.exp (Complex.I *
                  (((omega n : ℂ) - (omega m : ℂ)) * (t : ℂ))))) =
            (g t : ℂ) *
              (∑ m ∈ S, ∑ n ∈ S,
                conj (c m) * c n *
                  Complex.exp (Complex.I *
                    (((omega n : ℂ) - (omega m : ℂ)) * (t : ℂ)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = (g t : ℂ) *
              (conj (finiteExponentialSum S c omega t) *
                finiteExponentialSum S c omega t) := by
          rw [conj_mul_finiteExponentialSum_eq]
        _ = ((g t * ‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          rw [← ofReal_pow, ← Complex.normSq_eq_norm_sq,
            Complex.normSq_eq_conj_mul_self]
    _ = ((∫ t, g t * ‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ) := by
      exact integral_ofReal

/-- Every nonnegative integrable weight produces a positive-semidefinite
Fourier kernel on every finite family of real frequencies. -/
theorem finiteFourierKernelForm_re_nonneg
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {c : ι → ℂ} {omega : ι → ℝ} {g : ℝ → ℝ}
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t) :
    0 ≤ (finiteFourierKernelForm S c omega g).re := by
  rw [finiteFourierKernelForm_eq_integral_normSq hg]
  simp only [ofReal_re]
  exact integral_nonneg fun t => mul_nonneg (hg0 t) (sq_nonneg _)

/-- A prescribed reciprocal-frequency formula for the off-diagonal Fourier
kernel turns its finite quadratic form into a diagonal term plus a scalar
multiple of the Hilbert form. -/
theorem finiteFourierKernelForm_eq_diagonal_add_mul_hilbert
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {c : ι → ℂ} {omega : ι → ℝ} {g : ℝ → ℝ} {kappa : ℂ}
    (hkernel : ∀ m ∈ S, ∀ n ∈ S, m ≠ n →
      fourierKernel g (omega n - omega m) =
        kappa / (omega n - omega m)) :
    finiteFourierKernelForm S c omega g =
      fourierKernel g 0 * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) +
        kappa * hilbertForm S c omega := by
  have hpair : ∀ m ∈ S, ∀ n ∈ S,
      conj (c m) * c n * fourierKernel g (omega n - omega m) =
        if m = n then
          fourierKernel g 0 * (‖c m‖ ^ 2 : ℂ)
        else kappa * (conj (c m) * c n / (omega n - omega m)) := by
    intro m hm n hn
    by_cases hmn : m = n
    · subst n
      rw [if_pos rfl, sub_self]
      rw [← ofReal_pow, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_conj_mul_self]
      ring
    · rw [if_neg hmn, hkernel m hm n hn hmn]
      ring
  have hdiag :
      (∑ m ∈ S, ∑ n ∈ S,
        if m = n then fourierKernel g 0 * (‖c m‖ ^ 2 : ℂ) else 0) =
        fourierKernel g 0 * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) := by
    calc
      (∑ m ∈ S, ∑ n ∈ S,
          if m = n then fourierKernel g 0 * (‖c m‖ ^ 2 : ℂ) else 0) =
          ∑ m ∈ S, fourierKernel g 0 * (‖c m‖ ^ 2 : ℂ) := by
        apply Finset.sum_congr rfl
        intro m hm
        simp [hm]
      _ = fourierKernel g 0 * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) := by
        rw [Finset.mul_sum]
  have hoff :
      (∑ m ∈ S, ∑ n ∈ S,
        if m = n then 0
        else kappa * (conj (c m) * c n / (omega n - omega m))) =
        kappa * hilbertForm S c omega := by
    unfold hilbertForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hmn : m = n <;> simp [hmn]
  unfold finiteFourierKernelForm
  calc
    (∑ m ∈ S, ∑ n ∈ S,
        conj (c m) * c n * fourierKernel g (omega n - omega m)) =
        ∑ m ∈ S, ∑ n ∈ S,
          if m = n then
            fourierKernel g 0 * (‖c m‖ ^ 2 : ℂ)
          else kappa * (conj (c m) * c n / (omega n - omega m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact hpair m hm n hn
    _ = (∑ m ∈ S, ∑ n ∈ S,
          if m = n then fourierKernel g 0 * (‖c m‖ ^ 2 : ℂ) else 0) +
        (∑ m ∈ S, ∑ n ∈ S,
          if m = n then 0
          else kappa * (conj (c m) * c n / (omega n - omega m))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmn : m = n <;> simp [hmn]
    _ = fourierKernel g 0 * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) +
        kappa * hilbertForm S c omega := by
      rw [hdiag, hoff]

/-- A nonnegative kernel with off-diagonal value `-2i / ξ` supplies the
minus side of a weighted Hilbert-form certificate. -/
theorem hilbertForm_minus_certificate_of_positive_kernel
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {c : ι → ℂ} {omega : ι → ℝ} {g : ℝ → ℝ} {C : ℝ}
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t)
    (hzero : fourierKernel g 0 = ((2 * C : ℝ) : ℂ))
    (hkernel : ∀ m ∈ S, ∀ n ∈ S, m ≠ n →
      fourierKernel g (omega n - omega m) =
        (-2 * Complex.I) / (omega n - omega m)) :
    0 ≤ (((C * ∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) -
      Complex.I * hilbertForm S c omega).re := by
  have hsum :
      (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) =
        ((∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hform :=
    finiteFourierKernelForm_eq_diagonal_add_mul_hilbert
      (S := S) (c := c) (omega := omega) (g := g)
      (kappa := -2 * Complex.I) hkernel
  have hfactor :
      finiteFourierKernelForm S c omega g =
        (2 : ℂ) *
          (((C * ∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) -
            Complex.I * hilbertForm S c omega) := by
    rw [hform, hzero, hsum]
    push_cast
    ring
  have hnonneg := finiteFourierKernelForm_re_nonneg
    (S := S) (c := c) (omega := omega) hg hg0
  rw [hfactor] at hnonneg
  have htwice :
      0 ≤ 2 * ((((C * ∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) -
        Complex.I * hilbertForm S c omega).re) := by
    simpa using hnonneg
  linarith

/-- A nonnegative kernel with off-diagonal value `2i / ξ` supplies the plus
side of a weighted Hilbert-form certificate. -/
theorem hilbertForm_plus_certificate_of_positive_kernel
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {c : ι → ℂ} {omega : ι → ℝ} {g : ℝ → ℝ} {C : ℝ}
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t)
    (hzero : fourierKernel g 0 = ((2 * C : ℝ) : ℂ))
    (hkernel : ∀ m ∈ S, ∀ n ∈ S, m ≠ n →
      fourierKernel g (omega n - omega m) =
        (2 * Complex.I) / (omega n - omega m)) :
    0 ≤ (((C * ∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * hilbertForm S c omega).re := by
  have hsum :
      (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) =
        ((∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hform :=
    finiteFourierKernelForm_eq_diagonal_add_mul_hilbert
      (S := S) (c := c) (omega := omega) (g := g)
      (kappa := 2 * Complex.I) hkernel
  have hfactor :
      finiteFourierKernelForm S c omega g =
        (2 : ℂ) *
          (((C * ∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) +
            Complex.I * hilbertForm S c omega) := by
    rw [hform, hzero, hsum]
    push_cast
    ring
  have hnonneg := finiteFourierKernelForm_re_nonneg
    (S := S) (c := c) (omega := omega) hg hg0
  rw [hfactor] at hnonneg
  have htwice :
      0 ≤ 2 * ((((C * ∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) +
        Complex.I * hilbertForm S c omega).re) := by
    simpa using hnonneg
  linarith

/-- The finite Fourier-kernel form is additive with respect to subtraction of
integrable weights. -/
theorem finiteFourierKernelForm_sub
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {c : ι → ℂ} {omega : ι → ℝ} {g h : ℝ → ℝ}
    (hg : Integrable g) (hh : Integrable h) :
    finiteFourierKernelForm S c omega (fun t => g t - h t) =
      finiteFourierKernelForm S c omega g -
        finiteFourierKernelForm S c omega h := by
  unfold finiteFourierKernelForm
  simp_rw [fourierKernel_sub hg hh]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- If a positive dilation increases an integrable weight pointwise, the
corresponding increment of every finite Fourier-kernel form is positive. -/
theorem finiteFourierKernelForm_scaled_sub_re_nonneg
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {c : ι → ℂ} {omega : ι → ℝ} {g : ℝ → ℝ}
    {deltaSmall deltaLarge : ℝ}
    (hg : Integrable g) (hSmall : 0 < deltaSmall)
    (hLarge : 0 < deltaLarge)
    (hmono : ∀ t, g (deltaSmall * t) ≤ g (deltaLarge * t)) :
    0 ≤ (finiteFourierKernelForm S c omega
          (fun t => g (deltaLarge * t)) -
        finiteFourierKernelForm S c omega
          (fun t => g (deltaSmall * t))).re := by
  have hgLarge : Integrable (fun t => g (deltaLarge * t)) :=
    hg.comp_mul_left' hLarge.ne'
  have hgSmall : Integrable (fun t => g (deltaSmall * t)) :=
    hg.comp_mul_left' hSmall.ne'
  rw [← finiteFourierKernelForm_sub hgLarge hgSmall]
  exact finiteFourierKernelForm_re_nonneg (hgLarge.sub hgSmall)
    fun t => sub_nonneg.mpr (hmono t)

/-- Successive increments of finite Fourier-kernel forms telescope exactly. -/
theorem finiteFourierKernelForm_telescope
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (g : ℕ → ℝ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
        (finiteFourierKernelForm S c omega (g (k + 1)) -
          finiteFourierKernelForm S c omega (g k))) =
      finiteFourierKernelForm S c omega (g N) -
        finiteFourierKernelForm S c omega (g 0) := by
  exact Finset.sum_range_sub (fun k => finiteFourierKernelForm S c omega (g k)) N

end DirichletPolynomial
end PrimeNumberTheorem
