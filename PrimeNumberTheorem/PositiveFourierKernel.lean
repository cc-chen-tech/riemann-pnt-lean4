import PrimeNumberTheorem.DirichletPolynomialMeanSquare

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- Fourier kernel with the convention matching `finiteExponentialSum`. -/
noncomputable def fourierKernel (g : ℝ → ℝ) (xi : ℝ) : ℂ :=
  ∫ t, (g t : ℂ) * Complex.exp (Complex.I * (xi * t))

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

end DirichletPolynomial
end PrimeNumberTheorem
