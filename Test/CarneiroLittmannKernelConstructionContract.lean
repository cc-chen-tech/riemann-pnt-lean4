import PrimeNumberTheorem.CarneiroLittmannKernelConstruction

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example {x : ℝ} (hx : x ≤ 0) :
    0 ≤ carneiroLittmannCumulative x :=
  carneiroLittmannCumulative_nonneg_of_nonpos hx

example {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ carneiroLittmannCumulative x :=
  one_le_carneiroLittmannCumulative_of_nonneg hx

example (x : ℝ) : 0 ≤ carneiroLittmannKernelError x :=
  carneiroLittmannKernelError_nonneg x

example {deltaSmall deltaLarge : ℝ}
    (hsmall : 0 < deltaSmall) (hle : deltaSmall ≤ deltaLarge) (t : ℝ) :
    carneiroLittmannKernelError (deltaLarge * t) ≤
      carneiroLittmannKernelError (deltaSmall * t) :=
  carneiroLittmannKernelError_dilation_antitone hsmall hle t

example {x : ℝ} (hx : 1 ≤ x) :
    carneiroLittmannKernelError x ≤ x ^ (-2 : ℝ) / 2 :=
  carneiroLittmannKernelError_le_rpow_neg_two_of_one_le hx

example {x : ℝ} (hx : x ≤ -2) :
    carneiroLittmannKernelError x ≤ 2 * (-x) ^ (-2 : ℝ) :=
  carneiroLittmannKernelError_le_two_mul_neg_rpow_neg_two_of_le_neg_two hx

example : MeasureTheory.Integrable carneiroLittmannKernelError :=
  integrable_carneiroLittmannKernelError

example (x : ℝ) :
    -(x * carneiroLittmannDerivative x) = carneiroLittmannSincSquare x :=
  neg_mul_carneiroLittmannDerivative_eq_sincSquare x

example : (∫ x : ℝ, carneiroLittmannKernelError x) = 1 :=
  integral_carneiroLittmannKernelError_eq_one

example : MeasureTheory.Integrable carneiroLittmannRawKernel :=
  integrable_carneiroLittmannRawKernel

example (x : ℝ) : 0 ≤ carneiroLittmannRawKernel x :=
  carneiroLittmannRawKernel_nonneg x

example {deltaSmall deltaLarge : ℝ}
    (hsmall : 0 < deltaSmall) (hle : deltaSmall ≤ deltaLarge) (t : ℝ) :
    carneiroLittmannRawKernel (deltaLarge * t) ≤
      carneiroLittmannRawKernel (deltaSmall * t) :=
  carneiroLittmannRawKernel_dilation_antitone hsmall hle t

example : fourierKernel carneiroLittmannRawKernel 0 = (2 : ℂ) :=
  fourierKernel_carneiroLittmannRawKernel_zero

example {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel carneiroLittmannRawKernel xi =
      (-2 * Complex.I) / xi :=
  fourierKernel_carneiroLittmannRawKernel_of_two_pi_le_abs hxi

noncomputable example : CarneiroLittmannKernel :=
  carneiroLittmannKernel

example {N : ℕ} {c : ℕ → ℂ} {omega delta : ℕ → ℝ}
    (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n)
    (hlocal : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    ‖hilbertForm (Finset.range N) c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ Finset.range N, (delta n)⁻¹ * ‖c n‖ ^ 2 :=
  norm_hilbertForm_range_le_carneiroLittmann hdelta hanti hlocal

example {L U : ℕ} (hL : 0 < L) (c : ℕ → ℂ) :
    ‖hilbertForm (Finset.Icc L U) c (fun n : ℕ => -Real.log n)‖ ≤
      2 * Real.pi *
        ∑ n ∈ Finset.Icc L U, ((n : ℝ) + 1) * ‖c n‖ ^ 2 :=
  norm_hilbertForm_Icc_neg_log_le_carneiroLittmann hL c

example {a b : ℝ} (N : ℕ) (c : ℕ → ℂ) (omega delta : ℕ → ℝ)
    (hab : a ≤ b)
    (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n)
    (hlocal : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    ∫ t in a..b, ‖finiteExponentialSum (Finset.range N) c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 +
        4 * Real.pi *
          ∑ n ∈ Finset.range N, (delta n)⁻¹ * ‖c n‖ ^ 2 :=
  finiteExponentialSum_meanSquare_le_carneiroLittmann
    hab hdelta hanti hlocal

#print axioms carneiroLittmannCumulative_nonneg_of_nonpos
#print axioms one_le_carneiroLittmannCumulative_of_nonneg
#print axioms carneiroLittmannKernelError_nonneg
#print axioms carneiroLittmannKernelError_dilation_antitone
#print axioms carneiroLittmannKernelError_le_rpow_neg_two_of_one_le
#print axioms carneiroLittmannKernelError_le_two_mul_neg_rpow_neg_two_of_le_neg_two
#print axioms integrable_carneiroLittmannKernelError
#print axioms neg_mul_carneiroLittmannDerivative_eq_sincSquare
#print axioms integral_carneiroLittmannKernelError_eq_one
#print axioms integrable_carneiroLittmannRawKernel
#print axioms carneiroLittmannRawKernel_nonneg
#print axioms carneiroLittmannRawKernel_dilation_antitone
#print axioms fourierKernel_carneiroLittmannRawKernel_zero
#print axioms fourierKernel_carneiroLittmannRawKernel_of_two_pi_le_abs
#print axioms carneiroLittmannKernel
#print axioms norm_hilbertForm_range_le_carneiroLittmann
#print axioms norm_hilbertForm_Icc_neg_log_le_carneiroLittmann
#print axioms finiteExponentialSum_meanSquare_le_carneiroLittmann

end DirichletPolynomial
end PrimeNumberTheorem
