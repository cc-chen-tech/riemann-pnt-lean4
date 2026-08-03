import MathlibAux.ExponentialPolynomialShiftedCorrelation

open Complex
open scoped BigOperators

namespace MathlibAux

/-!
# Contract for shifted exponential-polynomial correlations
-/

#check exponentialPolynomial_mul_conj_shift_eq_double_sum
#check exponentialPolynomial_mul_shift_eq_double_sum
#check exponentialPolynomial_mul_conj_shift_eq_diagonal_add_offDiagonal

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t v w : ℝ) :
    exponentialPolynomial s coeff freq (t + v) *
        (starRingEnd ℂ) (exponentialPolynomial s coeff freq (t + w)) =
      ∑ n ∈ s, ∑ m ∈ s,
        coeff n * (starRingEnd ℂ) (coeff m) *
          Complex.exp
            (I * (((freq n - freq m) * t + freq n * v - freq m * w) : ℂ)) :=
  exponentialPolynomial_mul_conj_shift_eq_double_sum s coeff freq t v w

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t v w : ℝ) :
    exponentialPolynomial s coeff freq (t + v) *
        exponentialPolynomial s coeff freq (t + w) =
      ∑ n ∈ s, ∑ m ∈ s,
        coeff n * coeff m *
          Complex.exp
            (I * (((freq n + freq m) * t + freq n * v + freq m * w) : ℂ)) :=
  exponentialPolynomial_mul_shift_eq_double_sum s coeff freq t v w

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (hfreq : ∀ i ∈ s, ∀ j ∈ s, freq i = freq j → i = j)
    (t v w : ℝ) :
    exponentialPolynomial s coeff freq (t + v) *
        (starRingEnd ℂ) (exponentialPolynomial s coeff freq (t + w)) =
      (∑ i ∈ s,
        coeff i * (starRingEnd ℂ) (coeff i) *
          Complex.exp (I * ((freq i * v - freq i * w : ℝ) : ℂ))) +
      exponentialOffDiagonalForm s
        (fun i => coeff i * Complex.exp (I * ((freq i * v : ℝ) : ℂ)))
        (fun j =>
          (starRingEnd ℂ) (coeff j) *
            Complex.exp (-I * ((freq j * w : ℝ) : ℂ)))
        freq t :=
  exponentialPolynomial_mul_conj_shift_eq_diagonal_add_offDiagonal
    s coeff freq hfreq t v w

end MathlibAux
