import MathlibAux.AmplitudeExponentialGapIntegral

open Complex
open scoped BigOperators

namespace MathlibAux

/-!
# Shifted correlations of finite exponential polynomials

This module expands the ordinary correlation and pseudo-correlation of a
finite exponential polynomial at two translated arguments.  Keeping the
translation phases explicit lets later estimates separate equal frequencies
from genuine frequency gaps.
-/

/-- The shifted ordinary correlation is a finite double sum with frequency
difference in the common variable. -/
theorem exponentialPolynomial_mul_conj_shift_eq_double_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (t v w : ℝ) :
    exponentialPolynomial s coeff freq (t + v) *
        (starRingEnd ℂ) (exponentialPolynomial s coeff freq (t + w)) =
      ∑ n ∈ s, ∑ m ∈ s,
        coeff n * (starRingEnd ℂ) (coeff m) *
          Complex.exp
            (I * (((freq n - freq m) * t +
              freq n * v - freq m * w) : ℂ)) := by
  unfold exponentialPolynomial
  rw [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_mul, conj_I, conj_ofReal]
  rw [show
      (coeff n * Complex.exp (I * ((freq n : ℂ) * ((t + v : ℝ) : ℂ)))) *
          ((starRingEnd ℂ) (coeff m) *
            Complex.exp (-I * ((freq m : ℂ) * ((t + w : ℝ) : ℂ)))) =
        (coeff n * (starRingEnd ℂ) (coeff m)) *
          (Complex.exp (I * ((freq n : ℂ) * ((t + v : ℝ) : ℂ))) *
            Complex.exp (-I * ((freq m : ℂ) * ((t + w : ℝ) : ℂ)))) by
      ring]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The shifted pseudo-correlation is a finite double sum with frequency sum
in the common variable. -/
theorem exponentialPolynomial_mul_shift_eq_double_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (t v w : ℝ) :
    exponentialPolynomial s coeff freq (t + v) *
        exponentialPolynomial s coeff freq (t + w) =
      ∑ n ∈ s, ∑ m ∈ s,
        coeff n * coeff m *
          Complex.exp
            (I * (((freq n + freq m) * t +
              freq n * v + freq m * w) : ℂ)) := by
  unfold exponentialPolynomial
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [show
      (coeff n * Complex.exp (I * ((freq n : ℂ) * ((t + v : ℝ) : ℂ)))) *
          (coeff m * Complex.exp (I * ((freq m : ℂ) * ((t + w : ℝ) : ℂ)))) =
        (coeff n * coeff m) *
          (Complex.exp (I * ((freq n : ℂ) * ((t + v : ℝ) : ℂ))) *
            Complex.exp (I * ((freq m : ℂ) * ((t + w : ℝ) : ℂ)))) by
      ring]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- When the support frequencies are distinct, the shifted ordinary
correlation splits exactly into its equal-frequency block and the
off-diagonal gap form used by integration-by-parts estimates. -/
theorem exponentialPolynomial_mul_conj_shift_eq_diagonal_add_offDiagonal
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (hfreq : ∀ i ∈ s, ∀ j ∈ s, freq i = freq j → i = j)
    (t v w : ℝ) :
    exponentialPolynomial s coeff freq (t + v) *
        (starRingEnd ℂ) (exponentialPolynomial s coeff freq (t + w)) =
      (∑ i ∈ s,
        coeff i * (starRingEnd ℂ) (coeff i) *
          Complex.exp (I * ((freq i * v - freq i * w : ℝ) : ℂ))) +
      exponentialOffDiagonalForm s
        (fun i =>
          coeff i * Complex.exp (I * ((freq i * v : ℝ) : ℂ)))
        (fun j =>
          (starRingEnd ℂ) (coeff j) *
            Complex.exp (-I * ((freq j * w : ℝ) : ℂ)))
        freq t := by
  rw [exponentialPolynomial_mul_conj_shift_eq_double_sum]
  unfold exponentialOffDiagonalForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hdiag :
      coeff i * (starRingEnd ℂ) (coeff i) *
          Complex.exp (I * ((freq i * v - freq i * w : ℝ) : ℂ)) =
        coeff i * (starRingEnd ℂ) (coeff i) *
          Complex.exp
            (I * (((freq i - freq i) * t +
              freq i * v - freq i * w) : ℂ)) := by
    congr 2
    push_cast
    ring
  rw [hdiag, ← Finset.sum_ite_eq_of_mem s i
    (fun j =>
      coeff i * (starRingEnd ℂ) (coeff j) *
        Complex.exp
          (I * (((freq i - freq j) * t +
            freq i * v - freq j * w) : ℂ))) hi]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp
  · have hfreqne : freq i ≠ freq j := fun h => hij (hfreq i hi j hj h)
    simp only [hfreqne, hij, if_false]
    have hgap :
        I * (((freq i : ℂ) - (freq j : ℂ)) * (t : ℂ)) =
          I * (((freq i - freq j) * t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [show
      (coeff i *
          Complex.exp (I * ((freq i * v : ℝ) : ℂ))) *
        ((starRingEnd ℂ) (coeff j) *
          Complex.exp (-I * ((freq j * w : ℝ) : ℂ))) *
        Complex.exp (I * ((freq i - freq j) * t)) =
      (coeff i * (starRingEnd ℂ) (coeff j)) *
        (Complex.exp (I * ((freq i * v : ℝ) : ℂ)) *
          Complex.exp (-I * ((freq j * w : ℝ) : ℂ)) *
          Complex.exp (I * (((freq i - freq j) * t : ℝ) : ℂ))) by
      rw [hgap]
      ring]
    rw [← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring

end MathlibAux
