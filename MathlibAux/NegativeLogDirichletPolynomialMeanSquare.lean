import MathlibAux.LogDirichletPolynomialMeanSquare

open Complex MeasureTheory Set

namespace MathlibAux

private theorem negLogExponentialPolynomial_eq_logExponentialPolynomial_neg
    (s : Finset ℕ) (coeff : ℕ → ℂ) (t : ℝ) :
    exponentialPolynomial s coeff (fun n => -Real.log n) t =
      exponentialPolynomial s coeff (fun n => Real.log n) (-t) := by
  simp only [exponentialPolynomial]
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  push_cast
  ring

/-- Reflecting the time variable transfers the global logarithmic-frequency
second-moment bound to the negative logarithmic frequencies used by the
critical-line short Dirichlet polynomial. -/
theorem integral_normSq_negLogExponentialPolynomial_le_of_upper
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    {a b : ℝ} :
    (∫ t in a..b,
        Complex.normSq
          (exponentialPolynomial s coeff (fun n => -Real.log n) t)) ≤
      ((b - a) + 4 * (5 * Real.pi + 4) * N) *
        ∑ n ∈ s, Complex.normSq (coeff n) := by
  have hreflect :
      (∫ t in a..b,
          Complex.normSq
            (exponentialPolynomial s coeff (fun n => -Real.log n) t)) =
        ∫ t in -b..-a,
          Complex.normSq
            (exponentialPolynomial s coeff (fun n => Real.log n) t) := by
    calc
      (∫ t in a..b,
          Complex.normSq
            (exponentialPolynomial s coeff (fun n => -Real.log n) t)) =
          ∫ t in a..b,
            Complex.normSq
              (exponentialPolynomial s coeff (fun n => Real.log n) (-t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change Complex.normSq
            (exponentialPolynomial s coeff (fun n => -Real.log n) t) =
          Complex.normSq
            (exponentialPolynomial s coeff (fun n => Real.log n) (-t))
        exact congrArg Complex.normSq
          (negLogExponentialPolynomial_eq_logExponentialPolynomial_neg
            s coeff t)
      _ = ∫ t in -b..-a,
          Complex.normSq
            (exponentialPolynomial s coeff (fun n => Real.log n) t) :=
        intervalIntegral.integral_comp_neg
          (f := fun t : ℝ => Complex.normSq
            (exponentialPolynomial s coeff (fun n => Real.log n) t))
          (a := a) (b := b)
  rw [hreflect]
  have hbound := integral_normSq_logExponentialPolynomial_le_of_upper
    hN s coeff hpositive hupper (a := -b) (b := -a)
  convert hbound using 1
  ring

end MathlibAux
