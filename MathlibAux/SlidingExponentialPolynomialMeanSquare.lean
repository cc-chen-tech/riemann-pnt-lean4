import MathlibAux.DirichletPolynomialMeanSquare

/-!
# Mean square of a sliding exponential-polynomial integral

Integrating a finite exponential polynomial over a translated interval does
not change its frequencies.  It multiplies each coefficient by the exact
Fourier transform of the interval.  This file records that identity and feeds
the transformed coefficients into the generic finite exponential-polynomial
mean-square estimate.
-/

open Complex MeasureTheory Set

namespace MathlibAux

/-- The coefficient acquired by a frequency mode after integration over a
sliding interval of length `H`. -/
noncomputable def slidingExponentialCoefficient {ι : Type*}
    (H : ℝ) (coeff : ι → ℂ) (freq : ι → ℝ) (j : ι) : ℂ :=
  coeff j * ∫ u in 0..H, Complex.exp (I * (freq j * u))

/-- The forward sliding interval integral of a finite exponential polynomial. -/
noncomputable def slidingExponentialPolynomialIntegral
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (H t : ℝ) : ℂ :=
  ∫ u in t..t + H, exponentialPolynomial s coeff freq u

/-- A sliding interval integral is an exponential polynomial with the same
frequencies and the exact interval-transform coefficients. -/
theorem slidingExponentialPolynomialIntegral_eq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (H t : ℝ) :
    slidingExponentialPolynomialIntegral s coeff freq H t =
      exponentialPolynomial s
        (slidingExponentialCoefficient H coeff freq) freq t := by
  unfold slidingExponentialPolynomialIntegral
  rw [show (fun u : ℝ => exponentialPolynomial s coeff freq u) =
      fun u : ℝ => ∑ j ∈ s,
        coeff j * Complex.exp (I * (freq j * u)) by
    rfl]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    calc
      (∫ u in t..t + H,
          coeff j * Complex.exp (I * (freq j * u))) =
          ∫ v in 0..H,
            coeff j * Complex.exp
              (I * ((freq j : ℂ) * ((v + t : ℝ) : ℂ))) := by
        have hshift := intervalIntegral.integral_comp_add_right
          (fun u : ℝ => coeff j * Complex.exp (I * (freq j * u))) t
          (a := 0) (b := H)
        simpa only [zero_add, add_comm H t] using hshift.symm
      _ = ∫ v in 0..H,
          (coeff j * Complex.exp (I * (freq j * v))) *
            Complex.exp (I * (freq j * t)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        change coeff j * Complex.exp
            (I * ((freq j : ℂ) * ((v + t : ℝ) : ℂ))) =
          (coeff j * Complex.exp (I * (freq j * v))) *
            Complex.exp (I * (freq j * t))
        push_cast
        rw [mul_assoc, ← Complex.exp_add]
        congr 1
        ring_nf
      _ = (∫ v in 0..H,
          coeff j * Complex.exp (I * (freq j * v))) *
            Complex.exp (I * (freq j * t)) :=
        intervalIntegral.integral_mul_const _ _
      _ = slidingExponentialCoefficient H coeff freq j *
            Complex.exp (I * (freq j * t)) := by
        rw [slidingExponentialCoefficient]
        congr 1
        exact intervalIntegral.integral_const_mul _ _
  · intro j hj
    apply Continuous.intervalIntegrable
    fun_prop

/-- The standard diagonal plus frequency-gap upper bound for the second
moment, over `t ∈ [A, B]`, of a sliding integral of a finite exponential
polynomial.  The bound retains the exact transformed coefficients, including
all cancellation within the sliding interval. -/
theorem integral_normSq_slidingExponentialPolynomialIntegral_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    {A B H : ℝ}
    (hfreq : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → freq m ≠ freq n) :
    (∫ t in A..B,
        Complex.normSq
          (slidingExponentialPolynomialIntegral s coeff freq H t)) ≤
      ∑ m ∈ s, ∑ n ∈ s,
        if m = n then
          (B - A) * Complex.normSq
            (slidingExponentialCoefficient H coeff freq n)
        else
          2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
              ‖slidingExponentialCoefficient H coeff freq n‖ /
            |freq m - freq n| := by
  rw [show (fun t : ℝ =>
      Complex.normSq
        (slidingExponentialPolynomialIntegral s coeff freq H t)) =
      fun t : ℝ => Complex.normSq
        (exponentialPolynomial s
          (slidingExponentialCoefficient H coeff freq) freq t) by
    funext t
    rw [slidingExponentialPolynomialIntegral_eq]]
  exact integral_normSq_exponentialPolynomial_le s
    (slidingExponentialCoefficient H coeff freq) freq hfreq

end MathlibAux
