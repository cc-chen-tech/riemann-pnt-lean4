import MathlibAux.DirichletPolynomialMeanSquare

open Complex MeasureTheory
open scoped BigOperators

namespace MathlibAux

/-!
# Fourth moments of finite exponential polynomials

The square of a finite exponential polynomial is again a finite exponential
polynomial.  Frequencies of different pairs may coincide, so the coefficients
below are first collected along the fibers of the pair-frequency map.  The
existing interval second-moment theorem can then be applied without any false
injectivity assumption.
-/

/-- The distinct frequencies occurring after squaring an exponential
polynomial. -/
noncomputable def squareFrequencySupport {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (freq : ι → ℝ) : Finset ℝ :=
  (s ×ˢ s).image fun p => freq p.1 + freq p.2

/-- The coefficient of a frequency in the square of an exponential
polynomial, obtained by summing over all pairs producing that frequency. -/
noncomputable def squareFrequencyCoeff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ p ∈ s ×ˢ s with freq p.1 + freq p.2 = u,
    coeff p.1 * coeff p.2

/-- Squaring a finite exponential polynomial and collecting equal pair
frequencies gives the polynomial with `squareFrequencyCoeff` coefficients. -/
theorem exponentialPolynomial_sq_eq_squareFrequencyPolynomial
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    exponentialPolynomial s coeff freq t ^ 2 =
      exponentialPolynomial (squareFrequencySupport s freq)
        (squareFrequencyCoeff s coeff freq) (fun u => u) t := by
  let pairFreq : ι × ι → ℝ := fun p => freq p.1 + freq p.2
  let pairCoeff : ι × ι → ℂ := fun p => coeff p.1 * coeff p.2
  have hmaps : ∀ p ∈ s ×ˢ s,
      pairFreq p ∈ squareFrequencySupport s freq := by
    intro p hp
    exact Finset.mem_image_of_mem pairFreq hp
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => pairCoeff p * Complex.exp (I * (pairFreq p * t)))
  have hcollected :
      ∑ u ∈ squareFrequencySupport s freq,
          squareFrequencyCoeff s coeff freq u *
            Complex.exp (I * (u * t)) =
        ∑ p ∈ s ×ˢ s,
          pairCoeff p * Complex.exp (I * (pairFreq p * t)) := by
    calc
      ∑ u ∈ squareFrequencySupport s freq,
          squareFrequencyCoeff s coeff freq u *
            Complex.exp (I * (u * t)) =
          ∑ u ∈ squareFrequencySupport s freq,
            ∑ p ∈ s ×ˢ s with pairFreq p = u,
              pairCoeff p * Complex.exp (I * (pairFreq p * t)) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [squareFrequencyCoeff, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro p hp
            have hpu : pairFreq p = u := (Finset.mem_filter.mp hp).2
            rw [hpu]
      _ = ∑ p ∈ s ×ˢ s,
          pairCoeff p * Complex.exp (I * (pairFreq p * t)) := hfiber
  rw [exponentialPolynomial]
  change exponentialPolynomial s coeff freq t ^ 2 = _
  calc
    exponentialPolynomial s coeff freq t ^ 2 =
        ∑ p ∈ s ×ˢ s,
          pairCoeff p * Complex.exp (I * (pairFreq p * t)) := by
      rw [pow_two]
      simp only [exponentialPolynomial, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [pairCoeff, pairFreq]
      rw [show
          coeff n * Complex.exp (I * (freq n * t)) *
              (coeff m * Complex.exp (I * (freq m * t))) =
            coeff m * coeff n *
              (Complex.exp (I * (freq n * t)) *
                Complex.exp (I * (freq m * t))) by ring_nf]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    _ = ∑ u ∈ squareFrequencySupport s freq,
          squareFrequencyCoeff s coeff freq u *
            Complex.exp (I * (u * t)) := hcollected.symm

/-- Explicit interval fourth-moment bound for a finite exponential
polynomial.  Equal pair frequencies have already been merged, so every
off-diagonal denominator is nonzero. -/
theorem integral_fourthMoment_exponentialPolynomial_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    {a b : ℝ} :
    (∫ t in a..b,
        Complex.normSq (exponentialPolynomial s coeff freq t) ^ 2) ≤
      ∑ u ∈ squareFrequencySupport s freq,
        ∑ v ∈ squareFrequencySupport s freq,
          if u = v then
            (b - a) * Complex.normSq (squareFrequencyCoeff s coeff freq v)
          else
            2 * ‖squareFrequencyCoeff s coeff freq u‖ *
                ‖squareFrequencyCoeff s coeff freq v‖ / |u - v| := by
  have hrewrite :
      (∫ t in a..b,
          Complex.normSq (exponentialPolynomial s coeff freq t) ^ 2) =
        ∫ t in a..b,
          Complex.normSq
            (exponentialPolynomial (squareFrequencySupport s freq)
              (squareFrequencyCoeff s coeff freq) (fun u => u) t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    calc
      Complex.normSq (exponentialPolynomial s coeff freq t) ^ 2 =
          Complex.normSq
            (exponentialPolynomial s coeff freq t *
              exponentialPolynomial s coeff freq t) := by
        rw [Complex.normSq_mul, pow_two]
      _ = Complex.normSq (exponentialPolynomial s coeff freq t ^ 2) := by
        rw [pow_two]
      _ = Complex.normSq
          (exponentialPolynomial (squareFrequencySupport s freq)
            (squareFrequencyCoeff s coeff freq) (fun u => u) t) :=
        congrArg Complex.normSq
          (exponentialPolynomial_sq_eq_squareFrequencyPolynomial
            s coeff freq t)
  rw [hrewrite]
  exact integral_normSq_exponentialPolynomial_le
    (squareFrequencySupport s freq) (squareFrequencyCoeff s coeff freq)
      (fun u => u)
      (fun u hu v hv huv => huv)

/-- The same fourth-moment estimate specialized to logarithmic frequencies,
the form used by finite Dirichlet polynomials on a vertical line. -/
theorem integral_fourthMoment_logExponentialPolynomial_le
    (s : Finset ℕ) (coeff : ℕ → ℂ) {a b : ℝ} :
    (∫ t in a..b,
        Complex.normSq
            (exponentialPolynomial s coeff (fun n => Real.log n) t) ^ 2) ≤
      ∑ u ∈ squareFrequencySupport s (fun n => Real.log n),
        ∑ v ∈ squareFrequencySupport s (fun n => Real.log n),
          if u = v then
            (b - a) * Complex.normSq
              (squareFrequencyCoeff s coeff (fun n => Real.log n) v)
          else
            2 * ‖squareFrequencyCoeff s coeff (fun n => Real.log n) u‖ *
                ‖squareFrequencyCoeff s coeff (fun n => Real.log n) v‖ /
              |u - v| :=
  integral_fourthMoment_exponentialPolynomial_le s coeff
    (fun n => Real.log n)

end MathlibAux
