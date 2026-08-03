import MathlibAux.DirichletPolynomialMeanSquare

open Complex
open scoped BigOperators

namespace MathlibAux

/-!
# Exponential polynomials with collected frequencies

An arbitrary finite exponential polynomial may assign the same real frequency
to several indices.  This file collects all coefficients in each frequency
fiber and reindexes the polynomial by the finite image of the frequency map.
The resulting frequency function is the identity on `ℝ`, so distinct
collected indices always have distinct frequencies.
-/

/-- The finite image of the frequencies occurring on `s`. -/
noncomputable def collectedFrequencySupport
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (freq : ι → ℝ) : Finset ℝ :=
  s.image freq

/-- The sum of all coefficients whose indices have frequency `omega`. -/
noncomputable def collectedCoefficient
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (omega : ℝ) : ℂ :=
  ∑ i ∈ s.filter (fun i => freq i = omega), coeff i

/-- The exponential polynomial obtained by collecting equal frequencies. -/
noncomputable def collectedExponentialPolynomial
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t : ℝ) : ℂ :=
  exponentialPolynomial
    (collectedFrequencySupport s freq)
    (collectedCoefficient s coeff freq)
    (fun omega => omega) t

/-- Collecting coefficients along equal-frequency fibers preserves the
exponential polynomial exactly. -/
theorem collectedExponentialPolynomial_eq_exponentialPolynomial
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    collectedExponentialPolynomial s coeff freq t =
      exponentialPolynomial s coeff freq t := by
  let term : ι → ℂ := fun i =>
    coeff i * Complex.exp (I * (freq i * t))
  have hmaps : ∀ i ∈ s, freq i ∈ collectedFrequencySupport s freq := by
    intro i hi
    exact Finset.mem_image_of_mem freq hi
  have hfiber :
      (∑ omega ∈ collectedFrequencySupport s freq,
          ∑ i ∈ s.filter (fun i => freq i = omega), term i) =
        ∑ i ∈ s, term i :=
    Finset.sum_fiberwise_of_maps_to hmaps term
  unfold collectedExponentialPolynomial exponentialPolynomial
  calc
    (∑ omega ∈ collectedFrequencySupport s freq,
        collectedCoefficient s coeff freq omega *
          Complex.exp (I * (omega * t))) =
        ∑ omega ∈ collectedFrequencySupport s freq,
          ∑ i ∈ s.filter (fun i => freq i = omega),
            term i := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [collectedCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hfreq : freq i = omega := (Finset.mem_filter.mp hi).2
      unfold term
      rw [hfreq]
    _ = ∑ i ∈ s, term i := hfiber

/-- The identity frequency map is injective on the collected support. -/
theorem collectedFrequency_injective_on_support
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (freq : ι → ℝ)
    {omega nu : ℝ}
    (_homega : omega ∈ collectedFrequencySupport s freq)
    (_hnu : nu ∈ collectedFrequencySupport s freq)
    (hfreq : (fun u : ℝ => u) omega = (fun u : ℝ => u) nu) :
    omega = nu :=
  hfreq

/-- Distinct collected support indices have distinct frequencies, in the
argument shape required by exponential-polynomial frequency-gap estimates. -/
theorem collectedFrequency_pairwise
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (freq : ι → ℝ) :
    ∀ omega ∈ collectedFrequencySupport s freq,
      ∀ nu ∈ collectedFrequencySupport s freq,
        omega ≠ nu → (fun u : ℝ => u) omega ≠ (fun u : ℝ => u) nu := by
  intro omega homega nu hnu hne
  exact hne

end MathlibAux
