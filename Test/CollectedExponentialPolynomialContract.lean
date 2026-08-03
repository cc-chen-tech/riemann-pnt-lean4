import MathlibAux.CollectedExponentialPolynomial

open Complex
open scoped BigOperators

namespace MathlibAux

/-!
# Contract for collected exponential polynomials
-/

noncomputable example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (freq : ι → ℝ) : Finset ℝ :=
  collectedFrequencySupport s freq

noncomputable example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (omega : ℝ) : ℂ :=
  collectedCoefficient s coeff freq omega

noncomputable example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t : ℝ) : ℂ :=
  collectedExponentialPolynomial s coeff freq t

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    collectedExponentialPolynomial s coeff freq t =
      exponentialPolynomial s coeff freq t :=
  collectedExponentialPolynomial_eq_exponentialPolynomial s coeff freq t

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (freq : ι → ℝ) {omega nu : ℝ}
    (homega : omega ∈ collectedFrequencySupport s freq)
    (hnu : nu ∈ collectedFrequencySupport s freq)
    (hfreq : (fun u : ℝ => u) omega = (fun u : ℝ => u) nu) :
    omega = nu :=
  collectedFrequency_injective_on_support s freq homega hnu hfreq

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (freq : ι → ℝ) :
    ∀ omega ∈ collectedFrequencySupport s freq,
      ∀ nu ∈ collectedFrequencySupport s freq,
        omega ≠ nu → (fun u : ℝ => u) omega ≠ (fun u : ℝ => u) nu :=
  collectedFrequency_pairwise s freq

end MathlibAux
