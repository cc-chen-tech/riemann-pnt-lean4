import MathlibAux.CollectedExponentialPolynomial

open Complex
open scoped BigOperators

#check MathlibAux.collectedFrequencySupport
#check MathlibAux.collectedCoefficient
#check MathlibAux.collectedExponentialPolynomial
#check MathlibAux.collectedExponentialPolynomial_eq_exponentialPolynomial
#check MathlibAux.collectedFrequency_injective_on_support
#check MathlibAux.collectedFrequency_pairwise

example (coeff : ℕ → ℂ) (t : ℝ) :
    MathlibAux.collectedExponentialPolynomial
        ({0, 1} : Finset ℕ) coeff (fun _ => 0) t =
      MathlibAux.exponentialPolynomial
        ({0, 1} : Finset ℕ) coeff (fun _ => 0) t :=
  MathlibAux.collectedExponentialPolynomial_eq_exponentialPolynomial
    ({0, 1} : Finset ℕ) coeff (fun _ => 0) t

#print axioms MathlibAux.collectedExponentialPolynomial_eq_exponentialPolynomial
#print axioms MathlibAux.collectedFrequency_injective_on_support
#print axioms MathlibAux.collectedFrequency_pairwise
