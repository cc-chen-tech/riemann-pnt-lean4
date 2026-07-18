import MathlibAux.DirichletPolynomialMeanSquare

#check MathlibAux.exponentialPolynomial
#check MathlibAux.norm_integral_cexp_linear_le
#check MathlibAux.integral_normSq_exponentialPolynomial_le

example {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    {a b : ℝ}
    (hfreq : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → freq m ≠ freq n) :
    (∫ t in a..b,
        Complex.normSq (MathlibAux.exponentialPolynomial s coeff freq t)) ≤
      ∑ m ∈ s, ∑ n ∈ s,
        if m = n then (b - a) * Complex.normSq (coeff n)
        else 2 * ‖coeff m‖ * ‖coeff n‖ / |freq m - freq n| :=
  MathlibAux.integral_normSq_exponentialPolynomial_le s coeff freq hfreq
