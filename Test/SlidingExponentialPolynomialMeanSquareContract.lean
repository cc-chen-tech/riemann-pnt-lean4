import MathlibAux.SlidingExponentialPolynomialMeanSquare

open Complex

namespace MathlibAux

#check slidingExponentialCoefficient
#check slidingExponentialPolynomialIntegral
#check slidingExponentialPolynomialIntegral_eq
#check integral_normSq_slidingExponentialPolynomialIntegral_le

#print axioms slidingExponentialPolynomialIntegral_eq
#print axioms integral_normSq_slidingExponentialPolynomialIntegral_le

example {ι : Type*} [DecidableEq ι]
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
  exact integral_normSq_slidingExponentialPolynomialIntegral_le
    s coeff freq hfreq

end MathlibAux
