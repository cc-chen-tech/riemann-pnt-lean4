import MathlibAux.ExponentialPolynomialFourthMoment

open Complex MeasureTheory

namespace MathlibAux

#check squareFrequencySupport
#check squareFrequencyCoeff
#check exponentialPolynomial_sq_eq_squareFrequencyPolynomial
#check integral_fourthMoment_exponentialPolynomial_le
#check integral_fourthMoment_logExponentialPolynomial_le

#print axioms exponentialPolynomial_sq_eq_squareFrequencyPolynomial
#print axioms integral_fourthMoment_exponentialPolynomial_le
#print axioms integral_fourthMoment_logExponentialPolynomial_le

example {ι : Type*} [DecidableEq ι]
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
                ‖squareFrequencyCoeff s coeff freq v‖ / |u - v| :=
  integral_fourthMoment_exponentialPolynomial_le s coeff freq

example (s : Finset ℕ) (coeff : ℕ → ℂ) {a b : ℝ} :
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
  integral_fourthMoment_logExponentialPolynomial_le s coeff

end MathlibAux
