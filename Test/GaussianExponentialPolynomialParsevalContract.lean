import MathlibAux.GaussianExponentialPolynomialParseval

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace MathlibAux

noncomputable section

example (m y : ℝ) :
    gaussianFourierDensity m y =
      Real.exp (-y ^ 2 / (4 * m)) / (2 * Real.sqrt (Real.pi * m)) := rfl

example {ι : Type*} (S : Finset ι) (coeff : ι → ℂ)
    (drift freq : ι → ℝ) (t y : ℝ) :
    frozenDriftingExponentialPolynomial S coeff drift freq t y =
      ∑ i ∈ S, coeff i * Real.exp (drift i * t) *
        Complex.exp (Complex.I * ((freq i : ℂ) * (y : ℂ))) := rfl

example {ι : Type*} (S : Finset ι) (coeff : ι → ℂ)
    (drift freq : ι → ℝ) (t m : ℝ) :
    gaussianWeightedSecondMoment S coeff drift freq t m =
      ∫ y : ℝ, gaussianFourierDensity m y *
        Complex.normSq (frozenDriftingExponentialPolynomial S coeff drift freq t y) := rfl

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (coeff : ι → ℂ) (drift freq : ι → ℝ)
    (t : ℝ) {m : ℝ} (hm : 0 < m) :
    gaussianWeightedSecondMoment S coeff drift freq t m =
      ∑ i ∈ S, ∑ j ∈ S,
        (starRingEnd ℂ (coeff j * Real.exp (drift j * t)) *
          (coeff i * Real.exp (drift i * t))).re *
            Real.exp (-m * (freq i - freq j) ^ 2) :=
  gaussianWeightedSecondMoment_eq_hermitian_sum S coeff drift freq t hm

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (coeff : ι → ℂ) (mass drift freq : ι → ℝ)
    (t : ℝ) {m : ℝ} (hm : 0 < m)
    (hmass : ∀ i ∈ S, ‖coeff i‖ = mass i) :
    gaussianWeightedSecondMoment S coeff drift freq t m ≤
      dyadicDriftingGaussianGram S mass drift freq t m :=
  gaussianWeightedSecondMoment_le_driftingGram
    S coeff mass drift freq t hm hmass

end

end MathlibAux
