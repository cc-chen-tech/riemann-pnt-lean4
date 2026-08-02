import MathlibAux.AmplitudeExponentialGapIntegral

open Complex MeasureTheory Set

namespace MathlibAux

#check exponentialOffDiagonalForm

example {A A' : ℝ → ℂ} {a b K V lambda : ℝ}
    (hab : a ≤ b) (hlambda : lambda ≠ 0)
    (hA : ∀ x ∈ Set.uIcc a b, HasDerivAt A (A' x) x)
    (hAend : ‖A a‖ ≤ K ∧ ‖A b‖ ≤ K)
    (hA'int : IntervalIntegrable A' volume a b)
    (hvariation : (∫ x in a..b, ‖A' x‖) ≤ V) :
    ‖∫ t in a..b, A t * Complex.exp (I * (lambda * t))‖ ≤
      (2 * K + V) / |lambda| :=
  norm_integral_amplitude_mul_cexp_linear_le
    hab hlambda hA hAend hA'int hvariation

example {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (left right : ι → ℂ) (freq : ι → ℝ)
    {A A' : ℝ → ℂ} {a b K V : ℝ}
    (hab : a ≤ b)
    (hA : ∀ x ∈ Set.uIcc a b, HasDerivAt A (A' x) x)
    (hAend : ‖A a‖ ≤ K ∧ ‖A b‖ ≤ K)
    (hA'int : IntervalIntegrable A' volume a b)
    (hvariation : (∫ x in a..b, ‖A' x‖) ≤ V) :
    ‖∫ t in a..b,
        A t * exponentialOffDiagonalForm s left right freq t‖ ≤
      ∑ i ∈ s, ∑ j ∈ s,
        if freq i = freq j then 0
        else ‖left i‖ * ‖right j‖ *
          ((2 * K + V) / |freq i - freq j|) :=
  norm_integral_amplitude_mul_exponentialOffDiagonal_le
    s left right freq hab hA hAend hA'int hvariation

end MathlibAux
