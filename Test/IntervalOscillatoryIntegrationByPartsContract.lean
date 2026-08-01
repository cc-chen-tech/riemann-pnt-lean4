import MathlibAux.IntervalOscillatoryIntegrationByParts

open Complex MeasureTheory Set

#check MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_of_norm_deriv

example {A A' : ℝ → ℂ} {u v omega M0 M1 : ℝ}
    (huv : u ≤ v) (homega : omega ≠ 0)
    (hA : ∀ t ∈ uIcc u v, HasDerivAt A (A' t) t)
    (hA'int : IntervalIntegrable A' volume u v)
    (hA0 : ∀ t ∈ uIcc u v, ‖A t‖ ≤ M0)
    (hA1 : ∀ t ∈ uIcc u v, ‖A' t‖ ≤ M1) :
    ‖∫ t in u..v, A t * Complex.exp (I * (omega * t))‖ ≤
      (2 * M0 + (v - u) * M1) / |omega| :=
  MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_of_norm_deriv
    huv homega hA hA'int hA0 hA1
