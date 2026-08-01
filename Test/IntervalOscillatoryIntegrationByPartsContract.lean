import MathlibAux.IntervalOscillatoryIntegrationByParts

open Complex MeasureTheory Set

#check MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_of_norm_deriv
#check MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_of_totalVariation
#check MathlibAux.intervalIntegral_norm_le_mul_log_div_of_norm_le_div
#check MathlibAux.intervalIntegrable_deriv_of_norm_le_div

example {A : ℝ → ℂ} {u v V : ℝ}
    (hu : 0 < u) (huv : u ≤ v)
    (hbound : ∀ t ∈ Set.Icc u v, ‖deriv A t‖ ≤ V / t) :
    IntervalIntegrable (deriv A) volume u v :=
  MathlibAux.intervalIntegrable_deriv_of_norm_le_div hu huv hbound

example {A' : ℝ → ℂ} {u v V : ℝ}
    (hu : 0 < u) (huv : u ≤ v)
    (hA'int : IntervalIntegrable A' volume u v)
    (hbound : ∀ t ∈ Set.Icc u v, ‖A' t‖ ≤ V / t) :
    (∫ t in u..v, ‖A' t‖) ≤ V * Real.log (v / u) :=
  MathlibAux.intervalIntegral_norm_le_mul_log_div_of_norm_le_div
    hu huv hA'int hbound

example {A A' : ℝ → ℂ} {u v omega M0 V : ℝ}
    (huv : u ≤ v) (homega : omega ≠ 0)
    (hA : ∀ t ∈ uIcc u v, HasDerivAt A (A' t) t)
    (hA'int : IntervalIntegrable A' volume u v)
    (hA0 : ∀ t ∈ uIcc u v, ‖A t‖ ≤ M0)
    (hvariation : (∫ t in u..v, ‖A' t‖) ≤ V) :
    ‖∫ t in u..v, A t * Complex.exp (I * (omega * t))‖ ≤
      (2 * M0 + V) / |omega| :=
  MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_of_totalVariation
    huv homega hA hA'int hA0 hvariation

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
