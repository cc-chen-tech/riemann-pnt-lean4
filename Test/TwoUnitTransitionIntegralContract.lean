import MathlibAux.TwoUnitTransitionIntegral

open Set MeasureTheory

-- These types rule out an extra length-N factor or a hidden integrability premise.
example {f : ℝ → ℝ} {x N C : ℝ} (hxN : x ≤ N)
    (hf : ContinuousOn f (Icc (x - 1) (N + 1)))
    (hbound : ∀ u ∈ Icc (x - 1) (N + 1), f u ≤ C)
    (hzero : ∀ u ∈ Icc x N, f u = 0) :
    (∫ u in (x - 1)..(N + 1), f u) ≤ 2 * C :=
  MathlibAux.intervalIntegral_le_two_unit_transitions hxN hf hbound hzero

example {f : ℝ → ℝ} {x N C p : ℝ} (hx : 1 < x) (hxN : x ≤ N)
    (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hf : ContinuousOn f (Icc (x - 1) (N + 1)))
    (hbound : ∀ u ∈ Icc (x - 1) (N + 1), |f u| ≤ C)
    (hzero : ∀ u ∈ Icc x N, f u = 0) :
    (∫ u in (x - 1)..(N + 1), |f u| * u ^ (-p)) ≤
      2 * C * (x - 1) ^ (-p) :=
  MathlibAux.intervalIntegral_abs_mul_rpow_le_two_unit_transitions
    hx hxN hC hp hf hbound hzero

#print axioms MathlibAux.intervalIntegral_le_two_unit_transitions
#print axioms MathlibAux.intervalIntegral_abs_mul_rpow_le_two_unit_transitions
