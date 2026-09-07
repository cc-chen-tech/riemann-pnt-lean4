import PrimeNumberTheorem.MWKFCubicAFEEndpointPower

open PrimeNumberTheorem.MWKFCubic
open MeasureTheory Set

#check cubicAFEEndpointPower_nonneg
#check measurable_cubicAFEEndpointPower
#check integrable_cubicAFEEndpointPower
#check norm_cubicAFEWeightedProduct_le_endpointPower
#check integrableOn_cubicAFEEndpointPower_quadratic

-- The common boundary belongs to the small-product piece exactly once.
example (X : ℝ) : cubicAFEEndpointPower X 1 = 1 := by
  rw [cubicAFEEndpointPower_small X zero_lt_one le_rfl, Real.one_rpow]

example (X : ℝ) : cubicAFEEndpointPower X 0 = 0 := by
  simp [cubicAFEEndpointPower]

-- At a negative shift the spatial domain starts at 1, not at 0.
example : IntegrableOn (fun x : ℝ ↦ cubicAFEEndpointPower 1 (x * (x - 1))) (Ioi (1 : ℝ)) := by
  have hD : {x : ℝ | 0 < x ∧ 0 < (-1 : ℝ) + 1 * x} = Ioi (1 : ℝ) := by
    ext x
    simp only [mem_ofPred_eq, mem_Ioi, one_mul]
    constructor
    · rintro ⟨_, hx⟩
      linarith
    · intro hx
      constructor <;> linarith
  have hi := integrableOn_cubicAFEEndpointPower_quadratic (X := 1) (r := 1) (s := 1) (δ := -1)
    (by norm_num) zero_lt_one zero_lt_one (by norm_num)
  rw [hD] at hi
  simpa only [one_mul, div_one, show ∀ x : ℝ, -1 + x = x - 1 by intro x; ring] using hi
