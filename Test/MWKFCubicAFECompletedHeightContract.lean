import PrimeNumberTheorem.MWKFCubicAFECompletedHeight

open PrimeNumberTheorem.MWKFCubic
open Complex Filter MeasureTheory Set
open scoped Topology

#check cubicAFEPhysicalHeightMass_nonneg
#check norm_cubicAFECompletedPhysicalSummand_le_heightMass
#check measurable_cubicAFEProgressionPhysicalSummand
#check tendsto_cubicAFECompletedPhysicalSummand_height
#check tendsto_cubicAFECompletedPhysicalIntegral_height
#check tendsto_cubicAFECompletedPhysicalIntegral_wholeLine

-- Zero shift is legitimate at fixed completion depth. In particular the
-- full spatial integral, not just each point, has the stated height limit.
example (W : CubicTestWeight) (T t : ℝ) (J : ℕ) :
    Tendsto (fun V : ℝ ↦ ∫ x : ℝ,
      (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond 1 1 0 x) : ℂ) *
        cubicAFEProgressionPhysicalSummand W T 1 V 1 1 0 t x) atTop
      (nhds (∫ x : ℝ,
        (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond 1 1 0 x) : ℂ) *
          cubicAFEProgressionPhysicalSummandVertical W T 1 1 1 0 t x)) :=
  tendsto_cubicAFECompletedPhysicalIntegral_height W T (by norm_num) 1 1 0 t J

-- Negative shifts use the physical domain, not an incorrectly substituted
-- positive half-line. At d=e=1, delta=-1, this domain is exactly x>1.
example (W : CubicTestWeight) (T t : ℝ) :
    Tendsto (fun J : ℕ ↦ ∫ x : ℝ,
      (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond 1 1 (-1) x) : ℂ) *
        cubicAFEProgressionPhysicalSummandVertical W T 1 1 1 (-1) t x) atTop
      (nhds (∫ x in Ioi (1 : ℝ),
        cubicAFEProgressionPhysicalSummandVertical W T 1 1 1 (-1) t x)) := by
  have hD : cubicAFEProgressionDomain 1 1 (-1) = Ioi (1 : ℝ) := by
    ext x
    simp only [cubicAFEProgressionDomain, Nat.gcd_self, Nat.div_self (by decide : 0 < 1),
      Nat.cast_one, Int.cast_neg, Int.cast_one, mul_one, mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨_, h⟩
      linarith
    · intro h
      constructor <;> linarith
  simpa only [hD] using tendsto_cubicAFECompletedPhysicalIntegral_wholeLine W T
    (X := 1) (by norm_num) (d := 1) (e := 1) (by decide) (by decide)
    (δ := -1) (by decide) t

-- Reversed finite-height orientation is covered by the same actual bound.
example (W : CubicTestWeight) (T t x : ℝ) :
    ‖(cubicAFEDyadicCompletionWeight 2 x (cubicAFEProgressionRealSecond 2 3 (-5) x) : ℂ) *
      cubicAFEProgressionPhysicalSummand W T 1 (-7) 2 3 (-5) t x‖ ≤
      (cubicAFEPhysicalHeightMass W T 1 2 3 t *
        (1 / 8 : ℝ) ^ (-3 / 2 : ℝ)) * cubicAFECompletedHalfLinePower 1 2 x := by
  simpa only [show -(1 : ℝ) - 1 / 2 = -3 / 2 by norm_num,
    show cubicAFECompletionLowerEndpoint 2 = 1 / 8 by norm_num [cubicAFECompletionLowerEndpoint] ]
    using norm_cubicAFECompletedPhysicalSummand_le_heightMass W T (X := 1)
      (by norm_num) (-7) 2 3 (-5) t 2 x

-- Even when the reduced denominator is totalized to zero, the completion
-- vanishes off the actual two-positive-index domain.
example (J : ℕ) (x : ℝ) :
    cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond 0 0 0 x) = 0 := by
  apply cubicAFECompletionWeight_zero_outside_domain
  simp [cubicAFEProgressionDomain]
