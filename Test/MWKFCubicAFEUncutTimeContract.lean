import PrimeNumberTheorem.MWKFCubicAFEUncutTime

open PrimeNumberTheorem.MWKFCubic
open Complex Filter MeasureTheory Set
open scoped Topology

#check integrable_cubicAFEEndpointTimeMass
#check integrable_cubicAFEEndpointSpatialPower
#check norm_cubicAFEUncutPhysicalKernel_le
#check stronglyMeasurable_cubicAFEUncutPhysicalKernel
#check integrable_cubicAFEUncutPhysicalKernel
#check tendsto_cubicAFECompletedPhysicalDoubleIntegral_depth

-- The uncut double kernel has genuine absolute integrability for a
-- negative shift; the zero-shift singular endpoint is not asserted here.
example (W : CubicTestWeight) : Integrable (fun p : ℝ × ℝ ↦
    ‖cubicAFEUncutPhysicalKernel W 2 1 1 1 (-1) p.1 p.2‖) :=
  (integrable_cubicAFEUncutPhysicalKernel W (by norm_num) (by norm_num)
    (d := 1) (e := 1) (by decide) (by decide) (δ := -1) (by decide)).norm

-- Completion is removed after the full physical time integral, over the
-- correct negative-shift domain x>1.
example (W : CubicTestWeight) :
    Tendsto (fun J : ℕ ↦ ∫ t : ℝ, ∫ x : ℝ,
      cubicAFECompletedPhysicalKernelVertical W 2 1 1 1 (-1) J t x) atTop
      (nhds (∫ t : ℝ, ∫ x in Ioi (1 : ℝ),
        cubicAFEProgressionPhysicalSummandVertical W 2 1 1 1 (-1) t x)) := by
  have hD : cubicAFEProgressionDomain 1 1 (-1) = Ioi (1 : ℝ) := by
    ext x
    simp only [cubicAFEProgressionDomain, Nat.gcd_self, Nat.div_self (by decide : 0 < 1),
      Nat.cast_one, Int.cast_neg, Int.cast_one, mul_one, mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨_, hx⟩
      linarith
    · intro hx
      constructor <;> linarith
  simpa only [hD] using tendsto_cubicAFECompletedPhysicalDoubleIntegral_depth W
    (T := 2) (by norm_num) (X := 1) (by norm_num)
    (d := 1) (e := 1) (by decide) (by decide) (δ := -1) (by decide)

example (W : CubicTestWeight) (T X t : ℝ) :
    cubicAFEUncutPhysicalKernel W T X 1 1 (-1) t 1 = 0 := by
  simp [cubicAFEUncutPhysicalKernel, cubicAFEProgressionDomain]

example : Integrable (cubicAFEEndpointSpatialPower 1 1 1 1) :=
  integrable_cubicAFEEndpointSpatialPower (by norm_num) (by decide) (by decide) (by decide)
