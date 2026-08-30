import PrimeNumberTheorem.MWKFCubicAFEDyadicBoundary

open PrimeNumberTheorem.MWKFCubic

#check hasSum_cubicAFEDyadicWindow_allReal
#check hasSum_cubicAFEProgressionDyadicCutoff_allReal

-- Full real-axis statement: replacing the right side by 1 is invalid.
#check (@hasSum_cubicAFEDyadicWindow_allReal :
  ∀ x : ℝ, HasSum (fun j : ℕ ↦ cubicAFEDyadicWindow j x) (cubicAFEDyadicLowerWeight x))

example : cubicAFEDyadicLowerWeight (1 / 4) = 0 :=
  cubicAFEDyadicLowerWeight_zero (by norm_num)

example : cubicAFEDyadicLowerWeight (1 / 2) = 0 :=
  cubicAFEDyadicLowerWeight_zero le_rfl

example : cubicAFEDyadicLowerWeight 1 = 1 := cubicAFEDyadicLowerWeight_one le_rfl

example : cubicAFEDyadicLowerWeight (-3) = 0 :=
  cubicAFEDyadicLowerWeight_zero (by norm_num)

-- The second index can be below the continuous lower boundary even if the
-- first index is >=1. Both boundary factors must be retained.
example : (∑' jk : ℕ × ℕ,
    cubicAFEProgressionDyadicCutoff (d := 1) (by norm_num : 0 < 4) (-3) jk.1 jk.2 4) = 0 := by
  rw [(hasSum_cubicAFEProgressionDyadicCutoff_allReal (d := 1) (by norm_num : 0 < 4) (-3) 4).tsum_eq]
  have hy : cubicAFEProgressionRealSecond 1 4 (-3) 4 = 1 / 4 := by
    norm_num [cubicAFEProgressionRealSecond]
  rw [hy, cubicAFEDyadicLowerWeight_zero (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2), mul_zero]

#check (@hasSum_norm_cubicAFEProgressionDyadicKernel_allReal :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e) (δ : ℤ) (t x : ℝ),
    HasSum (fun jk : ℕ × ℕ ↦ ‖cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t x‖)
      (cubicAFEDyadicLowerWeight x *
        cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) *
          ‖cubicAFEProgressionPhysicalSummand W T X V d e δ t x‖))
