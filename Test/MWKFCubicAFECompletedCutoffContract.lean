import PrimeNumberTheorem.MWKFCubicAFECompletedCutoff

open PrimeNumberTheorem.MWKFCubic

#check cubicAFEProgressionCompletedCutoff
#check tsupport_cubicAFEProgressionCompletedCutoff_subset
#check hasSum_cubicAFEProgressionCompletedCutoff
#check cubicAFEProgressionCompletedCutoff_shift
#check cubicAFEProgressionCompletedCutoff_zero_on_progression

-- Old boxes retain their exact physical cutoffs after reindexing.
example (J j k : ℕ) (x : ℝ) :
    cubicAFEProgressionCompletedCutoff (d := 2) (by norm_num : 0 < 4) (-6) J
      (J + j) (J + k) x =
        cubicAFEProgressionDyadicCutoff (d := 2) (by norm_num : 0 < 4) (-6) j k x :=
  cubicAFEProgressionCompletedCutoff_shift _ _ _ _ _ _

-- Lower scales vanish on positive integer-sized inputs, including the endpoint.
example : cubicAFEDyadicWindow 2 ((2 : ℝ)^3 * 1) = 0 :=
  cubicAFEDyadicWindow_zero_of_lower_scale (by norm_num : 2 < 3) (by norm_num)

-- No positivity assumption on the shift and no coprimality of shift and modulus.
example (J : ℕ) {m : ℕ} (hm : m ∈ cubicAFEProgression 2 4 (-6)) :
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEProgressionCompletedCutoff (d := 2)
      (by norm_num : 0 < 4) (-6) J jk.1 jk.2 m) 1 :=
  hasSum_cubicAFEProgressionCompletedCutoff _ hm J

-- A lower-scale real box is nonzero even though every positive lattice value is zero.
example : cubicAFEProgressionCompletedCutoff (d := 1) (by norm_num : 0 < 1)
    0 2 0 0 (1 / 4) = 1 := by
  norm_num [cubicAFEProgressionCompletedCutoff, cubicAFEProgressionRealSecond, cubicAFEDyadicWindow]

example : cubicAFEProgressionDyadicCutoff (d := 1) (by norm_num : 0 < 1) 0 0 0 (1 / 4) = 0 := by
  change cubicAFEDyadicWindow 0 (1 / 4) * _ = 0
  rw [cubicAFEDyadicWindow_zero_of_le_half 0 (by norm_num), zero_mul]
