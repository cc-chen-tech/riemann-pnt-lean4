import PrimeNumberTheorem.MWKFCubicAFELatticeDecay

open PrimeNumberTheorem.MWKFCubic

-- The translation b is an arbitrary real, including negative integers.
example {X s : ℝ} (hX : 1 / 2 < X) (hs : 1 ≤ s) (b : ℝ) :
    Summable (fun δ : ℤ ↦ cubicAFEDyadicLowerWeight (((δ : ℝ) + b) / s) *
      (((δ : ℝ) + b) / s) ^ (-X - 1 / 2)) :=
  summable_cubicAFELatticePower hX hs b

#check tsum_cubicAFELatticePower_le

-- Exact threshold at y=1/2: the zero boundary does not leave an n=0 singularity.
example : cubicAFEDyadicLowerWeight ((((-3 : ℤ) : ℝ) + 7 / 2) / 1) *
    ((((-3 : ℤ) : ℝ) + 7 / 2) / 1) ^ (-(1 : ℝ) - 1 / 2) = 0 := by
  rw [cubicAFEDyadicLowerWeight_zero (by norm_num), zero_mul]

example : Summable (fun δ : ℤ ↦ cubicAFEDyadicLowerWeight (((δ : ℝ) - 7 / 3) / 1) *
    (((δ : ℝ) - 7 / 3) / 1) ^ (-(1 : ℝ) - 1 / 2)) := by
  simpa only [sub_eq_add_neg] using
    summable_cubicAFELatticePower (X := 1) (s := 1) (by norm_num) (by norm_num) (-(7 / 3))
