import PrimeNumberTheorem.MWKFCubicAFEDiagonalMellinKernel

open PrimeNumberTheorem.MWKFCubic

#check cubicAFEDiagonalMellinMonomial_eq
#check hasSum_cubicAFEDiagonalMellinMonomial

-- The gcd factors must give lcm(6,10)=30, not 60 or 15.
example : Real.sqrt (((6 / Nat.gcd 6 10) * (10 / Nat.gcd 6 10) : ℕ) : ℝ) *
    Real.sqrt ((6 : ℝ) * 10) = (Nat.lcm 6 10 : ℝ) :=
  cubicAFEDiagonal_sqrt_normalization (by norm_num) (by norm_num)

-- The first positive scale is 1, not a term at 0 of the zeta series.
example (z : ℂ) : cubicAFEDiagonalMellinMonomial 1 1 0 z = 1 := by
  rw [cubicAFEDiagonalMellinMonomial_eq (by norm_num) (by norm_num)]
  norm_num

example : cubicAFEDiagonalMellinMonomial 6 10 0 0 = (1 / 30 : ℂ) := by
  rw [cubicAFEDiagonalMellinMonomial_eq (by norm_num) (by norm_num)]
  norm_num
