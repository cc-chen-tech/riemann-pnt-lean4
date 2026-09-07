import PrimeNumberTheorem.MWKFCubicAFEPhysicalKernel

open Complex Set
open scoped ContDiff

namespace PrimeNumberTheorem.MWKFCubic

#check cubicAFEProgressionRealSecond
#check cubicAFEProgressionRealProduct
#check cubicAFEProgressionDomain
#check cubicAFEProgressionPhysicalSummand
#check cubicAFEProgressionPhysicalSummand_eq_discrete
#check contDiffOn_cubicAFEProgressionPhysicalSummand

-- The continuous extension uses exact real division, not integer division.
example : cubicAFEProgressionRealSecond 6 10 (-1) (3 / 2) = 7 / 10 := by
  norm_num [cubicAFEProgressionRealSecond, Nat.gcd]

example : cubicAFEProgressionRealProduct 6 10 (-1) 2 = 2 := by
  norm_num [cubicAFEProgressionRealProduct, cubicAFEProgressionRealSecond, Nat.gcd]

-- Positivity is separate from the lattice congruence: x=1 is inside the
-- real domain even though it is not in the corresponding progression.
example : (1 : ℝ) ∈ cubicAFEProgressionDomain 6 10 (-1) := by
  norm_num [cubicAFEProgressionDomain, Nat.gcd]

example : (0 : ℝ) ∉ cubicAFEProgressionDomain 6 10 5 := by
  norm_num [cubicAFEProgressionDomain]

example : (8 / 3 : ℝ) ∉ cubicAFEProgressionDomain 6 10 (-8) := by
  norm_num [cubicAFEProgressionDomain, Nat.gcd]

example : (6 : ℝ) ∈ cubicAFEProgressionDomain 7 7 (-5) := by
  norm_num [cubicAFEProgressionDomain, Nat.gcd]

-- Exact equality with the original full summand prevents substituting a
-- convenient unrelated kernel or losing coefficients/phases.
#check (@cubicAFEProgressionPhysicalSummand_eq_discrete :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}, 0 < d → 0 < e →
    ∀ (t : ℝ) {δ : ℤ} {m : ℕ}, m ∈ cubicAFEProgression d e δ →
      cubicAFEProgressionPhysicalSummand W T X V d e δ t m =
        cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m))

#check (@contDiffOn_cubicAFEProgressionPhysicalSummand :
  ∀ (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}, 0 < d → 0 < e →
    ∀ (δ : ℤ) (t : ℝ), 1 / 2 < X →
      ContDiffOn ℝ ∞ (cubicAFEProgressionPhysicalSummand W T X V d e δ t)
        (cubicAFEProgressionDomain d e δ))

end PrimeNumberTheorem.MWKFCubic
