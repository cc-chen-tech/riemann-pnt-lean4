import PrimeNumberTheorem.MWKFCubicAFEDyadicCutoff

open Set Filter
open scoped ContDiff Topology

namespace PrimeNumberTheorem.MWKFCubic

-- These contracts reject an arbitrary-cutoff interface: the dyadic windows
-- must actually be constructed, sum to one, and satisfy the stated scales.
#check cubicAFEDyadicWindow
#check contDiff_cubicAFEDyadicWindow
#check tsupport_cubicAFEDyadicWindow_subset
#check sum_cubicAFEDyadicWindow_range
#check hasSum_cubicAFEDyadicWindow
#check cubicAFEProgressionDyadicCutoff
#check cubicAFEProgressionDyadicCutoff_eq_discrete
#check hasSum_cubicAFEProgressionDyadicCutoff

-- Zero and negative arguments cannot enter a positive-index window.
example (j : ℕ) : cubicAFEDyadicWindow j 0 = 0 :=
  cubicAFEDyadicWindow_zero_of_le_half j (by positivity)
example (j : ℕ) : cubicAFEDyadicWindow j (-3) = 0 :=
  cubicAFEDyadicWindow_zero_of_le_half j (by
    have hp : (0 : ℝ) ≤ 2^j / 2 := by positivity
    linarith)

-- Independently fixed scale boundaries and center values.
example : cubicAFEDyadicWindow 0 1 = 1 := by norm_num [cubicAFEDyadicWindow]
example : cubicAFEDyadicWindow 1 2 = 1 := by norm_num [cubicAFEDyadicWindow]
example : cubicAFEDyadicWindow 0 2 = 0 := by norm_num [cubicAFEDyadicWindow]
example : cubicAFEDyadicWindow 1 1 = 0 := cubicAFEDyadicWindow_zero_of_le_half 1 (by norm_num)
example : cubicAFEDyadicWindow 2 2 = 0 := cubicAFEDyadicWindow_zero_of_le_half 2 (by norm_num)
example : cubicAFEDyadicWindow 2 8 = 0 := by norm_num [cubicAFEDyadicWindow]

-- The omitted lower-boundary term would make this expression equal one.
example (J : ℕ) : (∑ j ∈ Finset.range (J + 1), cubicAFEDyadicWindow j (1 / 4)) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  apply cubicAFEDyadicWindow_zero_of_le_half
  have hp : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  linarith

#check (@hasSum_cubicAFEDyadicWindow : ∀ {x : ℝ}, 1 ≤ x →
  HasSum (fun j : ℕ ↦ cubicAFEDyadicWindow j x) 1)

-- Both actual positive indices are powers of two in this fixture:
-- r=3, s=5, delta=-2, m=4, n=(-2+3*4)/5=2.
example : cubicAFEProgressionDyadicCutoff (d := 6) (by norm_num : 0 < 10) (-2) 2 1 4 = 1 := by
  norm_num [cubicAFEProgressionDyadicCutoff, cubicAFEProgressionRealSecond,
    cubicAFEDyadicWindow, Nat.gcd]

-- A positive first index alone does not suffice: n=(-8+3*2)/5 is negative.
example : cubicAFEProgressionDyadicCutoff (d := 6) (by norm_num : 0 < 10) (-8) 1 0 2 = 0 := by
  change cubicAFEDyadicWindow 1 2 * cubicAFEDyadicWindow 0 _ = 0
  rw [cubicAFEDyadicWindow_zero_of_le_half 0 (by
    norm_num [cubicAFEProgressionRealSecond, Nat.gcd]), mul_zero]

-- Arbitrary admissible progression integer, no partition hypothesis supplied.
#check (@hasSum_cubicAFEProgressionDyadicCutoff :
  ∀ {d e : ℕ} (he : 0 < e) {δ : ℤ} {m : ℕ},
    m ∈ cubicAFEProgression d e δ →
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 m) 1)

end PrimeNumberTheorem.MWKFCubic
