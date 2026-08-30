import PrimeNumberTheorem.MWKFCubicAFEProgression

open Filter MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

-- The negative shift must survive; nonintegral and nonpositive numerators
-- must not produce false positive solutions via integer division/toNat.
example : 2 ∈ cubicAFEProgression 6 10 (-1) := by unfold cubicAFEProgression; decide
example : 1 ∉ cubicAFEProgression 6 10 (-1) := by unfold cubicAFEProgression; decide
example : 1 ∉ cubicAFEProgression 6 10 (-8) := by unfold cubicAFEProgression; decide
example : 0 ∉ cubicAFEProgression 6 10 5 := by unfold cubicAFEProgression; decide
example : 5 ∉ cubicAFEProgression 7 7 (-5) := by unfold cubicAFEProgression; decide
example : 6 ∈ cubicAFEProgression 7 7 (-5) := by unfold cubicAFEProgression; decide
example : cubicAFEProgressionPair 6 10 (-1) 2 = (1, 0) := by decide
example : cubicAFEProgressionPair 6 10 2 1 = (0, 0) := by decide

-- No unproved bijection, summability, or analytic estimate is supplied.
#check (@tsum_cubicAFEShiftFiber_eq_progression :
  ∀ {d e : ℕ}, 0 < e → ∀ (δ : ℤ) (f : ℕ × ℕ → ℂ),
    (∑' p : cubicAFEShiftFiber d e δ, f p.val) =
      ∑' m : cubicAFEProgression d e δ, f (cubicAFEProgressionPair d e δ m.val))

#check (@cubicAFEShiftedMomentFinite_eq_progression :
  ∀ (W : CubicTestWeight) (T X V : ℝ),
    cubicAFEShiftedMomentFinite W T X V = cubicAFEProgressionMomentFinite W T X V)

-- Solving the congruence must expose the negative sign in -delta*rbar.
#check (@cubicAFEProgression_mem_iff_residue :
  ∀ {d e : ℕ}, 0 < e → ∀ (δ : ℤ) (m : ℕ),
    m ∈ cubicAFEProgression d e δ ↔
      0 < m ∧ 0 < cubicAFEProgressionNumerator d e δ m ∧
        Int.ModEq ((e / Nat.gcd d e : ℕ) : ℤ) (m : ℤ)
          (-δ * Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e)))

-- Passing to the real physical kernel must use exact division, not a
-- floor/toNat approximation of the second positive index.
#check (@cubicAFEProgressionPair_second_cast :
  ∀ {d e : ℕ}, 0 < e → ∀ {δ : ℤ} {m : ℕ},
    m ∈ cubicAFEProgression d e δ →
      (((cubicAFEProgressionPair d e δ m).2 + 1 : ℕ) : ℝ) =
        ((δ : ℝ) + (m : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) /
          ((e / Nat.gcd d e : ℕ) : ℝ))

end PrimeNumberTheorem.MWKFCubic
