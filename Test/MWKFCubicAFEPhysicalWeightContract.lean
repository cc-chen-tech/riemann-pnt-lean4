import PrimeNumberTheorem.MWKFCubicAFEPhysicalWeight

open Complex
open scoped ContDiff

namespace PrimeNumberTheorem.MWKFCubic

#check cubicAFELogProductWeightFinite
#check differentiable_cubicAFELogProductWeightFinite
#check cubicAFERealProductWeightFinite
#check cubicAFERealProductWeightFinite_natCast
#check contDiffOn_cubicAFERealProductWeightFinite

-- The actual weight, not a replacement function supplied by a hypothesis.
#check (@differentiable_cubicAFELogProductWeightFinite :
  ∀ t X V : ℝ, 1 / 2 < X →
    Differentiable ℂ (cubicAFELogProductWeightFinite t X V))

#check (@cubicAFERealProductWeightFinite_natCast :
  ∀ t X V : ℝ, ∀ {k : ℕ}, 0 < k →
    cubicAFERealProductWeightFinite t X V k = cubicAFEProductWeightFinite t X V k)

#check (@contDiffOn_cubicAFERealProductWeightFinite :
  ∀ t X V : ℝ, 1 / 2 < X →
    ContDiffOn ℝ ∞ (cubicAFERealProductWeightFinite t X V) (Set.Ioi 0))

-- Both orientations and the collapsed vertical interval remain admissible.
example (t X : ℝ) (hX : 1 / 2 < X) :
    ContDiffOn ℝ ∞ (cubicAFERealProductWeightFinite t X (-1)) (Set.Ioi 0) :=
  contDiffOn_cubicAFERealProductWeightFinite t X (-1) hX

example (t X : ℝ) (z : ℂ) : cubicAFELogProductWeightFinite t X 0 z = 0 := by
  simp [cubicAFELogProductWeightFinite]

example (t X V : ℝ) :
    cubicAFERealProductWeightFinite t X V 1 = cubicAFEProductWeightFinite t X V 1 := by
  simpa only [Nat.cast_one] using
    cubicAFERealProductWeightFinite_natCast t X V (by decide : 0 < (1 : ℕ))

end PrimeNumberTheorem.MWKFCubic
