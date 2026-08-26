import HardyTheorem.SelbergOffDiagonalArithmetic

open scoped BigOperators

namespace HardyTheorem

#check selberg_difference_of_squares_gap_le
#check selberg_arithmetic_progression_reciprocal_tail_le

example {A B L V : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : 0 < L) (hV : 0 < V) (hgap : B * L ≤ A * V) :
    A * (A * V - B * L) / (L ^ 2 * V) ≤
      A ^ 2 / L ^ 2 - B ^ 2 / V ^ 2 :=
  selberg_difference_of_squares_gap_le hA hB hL hV hgap

example {r d M : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) :
    (∑ j ∈ Finset.Icc 1 M, ((r + j * d : ℕ) : ℝ)⁻¹) ≤
      (d : ℝ)⁻¹ * (1 + Real.log (M : ℝ)) :=
  selberg_arithmetic_progression_reciprocal_tail_le hr hd M

end HardyTheorem
