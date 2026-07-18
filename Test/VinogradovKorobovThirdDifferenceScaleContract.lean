import ZeroFreeRegion.VinogradovKorobov.ThirdDifferenceScale

namespace ZeroFreeRegion.VinogradovKorobov

example {h k x : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hk : 0 < k)
    (hhx : h ≤ x) (hkx : k ≤ x) :
    logSecondDifferenceDecrementFraction h k x ≤ 5 :=
  logSecondDifferenceDecrementFraction_le_five hx hh hk hhx hkx

example {h k x : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hk : 0 < k)
    (hhx : h ≤ x) (hkx : k ≤ x) :
    logSecondDifferenceDecrementFraction h k x ≤
      5 * h * k / x ^ 3 :=
  decrementFraction_le_five_mul_div_cube hx hh hk hhx hkx

example {h k x : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hk : 0 < k)
    (hhx : h ≤ x) (hkx : k ≤ x) :
    2 * h * k / (27 * x ^ 3) ≤
      logSecondDifferenceDecrementFraction h k x :=
  two_mul_div_twentySeven_cube_le_decrementFraction hx hh hk hhx hkx

example {h k x : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hk : 0 < k)
    (hhx : h ≤ x) (hkx : k ≤ x) :
    h * k / (81 * x ^ 3) ≤ logSecondDifferenceDecrement h k x :=
  div_eightyOne_cube_le_logSecondDifferenceDecrement hx hh hk hhx hkx

end ZeroFreeRegion.VinogradovKorobov
