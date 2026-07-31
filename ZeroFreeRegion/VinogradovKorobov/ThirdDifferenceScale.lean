import ZeroFreeRegion.VinogradovKorobov.HigherLogDifference

namespace ZeroFreeRegion.VinogradovKorobov

/-- On the natural A-process scale `0 < h,k ≤ x`, the rational argument of
the third logarithmic difference is uniformly bounded. -/
lemma logSecondDifferenceDecrementFraction_le_five
    {h k x : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hk : 0 < k)
    (hhx : h ≤ x) (hkx : k ≤ x) :
    logSecondDifferenceDecrementFraction h k x ≤ 5 := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hhk : h * k ≤ x * x :=
    mul_le_mul hhx hkx hk.le hxpos.le
  have hlinear : 2 * x + h + k + 1 ≤ 5 * x := by linarith
  have hnum :
      h * k * (2 * x + h + k + 1) ≤ 5 * x ^ 3 := by
    calc
      h * k * (2 * x + h + k + 1) ≤ (x * x) * (5 * x) :=
        mul_le_mul hhk hlinear (by positivity) (by positivity)
      _ = 5 * x ^ 3 := by ring
  have hfirst : x * x ≤ (x + 1) * (x + h + k + 1) := by
    gcongr <;> linarith
  have hbracket :
      x * x ≤ (x + 1) * (x + h + k + 1) + h * k :=
    hfirst.trans (le_add_of_nonneg_right (mul_nonneg hh.le hk.le))
  have hleft : x * x ≤ x * (x + h + k) := by
    exact mul_le_mul le_rfl (by linarith) hxpos.le hxpos.le
  have hdenLower :
      x ^ 4 ≤
        x * (x + h + k) *
          ((x + 1) * (x + h + k + 1) + h * k) := by
    calc
      x ^ 4 = (x * x) * (x * x) := by ring
      _ ≤ x * (x + h + k) *
          ((x + 1) * (x + h + k + 1) + h * k) :=
        mul_le_mul hleft hbracket (by positivity) (by positivity)
  have hcube : x ^ 3 ≤ x ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg hxpos.le 3) (sub_nonneg.mpr hx)]
  have hden :
      0 < x * (x + h + k) *
        ((x + 1) * (x + h + k + 1) + h * k) := by positivity
  unfold logSecondDifferenceDecrementFraction
  apply (div_le_iff₀ hden).2
  calc
    h * k * (2 * x + h + k + 1) ≤ 5 * x ^ 3 := hnum
    _ ≤ 5 * x ^ 4 := by gcongr
    _ ≤ 5 *
        (x * (x + h + k) *
          ((x + 1) * (x + h + k + 1) + h * k)) := by
      gcongr

/-- Scale-sensitive upper bound complementary to the uniform bound above. -/
lemma decrementFraction_le_five_mul_div_cube
    {h k x : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hk : 0 < k)
    (hhx : h ≤ x) (hkx : k ≤ x) :
    logSecondDifferenceDecrementFraction h k x ≤
      5 * h * k / x ^ 3 := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlinear : 2 * x + h + k + 1 ≤ 5 * x := by linarith
  have hnum :
      h * k * (2 * x + h + k + 1) ≤ 5 * h * k * x := by
    nlinarith [mul_nonneg (mul_nonneg hh.le hk.le)
      (sub_nonneg.mpr hlinear)]
  have hfirst : x * x ≤ (x + 1) * (x + h + k + 1) := by
    gcongr <;> linarith
  have hbracket :
      x * x ≤ (x + 1) * (x + h + k + 1) + h * k :=
    hfirst.trans (le_add_of_nonneg_right (mul_nonneg hh.le hk.le))
  have hleft : x * x ≤ x * (x + h + k) := by
    exact mul_le_mul le_rfl (by linarith) hxpos.le hxpos.le
  have hdenLower :
      x ^ 4 ≤
        x * (x + h + k) *
          ((x + 1) * (x + h + k + 1) + h * k) := by
    calc
      x ^ 4 = (x * x) * (x * x) := by ring
      _ ≤ x * (x + h + k) *
          ((x + 1) * (x + h + k + 1) + h * k) :=
        mul_le_mul hleft hbracket (by positivity) (by positivity)
  have hdenPos :
      0 < x * (x + h + k) *
        ((x + 1) * (x + h + k + 1) + h * k) := by positivity
  unfold logSecondDifferenceDecrementFraction
  apply (div_le_div_iff₀ hdenPos (pow_pos hxpos 3)).2
  calc
    (h * k * (2 * x + h + k + 1)) * x ^ 3 ≤
        (5 * h * k * x) * x ^ 3 :=
      mul_le_mul_of_nonneg_right hnum (pow_nonneg hxpos.le 3)
    _ = (5 * h * k) * x ^ 4 := by ring
    _ ≤ (5 * h * k) *
        (x * (x + h + k) *
          ((x + 1) * (x + h + k + 1) + h * k)) :=
      mul_le_mul_of_nonneg_left hdenLower (by positivity)

/-- Matching lower bound for the rational argument of the third logarithmic
difference. -/
lemma two_mul_div_twentySeven_cube_le_decrementFraction
    {h k x : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hk : 0 < k)
    (hhx : h ≤ x) (hkx : k ≤ x) :
    2 * h * k / (27 * x ^ 3) ≤
      logSecondDifferenceDecrementFraction h k x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hhk : h * k ≤ x * x :=
    mul_le_mul hhx hkx hk.le hxpos.le
  have hnumLower :
      2 * h * k * x ≤ h * k * (2 * x + h + k + 1) := by
    nlinarith [mul_nonneg (mul_nonneg hh.le hk.le)
      (by positivity : 0 ≤ h + k + 1)]
  have hsum : x + h + k ≤ 3 * x := by linarith
  have hxone : x + 1 ≤ 2 * x := by linarith
  have hsumone : x + h + k + 1 ≤ 4 * x := by linarith
  have hproduct :
      (x + 1) * (x + h + k + 1) ≤ (2 * x) * (4 * x) :=
    mul_le_mul hxone hsumone (by positivity) (by positivity)
  have hbracket :
      (x + 1) * (x + h + k + 1) + h * k ≤ 9 * x ^ 2 := by
    calc
      (x + 1) * (x + h + k + 1) + h * k ≤
          (2 * x) * (4 * x) + x * x := add_le_add hproduct hhk
      _ = 9 * x ^ 2 := by ring
  have hdenUpper :
      x * (x + h + k) *
          ((x + 1) * (x + h + k + 1) + h * k) ≤
        27 * x ^ 4 := by
    calc
      x * (x + h + k) *
          ((x + 1) * (x + h + k + 1) + h * k) ≤
          x * (3 * x) * (9 * x ^ 2) := by
        gcongr
      _ = 27 * x ^ 4 := by ring
  have hdenPos :
      0 < x * (x + h + k) *
        ((x + 1) * (x + h + k + 1) + h * k) := by positivity
  have hscalePos : 0 < 27 * x ^ 4 := by positivity
  rw [show 2 * h * k / (27 * x ^ 3) =
      (2 * h * k * x) / (27 * x ^ 4) by
    field_simp]
  unfold logSecondDifferenceDecrementFraction
  apply (div_le_div_iff₀ hscalePos hdenPos).2
  calc
    (2 * h * k * x) *
        (x * (x + h + k) *
          ((x + 1) * (x + h + k + 1) + h * k)) ≤
        (h * k * (2 * x + h + k + 1)) *
          (x * (x + h + k) *
            ((x + 1) * (x + h + k + 1) + h * k)) := by
      gcongr
    _ ≤ (h * k * (2 * x + h + k + 1)) * (27 * x ^ 4) := by
      gcongr

/-- Coarse but scale-correct lower bound for the third finite difference of
`log`: its magnitude is at least `h k / (81 x^3)`. -/
theorem div_eightyOne_cube_le_logSecondDifferenceDecrement
    {h k x : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hk : 0 < k)
    (hhx : h ≤ x) (hkx : k ≤ x) :
    h * k / (81 * x ^ 3) ≤ logSecondDifferenceDecrement h k x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hfracPos : 0 < logSecondDifferenceDecrementFraction h k x := by
    unfold logSecondDifferenceDecrementFraction
    positivity
  have hfracFive := logSecondDifferenceDecrementFraction_le_five
    hx hh hk hhx hkx
  have hlower := two_mul_div_twentySeven_cube_le_decrementFraction
    hx hh hk hhx hkx
  calc
    h * k / (81 * x ^ 3) =
        (2 * h * k / (27 * x ^ 3)) / 6 := by
      field_simp
      ring
    _ ≤ logSecondDifferenceDecrementFraction h k x / 6 := by
      exact div_le_div_of_nonneg_right hlower (by norm_num)
    _ ≤ logSecondDifferenceDecrementFraction h k x /
          (1 + logSecondDifferenceDecrementFraction h k x) := by
      apply (div_le_div_iff₀ (by norm_num) (by positivity)).2
      nlinarith
    _ ≤ logSecondDifferenceDecrement h k x :=
      fraction_div_one_add_le_logSecondDifferenceDecrement hxpos hh hk

end ZeroFreeRegion.VinogradovKorobov
