import HardyTheorem.SelbergDiagonalScaleParameter

namespace HardyTheorem

/-! # Scalar isolation of the diagonal remainder's parameter loss. -/

noncomputable def selbergDiagonalRemainderAbsorptionScale
    (delta x theta Y : ℝ) : ℝ :=
  delta ^ (1 / 2 : ℝ) * Y ^ 4 * x * Real.log Y *
    (3 + theta * Real.log (2 + Y ^ 4 / delta))

theorem selbergDiagonalRemainderScale_identity
    {delta x theta Y : ℝ} (hdelta : 0 < delta)
    (hx : 0 < x) (htheta : 0 < theta) (hlogY : 0 < Real.log Y) :
    Y ^ 4 *
        (3 * (x ^ (1 - theta) / theta) +
          x ^ (1 - theta) * Real.log (2 + Y ^ 4 / delta)) =
      (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log Y)) *
        selbergDiagonalRemainderAbsorptionScale delta x theta Y := by
  have hdCancel :
      delta ^ (-(1 / 2 : ℝ)) * delta ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hdelta]
    norm_num
  have hxCombine : x ^ (-theta) * x = x ^ (1 - theta) := by
    calc
      x ^ (-theta) * x = x ^ (-theta) * x ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = x ^ (-theta + 1) := by rw [Real.rpow_add hx]
      _ = x ^ (1 - theta) := by congr 1 <;> ring
  unfold selbergDiagonalRemainderAbsorptionScale
  symm
  calc
    (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log Y)) *
        (delta ^ (1 / 2 : ℝ) * Y ^ 4 * x * Real.log Y *
          (3 + theta * Real.log (2 + Y ^ 4 / delta))) =
      Y ^ 4 *
        (delta ^ (-(1 / 2 : ℝ)) * delta ^ (1 / 2 : ℝ)) *
        (x ^ (-theta) * x) *
        ((3 + theta * Real.log (2 + Y ^ 4 / delta)) / theta) := by
      field_simp [htheta.ne', hlogY.ne']
    _ = Y ^ 4 * x ^ (1 - theta) *
        ((3 + theta * Real.log (2 + Y ^ 4 / delta)) / theta) := by
      rw [hdCancel, hxCombine, mul_one]
    _ = Y ^ 4 *
        (3 * (x ^ (1 - theta) / theta) +
          x ^ (1 - theta) * Real.log (2 + Y ^ 4 / delta)) := by
      field_simp [htheta.ne']

theorem selbergDiagonalRemainderTerm_le_target
    {K delta x theta Y : ℝ} (hK : 0 ≤ K)
    (hdelta : 0 < delta) (hx : 0 < x)
    (htheta : 0 < theta) (hlogY : 0 < Real.log Y)
    (hscale : selbergDiagonalRemainderAbsorptionScale
      delta x theta Y ≤ K) :
    Y ^ 4 *
        (3 * (x ^ (1 - theta) / theta) +
          x ^ (1 - theta) * Real.log (2 + Y ^ 4 / delta)) ≤
      K * (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
        (theta * Real.log Y)) := by
  rw [selbergDiagonalRemainderScale_identity hdelta hx htheta hlogY]
  have htarget0 : 0 ≤ delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
      (theta * Real.log Y) := by positivity
  calc
    (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log Y)) *
        selbergDiagonalRemainderAbsorptionScale delta x theta Y ≤
      (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log Y)) * K :=
        mul_le_mul_of_nonneg_left hscale htarget0
    _ = K * (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
        (theta * Real.log Y)) := by ring

end HardyTheorem
