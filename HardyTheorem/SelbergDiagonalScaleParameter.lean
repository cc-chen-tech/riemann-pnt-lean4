import HardyTheorem.SelbergDiagonalCoefficientParameter

namespace HardyTheorem

/-! # Exact power absorption for Selberg's signed `S(theta)` main term. -/

theorem selbergDiagonalThetaScale_identity
    {delta x Y theta : ℝ} (hdelta : 0 < delta)
    (hx : 0 < x) (hY : 0 < Y) :
    delta ^ ((theta - 1) / 2) * Y ^ (2 * theta) =
      delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) *
        (delta ^ (1 / 2 : ℝ) * Y ^ 2 * x) ^ theta := by
  have hdhalf0 : 0 ≤ delta ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hdelta.le _
  have hYsq0 : 0 ≤ Y ^ (2 : ℕ) := sq_nonneg Y
  rw [Real.mul_rpow (mul_nonneg hdhalf0 hYsq0) hx.le]
  rw [Real.mul_rpow hdhalf0 hYsq0]
  rw [← Real.rpow_mul hdelta.le]
  rw [← Real.rpow_natCast Y 2, ← Real.rpow_mul hY.le]
  calc
    delta ^ ((theta - 1) / 2) * Y ^ (2 * theta) =
        (delta ^ (-(1 / 2 : ℝ)) * delta ^ ((1 / 2) * theta)) *
          (x ^ (-theta) * x ^ theta) * Y ^ (2 * theta) := by
      rw [← Real.rpow_add hdelta, ← Real.rpow_add hx]
      have hxexp : -theta + theta = 0 := by ring
      have hdexp : -(1 / 2 : ℝ) + (1 / 2) * theta =
          (theta - 1) / 2 := by ring
      rw [hxexp, Real.rpow_zero, mul_one, hdexp]
    _ = delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) *
        (delta ^ ((1 / 2) * theta) * Y ^ (2 * theta) * x ^ theta) := by
      ring

theorem selbergDiagonalThetaScale_le
    {delta x Y theta : ℝ} (hdelta : 0 < delta)
    (hx : 0 < x) (hY : 0 < Y) (htheta : 0 ≤ theta)
    (hgate : delta ^ (1 / 2 : ℝ) * Y ^ 2 * x ≤ 1) :
    delta ^ ((theta - 1) / 2) * Y ^ (2 * theta) ≤
      delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) := by
  rw [selbergDiagonalThetaScale_identity hdelta hx hY]
  have hA0 : 0 ≤ delta ^ (1 / 2 : ℝ) * Y ^ 2 * x := by positivity
  have hArpow :
      (delta ^ (1 / 2 : ℝ) * Y ^ 2 * x) ^ theta ≤ 1 :=
    Real.rpow_le_one hA0 hgate htheta
  exact mul_le_of_le_one_right
    (mul_nonneg (Real.rpow_nonneg hdelta.le _)
      (Real.rpow_nonneg hx.le _)) hArpow

theorem selbergDiagonalMainGate_of_parameters
    {delta x a c : ℝ} {X : ℕ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : 1 ≤ X) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hXpow : (X : ℝ) ≤ delta ^ (-c))
    (hxX : x ≤ (X : ℝ) ^ a)
    (hac : (a + 2) * c ≤ 1 / 4) :
    delta ^ (1 / 2 : ℝ) * (X : ℝ) ^ 2 * x ≤ 1 := by
  have hX0 : 0 < (X : ℝ) := by exact_mod_cast hX
  have hXnonneg : 0 ≤ (X : ℝ) := hX0.le
  have hdneg0 : 0 < delta ^ (-c) := Real.rpow_pos_of_pos hdelta _
  have ha2 : 0 ≤ a + 2 := by linarith
  have hpowX : (X : ℝ) ^ (a + 2) ≤
      (delta ^ (-c)) ^ (a + 2) :=
    Real.rpow_le_rpow hXnonneg hXpow ha2
  have hexp0 : 0 ≤ (1 / 2 : ℝ) - c * (a + 2) := by
    nlinarith
  calc
    delta ^ (1 / 2 : ℝ) * (X : ℝ) ^ 2 * x ≤
        delta ^ (1 / 2 : ℝ) * (X : ℝ) ^ 2 * (X : ℝ) ^ a :=
      mul_le_mul_of_nonneg_left hxX (by positivity)
    _ = delta ^ (1 / 2 : ℝ) *
        ((X : ℝ) ^ 2 * (X : ℝ) ^ a) := by ring
    _ = delta ^ (1 / 2 : ℝ) * (X : ℝ) ^ (a + 2) := by
      rw [show (X : ℝ) ^ (2 : ℕ) = (X : ℝ) ^ (2 : ℝ) by
        exact (Real.rpow_natCast (X : ℝ) 2).symm]
      rw [← Real.rpow_add hX0]
      congr 2
      ring
    _ ≤ delta ^ (1 / 2 : ℝ) * (delta ^ (-c)) ^ (a + 2) := by
      gcongr
    _ = delta ^ ((1 / 2 : ℝ) - c * (a + 2)) := by
      rw [← Real.rpow_mul hdelta.le, ← Real.rpow_add hdelta]
      congr 1
      ring
    _ ≤ 1 := Real.rpow_le_one hdelta.le hdelta1 hexp0

theorem selbergDiagonalSZeroContribution_le
    {C delta x theta Y : ℝ} (hC : 0 ≤ C)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 0 < x) (htheta : 0 < theta) (hlogY : 0 < Real.log Y) :
    |selbergDiagonalSZeroCoefficient delta x theta| *
        (C / Real.log Y) ≤
      (Real.sqrt Real.pi / 2 * C) *
        (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log Y)) := by
  have hcoef := abs_selbergDiagonalSZeroCoefficient_le
    hdelta hdelta1 hx htheta
  calc
    |selbergDiagonalSZeroCoefficient delta x theta| *
        (C / Real.log Y) ≤
      ((Real.sqrt Real.pi / 2) * delta ^ (-(1 / 2 : ℝ)) *
        x ^ (-theta) / theta) * (C / Real.log Y) := by
      gcongr
    _ = (Real.sqrt Real.pi / 2 * C) *
        (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log Y)) := by ring

theorem selbergDiagonalSThetaContribution_le
    {C delta x theta Y : ℝ} (hC : 0 ≤ C)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 0 < x) (hY : 0 < Y) (hlogY : 0 < Real.log Y)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (hgate : delta ^ (1 / 2 : ℝ) * Y ^ 2 * x ≤ 1) :
    |selbergDiagonalSThetaCoefficient delta theta| *
        (C * Y ^ (2 * theta) / Real.log Y) ≤
      ((1 / 2 * Real.Gamma (1 / 4)) * C) *
        (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log Y)) := by
  have hcoef := abs_selbergDiagonalSThetaCoefficient_le
    hdelta hdelta1 htheta0 hthetaHalf
  have hscale := selbergDiagonalThetaScale_le hdelta hx hY
    htheta0.le hgate
  have hK0 : 0 ≤ (1 / 2 : ℝ) * Real.Gamma (1 / 4) := by positivity
  calc
    |selbergDiagonalSThetaCoefficient delta theta| *
        (C * Y ^ (2 * theta) / Real.log Y) ≤
      (((1 / 2 * Real.Gamma (1 / 4)) / theta) *
        delta ^ ((theta - 1) / 2)) *
          (C * Y ^ (2 * theta) / Real.log Y) := by
      gcongr
    _ = ((1 / 2 * Real.Gamma (1 / 4)) * C /
          (theta * Real.log Y)) *
        (delta ^ ((theta - 1) / 2) * Y ^ (2 * theta)) := by ring
    _ ≤ ((1 / 2 * Real.Gamma (1 / 4)) * C /
          (theta * Real.log Y)) *
        (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta)) := by
      gcongr
    _ = ((1 / 2 * Real.Gamma (1 / 4)) * C) *
        (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
          (theta * Real.log Y)) := by ring

end HardyTheorem
