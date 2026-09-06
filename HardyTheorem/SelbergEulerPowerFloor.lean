import HardyTheorem.SelbergEulerPowerSum
import Mathlib.Algebra.Order.Floor.Semiring

open Set Finset
open scoped BigOperators

namespace HardyTheorem

/-! # Passing Selberg's Euler power sum to a real floor cutoff. -/

theorem rpow_increment_div_le_left
    {theta x y : ℝ} (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hx0 : 0 < x) (hxy : x ≤ y) (hstep : y - x ≤ 1) :
    (y ^ theta - x ^ theta) / theta ≤ x ^ (theta - 1) := by
  rcases hxy.eq_or_lt with rfl | hxylt
  · simp only [sub_self, zero_div]
    exact Real.rpow_nonneg hx0.le _
  let f : ℝ → ℝ := fun t => t ^ theta
  have hdiff : DifferentiableOn ℝ f (Set.Icc x y) := by
    intro t ht
    exact (Real.differentiableAt_rpow_const_of_ne theta
      (ne_of_gt (hx0.trans_le ht.1))).differentiableWithinAt
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_deriv_eq_slope f hxylt hdiff.continuousOn
      (hdiff.mono Set.Ioo_subset_Icc_self)
  have hc0 : 0 < c := hx0.trans hc.1
  have hderiv : deriv f c = theta * c ^ (theta - 1) := by
    exact Real.deriv_rpow_const c theta
  rw [hderiv] at hcderiv
  dsimp [f] at hcderiv
  have hquot : (y ^ theta - x ^ theta) / theta =
      c ^ (theta - 1) * (y - x) := by
    calc
      (y ^ theta - x ^ theta) / theta =
          ((y ^ theta - x ^ theta) / (y - x)) * ((y - x) / theta) := by
        field_simp [htheta0.ne', sub_ne_zero.mpr hxylt.ne']
      _ = (theta * c ^ (theta - 1)) * ((y - x) / theta) := by
        rw [← hcderiv]
      _ = c ^ (theta - 1) * (y - x) := by
        field_simp [htheta0.ne']
  have hpow : c ^ (theta - 1) ≤ x ^ (theta - 1) :=
    Real.rpow_le_rpow_of_nonpos hx0 hc.1.le (by linarith)
  have hstep0 : 0 ≤ y - x := sub_nonneg.mpr hxylt.le
  rw [hquot]
  calc
    c ^ (theta - 1) * (y - x) ≤
        x ^ (theta - 1) * (y - x) := by gcongr
    _ ≤ x ^ (theta - 1) * 1 := by
      exact mul_le_mul_of_nonneg_left hstep
        (Real.rpow_nonneg hx0.le _)
    _ = x ^ (theta - 1) := mul_one _

noncomputable def selbergEulerFloorPowerSum (theta z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.floor z),
    (((n + 1 : ℕ) : ℝ) ^ (theta - 1))

noncomputable def selbergEulerFloorError (theta z : ℝ) : ℝ :=
  selbergEulerFloorPowerSum theta z -
    (z ^ theta + selbergEulerPowerConstant theta) / theta

theorem exists_selbergEulerFloorPowerSum_error
    {theta z : ℝ} (htheta0 : 0 < theta)
    (hthetaHalf : theta ≤ 1 / 2) (hz : 1 ≤ z) :
    ∃ E : ℝ,
      |E| ≤ z ^ (theta - 1) ∧
      selbergEulerFloorPowerSum theta z =
        (z ^ theta + selbergEulerPowerConstant theta) / theta + E := by
  let N := Nat.floor z
  obtain ⟨R, hR0, hRle, hsum⟩ :=
    exists_selbergEulerPowerSum_remainder htheta0 hthetaHalf N
  let D : ℝ := ((((N + 1 : ℕ) : ℝ) ^ theta - z ^ theta) / theta)
  let E : ℝ := D - R
  have hz0 : 0 < z := zero_lt_one.trans_le hz
  have hNz : (N : ℝ) ≤ z := by
    dsimp [N]
    exact Nat.floor_le hz0.le
  have hzN : z ≤ ((N + 1 : ℕ) : ℝ) := by
    have hlt : z < ((N + 1 : ℕ) : ℝ) := by
      simpa only [N, Nat.cast_add, Nat.cast_one] using
        (Nat.lt_floor_add_one z)
    exact hlt.le
  have hstep : ((N + 1 : ℕ) : ℝ) - z ≤ 1 := by
    push_cast
    linarith
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg
      (sub_nonneg.mpr (Real.rpow_le_rpow hz0.le hzN htheta0.le))
      htheta0.le
  have hDle : D ≤ z ^ (theta - 1) := by
    dsimp [D]
    exact rpow_increment_div_le_left htheta0 (by linarith)
      hz0 hzN hstep
  have hRleZ : R ≤ z ^ (theta - 1) := by
    exact hRle.trans
      (Real.rpow_le_rpow_of_nonpos hz0 hzN (by linarith))
  have hEabs : |E| ≤ z ^ (theta - 1) := by
    rw [abs_le]
    dsimp [E]
    constructor <;> linarith
  refine ⟨E, hEabs, ?_⟩
  unfold selbergEulerFloorPowerSum
  rw [show Nat.floor z = N by rfl, hsum]
  dsimp [E, D]
  field_simp [htheta0.ne']
  ring

theorem abs_selbergEulerFloorError_le
    {theta z : ℝ} (htheta0 : 0 < theta)
    (hthetaHalf : theta ≤ 1 / 2) (hz : 1 ≤ z) :
    |selbergEulerFloorError theta z| ≤ z ^ (theta - 1) := by
  obtain ⟨E, hE, hsum⟩ :=
    exists_selbergEulerFloorPowerSum_error htheta0 hthetaHalf hz
  have hEq : selbergEulerFloorError theta z = E := by
    unfold selbergEulerFloorError
    rw [hsum]
    ring
  rw [hEq]
  exact hE

theorem selbergEulerFloorPowerSum_eq_main_add_error
    {theta z : ℝ} :
    selbergEulerFloorPowerSum theta z =
      (z ^ theta + selbergEulerPowerConstant theta) / theta +
        selbergEulerFloorError theta z := by
  unfold selbergEulerFloorError
  ring

end HardyTheorem
