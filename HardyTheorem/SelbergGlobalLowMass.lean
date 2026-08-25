import HardyTheorem.SelbergJLowMassFinal

open Complex MeasureTheory Set

namespace HardyTheorem

/-!
# Selberg S3 low mass at the delta scale

The cutoff is `G = delta^(-2)`, but the `J` estimate is used only at the
base point `x = 1`.  This is the key distinction between S3 and the weighted
S2 tail estimate.
-/

theorem exists_integral_normSq_selbergPhysicalThetaKernel_delta_low_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log (delta ^ (-2 : ℝ)) →
        (∫ x in Ioc 1 (delta ^ (-2 : ℝ)),
          Complex.normSq (selbergPhysicalThetaKernel delta x X)) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
            Real.log (X : ℝ)) := by
  rcases exists_abs_selbergJ_le ha hc hcEight hac with ⟨C0, hC0, hJ⟩
  refine ⟨2 * Real.exp 1 * C0,
    mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) hC0, ?_⟩
  intro X delta hdelta hdelta1 hX hXexp hXpow hlogGtwo
  let G : ℝ := delta ^ (-2 : ℝ)
  let theta : ℝ := 1 / Real.log G
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact Real.rpow_nonneg hdelta.le _
  have hlogGpos : 0 < Real.log G := by
    dsimp only [G] at hlogGtwo ⊢
    linarith
  have hGone : 1 < G := (Real.log_pos_iff hG0).mp hlogGpos
  have htheta : 0 < theta := by
    dsimp [theta]
    positivity
  have hthetaHalf : theta ≤ 1 / 2 := by
    dsimp [theta]
    exact one_div_le_one_div_of_le (by norm_num) hlogGtwo
  have hscale : theta * Real.log G = 1 := by
    dsimp [theta]
    field_simp [hlogGpos.ne']
  have hlow := selbergJLowMass_le_exp_one_mul_J_unconditional
    hdelta hdelta1 hX hGone htheta.le hscale
  have hXone : 1 ≤ (X : ℝ) := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hbaseRange : (1 : ℝ) ≤ (X : ℝ) ^ a :=
    Real.one_le_rpow hXone ha
  have hJone := hJ X delta 1 theta hdelta hdelta1 hX hXexp hXpow
    (le_refl 1) hbaseRange htheta hthetaHalf
  have hlogG : Real.log G = 2 * Real.log (1 / delta) := by
    dsimp [G]
    rw [Real.log_rpow hdelta (-2), one_div, Real.log_inv]
    ring
  have htarget :
      delta ^ (-(1 / 2 : ℝ)) * (1 : ℝ) ^ (-theta) /
          (theta * Real.log (X : ℝ)) =
        delta ^ (-(1 / 2 : ℝ)) * Real.log G /
          Real.log (X : ℝ) := by
    rw [Real.one_rpow]
    dsimp [theta]
    field_simp [hlogGpos.ne']
  calc
    (∫ x in Ioc 1 (delta ^ (-2 : ℝ)),
        Complex.normSq (selbergPhysicalThetaKernel delta x X)) =
      ∫ x in Ioc 1 G,
        Complex.normSq (selbergPhysicalThetaKernel delta x X) := rfl
    _ ≤ Real.exp 1 * selbergJ delta 1 theta X := hlow
    _ ≤ Real.exp 1 * |selbergJ delta 1 theta X| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 *
        (C0 * (delta ^ (-(1 / 2 : ℝ)) * (1 : ℝ) ^ (-theta) /
          (theta * Real.log (X : ℝ)))) :=
      mul_le_mul_of_nonneg_left hJone (Real.exp_pos 1).le
    _ = (2 * Real.exp 1 * C0) *
        (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
          Real.log (X : ℝ)) := by
      rw [htarget, hlogG]
      ring

end HardyTheorem
