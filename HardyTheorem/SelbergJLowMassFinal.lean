import HardyTheorem.SelbergJMassIntegrability

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # Unconditional and parameter-uniform low mass bound -/

theorem selbergJLowMass_le_exp_one_mul_J_unconditional
    {delta G theta : ℝ} {X : ℕ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : 2 ≤ X) (hG : 1 < G) (htheta : 0 ≤ theta)
    (hscale : theta * Real.log G = 1) :
    (∫ x in Ioc 1 G,
      Complex.normSq (selbergPhysicalThetaKernel delta x X)) ≤
      Real.exp 1 * selbergJ delta 1 theta X := by
  exact selbergJLowMass_le_exp_one_mul_J
    hdelta hdelta1 hG htheta hscale
    (aestronglyMeasurableOn_selbergPhysicalThetaKernel_normSq
      hdelta hdelta1 hX)
    (integrableOn_selbergJ_weightedPhysicalNormSq
      hdelta hdelta1 htheta hX)

theorem exists_integral_normSq_selbergPhysicalThetaKernel_low_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ x in Ioc 1 ((X : ℝ) ^ a),
          Complex.normSq (selbergPhysicalThetaKernel delta x X)) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) *
            Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
  rcases exists_abs_selbergJ_le ha hc hcEight hac with ⟨C0, hC0, hJ⟩
  refine ⟨Real.exp 1 * C0, mul_nonneg (Real.exp_pos 1).le hC0, ?_⟩
  intro X delta hdelta hdelta1 hX hXexp hXpow hlogGtwo
  let G : ℝ := (X : ℝ) ^ a
  let theta : ℝ := 1 / Real.log G
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    exact Real.rpow_nonneg (Nat.cast_nonneg X) a
  have hlogGpos : 0 < Real.log G := by linarith
  have hGone : 1 < G :=
    (Real.log_pos_iff hGnonneg).mp hlogGpos
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
  have hJone := hJ X delta 1 theta hdelta hdelta1 hX hXexp hXpow
    (le_refl 1) hGone.le htheta hthetaHalf
  have htarget :
      delta ^ (-(1 / 2 : ℝ)) * (1 : ℝ) ^ (-theta) /
          (theta * Real.log (X : ℝ)) =
        delta ^ (-(1 / 2 : ℝ)) * Real.log G /
          Real.log (X : ℝ) := by
    rw [Real.one_rpow]
    dsimp [theta]
    field_simp [hlogGpos.ne']
  calc
    (∫ x in Ioc 1 ((X : ℝ) ^ a),
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
    _ = (Real.exp 1 * C0) *
        (delta ^ (-(1 / 2 : ℝ)) * Real.log G /
          Real.log (X : ℝ)) := by rw [htarget]; ring
    _ = _ := rfl

end HardyTheorem
