import HardyTheorem.SelbergJThetaAverageIdentity

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # The theta-averaged high logarithmic mass bound -/

theorem integral_Ioc_exp_neg_mul_le_inv
    {L : ℝ} (hL : 0 < L) :
    (∫ theta in Ioc (0 : ℝ) (1 / 2), Real.exp (-L * theta)) ≤ 1 / L := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  let A : ℝ → ℝ := fun theta => -Real.exp (-L * theta) / L
  have hder : ∀ theta : ℝ,
      HasDerivAt A (Real.exp (-L * theta)) theta := by
    intro theta
    simpa [A, hL.ne'] using
      (((hasDerivAt_id theta).const_mul (-L)).exp.const_mul (-1)).div_const L
  have hint : IntervalIntegrable
      (fun theta : ℝ => Real.exp (-L * theta)) volume 0 (1 / 2) :=
    (by fun_prop : Continuous
      (fun theta : ℝ => Real.exp (-L * theta))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun theta _h => hder theta) hint]
  dsimp [A]
  have hexp : 0 ≤ Real.exp (-L / 2) := (Real.exp_pos _).le
  have hform :
      -Real.exp (-L * (1 / 2)) / L - -Real.exp (-L * 0) / L =
        (1 - Real.exp (-L / 2)) / L := by
    simp only [mul_zero, neg_zero, Real.exp_zero]
    congr 1
    ring
  rw [hform]
  exact div_le_div_of_nonneg_right (by linarith) hL.le

theorem exists_integral_normSq_selbergPhysicalThetaKernel_high_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ x in Ioi ((X : ℝ) ^ a),
          Complex.normSq (selbergPhysicalThetaKernel delta x X) /
            Real.log x ^ 2) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) /
            (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
  rcases exists_abs_selbergJ_le ha hc hcEight hac with ⟨C0, hC0, hJ⟩
  let k : ℝ := 1 - 2 / Real.exp 1
  have hk : 0 < k := by
    dsimp [k]
    exact one_sub_two_div_exp_one_pos
  refine ⟨C0 / k, div_nonneg hC0 hk.le, ?_⟩
  intro X delta hdelta hdelta1 hX hXexp hXpow hlogGtwo
  let G : ℝ := (X : ℝ) ^ a
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (1 / 2))
  let μ : Measure ℝ := volume.restrict (Ioi G)
  let q : ℝ → ℝ := fun x =>
    Complex.normSq (selbergPhysicalThetaKernel delta x X)
  let r : ℝ → ℝ := fun x => q x / Real.log x ^ 2
  let w : ℝ → ℝ := fun x => q x * selbergThetaAverageKernel (Real.log x)
  let L : ℝ := Real.log G
  let A : ℝ := C0 * delta ^ (-(1 / 2 : ℝ)) / Real.log (X : ℝ)
  let B : ℝ → ℝ := fun theta => A * Real.exp (-L * theta)
  have hGnonneg : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg X) a
  have hLtwo : 2 ≤ L := by simpa only [L, G] using hlogGtwo
  have hL : 0 < L := by linarith
  have hGone : 1 < G := (Real.log_pos_iff hGnonneg).mp hL
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    exact Real.log_pos
      (lt_of_lt_of_le (lt_trans one_lt_two Real.exp_one_gt_two) hXexp)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hqInt : Integrable q μ := by
    change IntegrableOn q (Ioi G)
    exact (integrableOn_selbergPhysicalThetaKernel_normSq
      hdelta hdelta1 hX).mono_set (fun _x hx => hGone.le.trans_lt hx)
  have hfactorMeas : AEStronglyMeasurable
      (fun x : ℝ => 1 / Real.log x ^ 2) μ :=
    (measurable_const.div (Real.measurable_log.pow_const 2)).aestronglyMeasurable
  have hrInt : Integrable r μ := by
    have hmul := hqInt.mul_bdd hfactorMeas
      (show ∀ᵐ x ∂μ, ‖1 / Real.log x ^ 2‖ ≤ (1 : ℝ) by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hlogx : 2 ≤ Real.log x := by
          have hxpos : x ∈ Ioi (0 : ℝ) :=
            (zero_lt_one.trans hGone).trans hx
          have hstrict := Real.strictMonoOn_log
            (zero_lt_one.trans hGone) hxpos hx
          exact hLtwo.trans (by simpa only [L] using hstrict.le)
        have hden : 0 < Real.log x ^ 2 := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · rw [div_le_one hden]
          nlinarith
        · exact div_nonneg zero_le_one hden.le)
    simpa [r, q, div_eq_mul_inv] using hmul
  have hprod := integrable_selbergJThetaAverageProduct
    ha hc hcEight hac hdelta hdelta1 hX hXexp hXpow hlogGtwo
  have hwInt : Integrable w μ := by
    have hraw := hprod.integral_prod_right
    apply hraw.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change (∫ theta in Ioc (0 : ℝ) (1 / 2),
      selbergJThetaAverageProduct delta X (theta, x)) = w x
    simpa only [w, q] using
      integral_selbergJThetaAverageProduct_theta_section_eq hx hGone.le
  have hmassKernel : k * (∫ x, r x ∂μ) ≤ ∫ x, w x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hrInt.const_mul k) hwInt
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : x ∈ Ioi (0 : ℝ) :=
      (zero_lt_one.trans hGone).trans hx
    have hstrict := Real.strictMonoOn_log
      (zero_lt_one.trans hGone) hxpos hx
    have hlogx : 2 ≤ Real.log x :=
      hLtwo.trans (by simpa only [L] using hstrict.le)
    have hkernel :=
      one_sub_two_div_exp_one_div_sq_le_selbergThetaAverageKernel hlogx
    have hq : 0 ≤ q x := Complex.normSq_nonneg _
    dsimp [r, w, k]
    convert mul_le_mul_of_nonneg_left hkernel hq using 1 <;> ring
  have hthetaInt : Integrable
      (fun theta => theta * selbergJ delta G theta X) ν := by
    have hraw := hprod.integral_prod_left
    apply hraw.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
    change (∫ x in Ioi G,
      selbergJThetaAverageProduct delta X (theta, x)) = _
    exact integral_selbergJThetaAverageProduct_section_eq
      (X := X) hdelta hdelta1 hGone.le htheta.1
  have hBint : Integrable B ν := by
    change IntegrableOn B (Ioc (0 : ℝ) (1 / 2))
    exact ((by fun_prop : Continuous B).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hJleB : ∀ᵐ theta ∂ν,
      theta * selbergJ delta G theta X ≤ B theta := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
    have hthetaPos : 0 < theta := htheta.1
    have hJtheta := hJ X delta G theta hdelta hdelta1 hX hXexp hXpow
      hGone.le (le_refl G) hthetaPos htheta.2
    calc
      theta * selbergJ delta G theta X ≤
          theta * |selbergJ delta G theta X| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hthetaPos.le
      _ ≤ theta * (C0 *
          (delta ^ (-(1 / 2 : ℝ)) * G ^ (-theta) /
            (theta * Real.log (X : ℝ)))) :=
        mul_le_mul_of_nonneg_left hJtheta hthetaPos.le
      _ = B theta := by
        dsimp [B, A, L]
        rw [Real.rpow_def_of_pos (zero_lt_one.trans hGone)]
        field_simp [hthetaPos.ne', hlogXpos.ne']
  have hJupper :
      (∫ theta, theta * selbergJ delta G theta X ∂ν) ≤ A / L := by
    calc
      (∫ theta, theta * selbergJ delta G theta X ∂ν) ≤
          ∫ theta, B theta ∂ν :=
        integral_mono_ae hthetaInt hBint hJleB
      _ = A * (∫ theta in Ioc (0 : ℝ) (1 / 2),
          Real.exp (-L * theta)) := by
        dsimp [ν, B]
        rw [integral_const_mul]
      _ ≤ A * (1 / L) :=
        mul_le_mul_of_nonneg_left (integral_Ioc_exp_neg_mul_le_inv hL) hA
      _ = A / L := by ring
  have hid := integral_theta_mul_selbergJ_eq_integral_normSq_mul_thetaAverageKernel
    ha hc hcEight hac hdelta hdelta1 hX hXexp hXpow hlogGtwo
  have hcombined : k * (∫ x, r x ∂μ) ≤ A / L := by
    calc
      k * (∫ x, r x ∂μ) ≤ ∫ x, w x ∂μ := hmassKernel
      _ = ∫ theta, theta * selbergJ delta G theta X ∂ν := by
        symm
        simpa only [ν, μ, G, w, q] using hid
      _ ≤ A / L := hJupper
  have hmass : (∫ x, r x ∂μ) ≤ (A / L) / k := by
    apply (le_div_iff₀ hk).2
    simpa only [mul_comm] using hcombined
  change (∫ x, r x ∂μ) ≤ _
  calc
    (∫ x, r x ∂μ) ≤ (A / L) / k := hmass
    _ = (C0 / k) *
        (delta ^ (-(1 / 2 : ℝ)) /
          (Real.log G * Real.log (X : ℝ))) := by
      dsimp [A, L]
      field_simp [hk.ne', hL.ne', hlogXpos.ne']
    _ = _ := rfl

end HardyTheorem
