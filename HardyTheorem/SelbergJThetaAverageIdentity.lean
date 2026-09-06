import HardyTheorem.SelbergThetaAverageKernel
import Mathlib.MeasureTheory.Integral.Prod

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # Tonelli--Fubini identity for the high logarithmic tail -/

noncomputable def selbergJThetaAverageProduct
    (delta : ℝ) (X : ℕ) (p : ℝ × ℝ) : ℝ :=
  p.1 * Real.exp (Real.log p.2 * (-p.1)) *
    Complex.normSq (selbergPhysicalThetaKernel delta p.2 X)

theorem integral_selbergJThetaAverageProduct_section_eq
    {delta G theta : ℝ} {X : ℕ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hG : 1 ≤ G) (htheta : 0 < theta) :
    (∫ x in Ioi G,
      selbergJThetaAverageProduct delta X (theta, x)) =
      theta * selbergJ delta G theta X := by
  unfold selbergJ
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := zero_lt_one.trans_le (hG.trans hx.le)
  unfold selbergJThetaAverageProduct
  rw [Real.rpow_def_of_pos hxpos]
  rw [selbergPhysicalThetaKernel_eq_nonconstantThetaKernel_log
    hdelta hdelta1 hxpos]
  ring

theorem integral_norm_selbergJThetaAverageProduct_section_eq
    {delta G theta : ℝ} {X : ℕ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hG : 1 ≤ G) (htheta : 0 < theta) :
    (∫ x in Ioi G,
      ‖selbergJThetaAverageProduct delta X (theta, x)‖) =
      theta * selbergJ delta G theta X := by
  rw [← integral_selbergJThetaAverageProduct_section_eq
    hdelta hdelta1 hG htheta]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg]
  unfold selbergJThetaAverageProduct
  exact mul_nonneg
    (mul_nonneg htheta.le (Real.exp_pos _).le)
    (Complex.normSq_nonneg _)

theorem integrable_selbergJThetaAverageProduct
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4)
    {X : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : 2 ≤ X) (hXexp : Real.exp 1 ≤ (X : ℝ))
    (hXpow : (X : ℝ) ≤ delta ^ (-c))
    (hlogGtwo : 2 ≤ Real.log ((X : ℝ) ^ a)) :
    Integrable
      (selbergJThetaAverageProduct delta X)
      ((volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod
        (volume.restrict (Ioi ((X : ℝ) ^ a)))) := by
  let G : ℝ := (X : ℝ) ^ a
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (1 / 2))
  let μ : Measure ℝ := volume.restrict (Ioi G)
  let q : ℝ → ℝ := fun x =>
    Complex.normSq (selbergPhysicalThetaKernel delta x X)
  have hGnonneg : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg X) a
  have hlogGpos : 0 < Real.log G := by linarith
  have hGone : 1 < G := (Real.log_pos_iff hGnonneg).mp hlogGpos
  have hqInt : Integrable q μ := by
    change IntegrableOn q (Ioi G)
    exact (integrableOn_selbergPhysicalThetaKernel_normSq
      hdelta hdelta1 hX).mono_set (fun _x hx => hGone.le.trans_lt hx)
  have hqMeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => q p.2) (ν.prod μ) :=
    hqInt.aestronglyMeasurable.comp_snd
  have hfactorMeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => p.1 *
        Real.exp (Real.log p.2 * (-p.1))) (ν.prod μ) := by
    exact (by measurability : Measurable
      (fun p : ℝ × ℝ => p.1 *
        Real.exp (Real.log p.2 * (-p.1)))).aestronglyMeasurable
  have hprodMeas : AEStronglyMeasurable
      (selbergJThetaAverageProduct delta X) (ν.prod μ) := by
    unfold selbergJThetaAverageProduct
    exact hfactorMeas.mul hqMeas
  have hsections : ∀ᵐ theta ∂ν, Integrable
      (fun x => selbergJThetaAverageProduct delta X (theta, x)) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
    have hweighted := (integrableOn_selbergJ_weightedPhysicalNormSq
      hdelta hdelta1 htheta.1.le hX).mono_set
        (fun _x hx => hGone.le.trans_lt hx)
    have hbase := hweighted.const_mul theta
    apply hbase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := zero_lt_one.trans_le
      (hGone.le.trans (le_of_lt hx))
    unfold selbergJThetaAverageProduct
    rw [Real.rpow_def_of_pos hxpos]
    ring
  rcases exists_abs_selbergJ_le ha hc hcEight hac with ⟨C0, hC0, hJ⟩
  let A : ℝ := C0 * delta ^ (-(1 / 2 : ℝ)) / Real.log (X : ℝ)
  let B : ℝ → ℝ := fun theta =>
    A * Real.exp (Real.log G * (-theta))
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    exact Real.log_pos
      (lt_of_lt_of_le (lt_trans one_lt_two Real.exp_one_gt_two) hXexp)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hBint : Integrable B ν := by
    change IntegrableOn B (Ioc (0 : ℝ) (1 / 2))
    have hcont : Continuous B := by
      dsimp [B]
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hinnerMeas : AEStronglyMeasurable
      (fun theta => ∫ x, ‖selbergJThetaAverageProduct delta X (theta, x)‖ ∂μ)
      ν := hprodMeas.norm.integral_prod_right'
  have hinnerInt : Integrable
      (fun theta => ∫ x, ‖selbergJThetaAverageProduct delta X (theta, x)‖ ∂μ)
      ν := by
    apply hBint.mono' hinnerMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
    have hthetaPos : 0 < theta := htheta.1
    have hthetaHalf : theta ≤ 1 / 2 := htheta.2
    have hJtheta := hJ X delta G theta hdelta hdelta1 hX hXexp hXpow
      hGone.le (le_refl G) hthetaPos hthetaHalf
    have hsection := integral_norm_selbergJThetaAverageProduct_section_eq
      (X := X) hdelta hdelta1 hGone.le hthetaPos
    have hthetaJ : theta * selbergJ delta G theta X ≤
        B theta := by
      calc
        theta * selbergJ delta G theta X ≤
            theta * |selbergJ delta G theta X| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hthetaPos.le
        _ ≤ theta * (C0 *
            (delta ^ (-(1 / 2 : ℝ)) * G ^ (-theta) /
              (theta * Real.log (X : ℝ)))) :=
          mul_le_mul_of_nonneg_left hJtheta hthetaPos.le
        _ = B theta := by
          dsimp [B, A]
          rw [Real.rpow_def_of_pos (zero_lt_one.trans hGone)]
          field_simp [hthetaPos.ne', hlogXpos.ne']
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simpa only [μ, hsection] using hthetaJ
    · rw [hsection]
      exact mul_nonneg hthetaPos.le
        (setIntegral_nonneg measurableSet_Ioi fun x hx =>
          mul_nonneg
            (Real.rpow_nonneg
              (zero_lt_one.trans_le (hGone.le.trans (le_of_lt hx))).le _)
            (Complex.normSq_nonneg _))
  change Integrable (selbergJThetaAverageProduct delta X) (ν.prod μ)
  exact (integrable_prod_iff hprodMeas).2 ⟨hsections, hinnerInt⟩

theorem integral_selbergJThetaAverageProduct_theta_section_eq
    {delta G x : ℝ} {X : ℕ} (hx : G < x) (hG : 1 ≤ G) :
    (∫ theta in Ioc (0 : ℝ) (1 / 2),
      selbergJThetaAverageProduct delta X (theta, x)) =
      Complex.normSq (selbergPhysicalThetaKernel delta x X) *
        selbergThetaAverageKernel (Real.log x) := by
  have hxpos : 0 < x := zero_lt_one.trans_le (hG.trans hx.le)
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  unfold selbergThetaAverageKernel
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _htheta
  unfold selbergJThetaAverageProduct
  ring

theorem integral_theta_mul_selbergJ_eq_integral_normSq_mul_thetaAverageKernel
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4)
    {X : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : 2 ≤ X) (hXexp : Real.exp 1 ≤ (X : ℝ))
    (hXpow : (X : ℝ) ≤ delta ^ (-c))
    (hlogGtwo : 2 ≤ Real.log ((X : ℝ) ^ a)) :
    (∫ theta in Ioc (0 : ℝ) (1 / 2),
      theta * selbergJ delta ((X : ℝ) ^ a) theta X) =
      ∫ x in Ioi ((X : ℝ) ^ a),
        Complex.normSq (selbergPhysicalThetaKernel delta x X) *
          selbergThetaAverageKernel (Real.log x) := by
  let G : ℝ := (X : ℝ) ^ a
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (1 / 2))
  let μ : Measure ℝ := volume.restrict (Ioi G)
  have hGnonneg : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg X) a
  have hlogGpos : 0 < Real.log G := by linarith
  have hGone : 1 < G := (Real.log_pos_iff hGnonneg).mp hlogGpos
  have hprod := integrable_selbergJThetaAverageProduct
    ha hc hcEight hac hdelta hdelta1 hX hXexp hXpow hlogGtwo
  have hprodCurried : Integrable
      (Function.uncurry
        (fun theta x => selbergJThetaAverageProduct delta X (theta, x)))
      ((volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod
        (volume.restrict (Ioi ((X : ℝ) ^ a)))) := by
    apply hprod.congr
    exact Filter.Eventually.of_forall fun p => by cases p; rfl
  have hswap := integral_integral_swap
    (f := fun theta x => selbergJThetaAverageProduct delta X (theta, x))
    hprodCurried
  have hleft :
      (∫ theta, ∫ x,
        selbergJThetaAverageProduct delta X (theta, x) ∂μ ∂ν) =
      ∫ theta in Ioc (0 : ℝ) (1 / 2),
        theta * selbergJ delta G theta X := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
    change (∫ x in Ioi G,
      selbergJThetaAverageProduct delta X (theta, x)) = _
    exact integral_selbergJThetaAverageProduct_section_eq
      hdelta hdelta1 hGone.le htheta.1
  have hright :
      (∫ x, ∫ theta,
        selbergJThetaAverageProduct delta X (theta, x) ∂ν ∂μ) =
      ∫ x in Ioi G,
        Complex.normSq (selbergPhysicalThetaKernel delta x X) *
          selbergThetaAverageKernel (Real.log x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change (∫ theta in Ioc (0 : ℝ) (1 / 2),
      selbergJThetaAverageProduct delta X (theta, x)) = _
    exact integral_selbergJThetaAverageProduct_theta_section_eq hx hGone.le
  change (∫ theta in Ioc (0 : ℝ) (1 / 2),
      theta * selbergJ delta G theta X) = _
  calc
    _ = ∫ theta, ∫ x,
        selbergJThetaAverageProduct delta X (theta, x) ∂μ ∂ν := hleft.symm
    _ = ∫ x, ∫ theta,
        selbergJThetaAverageProduct delta X (theta, x) ∂ν ∂μ := hswap
    _ = _ := hright

end HardyTheorem
