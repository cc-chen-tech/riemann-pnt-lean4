import HardyTheorem.SelbergJKernelMassBridge

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # Low logarithmic mass from Selberg's true `J` -/

/-- A nonnegative mass on `[1,G]` is controlled by its `x^(-theta)` tail
when `theta * log G = 1`.  This is the direct positivity argument used in
place of differentiating `J`. -/
theorem integral_Ioc_le_exp_one_mul_integral_Ioi_rpow
    {q : ℝ → ℝ} {G theta : ℝ}
    (hG : 1 < G) (htheta : 0 ≤ theta)
    (hscale : theta * Real.log G = 1)
    (hq : ∀ x, 0 ≤ q x)
    (hqmeas : AEStronglyMeasurable q (volume.restrict (Ioc 1 G)))
    (hweighted : IntegrableOn
      (fun x : ℝ => x ^ (-theta) * q x) (Ioi 1)) :
    (∫ x in Ioc 1 G, q x) ≤
      Real.exp 1 *
        (∫ x in Ioi (1 : ℝ), x ^ (-theta) * q x) := by
  let w : ℝ → ℝ := fun x => x ^ (-theta) * q x
  have hsubset : Ioc (1 : ℝ) G ⊆ Ioi 1 := fun _x hx => hx.1
  have hfactor : ∀ x ∈ Ioc (1 : ℝ) G,
      1 ≤ Real.exp 1 * x ^ (-theta) := by
    intro x hx
    have hxpos : 0 < x := zero_lt_one.trans hx.1
    have hGpos : 0 < G := zero_lt_one.trans hG
    have hlogle : Real.log x ≤ Real.log G :=
      Real.log_le_log hxpos hx.2
    have hmul : theta * Real.log x ≤ 1 := by
      calc
        theta * Real.log x ≤ theta * Real.log G :=
          mul_le_mul_of_nonneg_left hlogle htheta
        _ = 1 := hscale
    rw [Real.rpow_def_of_pos hxpos]
    rw [← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  have hw_nonneg_of_pos : ∀ {x : ℝ}, 0 < x → 0 ≤ w x := by
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (hq x)
  have hpoint : ∀ x ∈ Ioc (1 : ℝ) G,
      q x ≤ Real.exp 1 * w x := by
    intro x hx
    dsimp [w]
    calc
      q x = 1 * q x := by ring
      _ ≤ (Real.exp 1 * x ^ (-theta)) * q x :=
        mul_le_mul_of_nonneg_right (hfactor x hx) (hq x)
      _ = Real.exp 1 * (x ^ (-theta) * q x) := by ring
  have hwIoc : IntegrableOn w (Ioc 1 G) :=
    hweighted.mono_set hsubset
  have hmajor : IntegrableOn (fun x => Real.exp 1 * w x) (Ioc 1 G) :=
    hwIoc.const_mul (Real.exp 1)
  have hqint : IntegrableOn q (Ioc 1 G) := by
    apply hmajor.mono' hqmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hq x)] using hpoint x hx
  calc
    (∫ x in Ioc 1 G, q x) ≤
        ∫ x in Ioc 1 G, Real.exp 1 * w x :=
      setIntegral_mono_on hqint hmajor measurableSet_Ioc hpoint
    _ = Real.exp 1 * (∫ x in Ioc 1 G, w x) := by
      rw [integral_const_mul]
    _ ≤ Real.exp 1 * (∫ x in Ioi (1 : ℝ), w x) := by
      have hset : (∫ x in Ioc 1 G, w x) ≤
          ∫ x in Ioi (1 : ℝ), w x := by
        apply setIntegral_mono_set hweighted
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact hw_nonneg_of_pos (zero_lt_one.trans hx)
        · exact ae_of_all volume hsubset
      exact mul_le_mul_of_nonneg_left hset (Real.exp_pos 1).le
    _ = _ := rfl

/-- Concrete low-mass bridge for the physical theta kernel.  The only
analytic side condition is genuine integrability of the weighted kernel;
the absolute-Fubini layer supplies that condition separately. -/
theorem selbergJLowMass_le_exp_one_mul_J
    {delta G theta : ℝ} {X : ℕ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hG : 1 < G) (htheta : 0 ≤ theta)
    (hscale : theta * Real.log G = 1)
    (hmeas : AEStronglyMeasurable
      (fun x : ℝ => Complex.normSq
        (selbergPhysicalThetaKernel delta x X))
      (volume.restrict (Ioc 1 G)))
    (hweighted : IntegrableOn
      (fun x : ℝ => x ^ (-theta) * Complex.normSq
        (selbergPhysicalThetaKernel delta x X)) (Ioi 1)) :
    (∫ x in Ioc 1 G,
      Complex.normSq (selbergPhysicalThetaKernel delta x X)) ≤
      Real.exp 1 * selbergJ delta 1 theta X := by
  have hmass := integral_Ioc_le_exp_one_mul_integral_Ioi_rpow
    hG htheta hscale
    (fun x => Complex.normSq_nonneg
      (selbergPhysicalThetaKernel delta x X)) hmeas hweighted
  calc
    (∫ x in Ioc 1 G,
        Complex.normSq (selbergPhysicalThetaKernel delta x X)) ≤
      Real.exp 1 *
        (∫ x in Ioi (1 : ℝ), x ^ (-theta) *
          Complex.normSq (selbergPhysicalThetaKernel delta x X)) := hmass
    _ = Real.exp 1 * selbergJ delta 1 theta X := by
      congr 1
      unfold selbergJ
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change x ^ (-theta) *
          Complex.normSq (selbergPhysicalThetaKernel delta x X) =
        x ^ (-theta) *
          Complex.normSq
            (selbergNonconstantThetaKernel delta X (Real.log x))
      rw [selbergPhysicalThetaKernel_eq_nonconstantThetaKernel_log
        hdelta hdelta1 (zero_lt_one.trans hx)]

end HardyTheorem
