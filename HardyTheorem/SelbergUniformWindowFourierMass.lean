import HardyTheorem.SelbergExplicitFourierMass

open Complex MeasureTheory Set

namespace HardyTheorem

/-!
# Fourier-mass constants uniform in the window exponent

The final Selberg argument chooses the window exponent only after the S2
constant is known.  Consequently the nonconstant Fourier-mass constant must
be uniform for `0 < a ≤ 1`.  The existing pointwise `J` theorem at exponent
one already has precisely this uniformity, because `x ≤ X^a ≤ X`.
-/

/-- The `J` bound with one constant valid simultaneously for all
`0 ≤ a ≤ 1`, at the fixed mollifier exponent `c=1/32`. -/
theorem exists_abs_selbergJ_le_uniform_unit_window :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ), 0 ≤ a → a ≤ 1 →
      ∀ (X : ℕ) (delta x theta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-(1 / 32 : ℝ)) →
        1 ≤ x → x ≤ (X : ℝ) ^ a →
        0 < theta → theta ≤ 1 / 2 →
        |selbergJ delta x theta X| ≤
          C * (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
            (theta * Real.log (X : ℝ))) := by
  obtain ⟨C, hC, hJ⟩ := exists_abs_selbergJ_le
    (a := (1 : ℝ)) (c := (1 / 32 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro a _ha haOne X delta x theta hdelta hdeltaOne hX hXexp hXpow
    hx hxXa htheta hthetaHalf
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hXaX : (X : ℝ) ^ a ≤ (X : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hXone haOne
  have hxXone : x ≤ (X : ℝ) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using hxXa.trans hXaX
  exact hJ X delta x theta hdelta hdeltaOne hX hXexp hXpow hx
    hxXone htheta hthetaHalf

/-- Low physical Fourier mass with a constant uniform for `0 < a ≤ 1`. -/
theorem exists_integral_normSq_selbergPhysicalThetaKernel_low_le_uniform_unit_window :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X →
        Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-(1 / 32 : ℝ)) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ x in Ioc 1 ((X : ℝ) ^ a),
          Complex.normSq (selbergPhysicalThetaKernel delta x X)) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) *
            Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
  obtain ⟨C0, hC0, hJ⟩ := exists_abs_selbergJ_le_uniform_unit_window
  refine ⟨Real.exp 1 * C0, mul_nonneg (Real.exp_pos 1).le hC0, ?_⟩
  intro a ha haOne X delta hdelta hdeltaOne hX hXexp hXpow hlogGtwo
  let G : ℝ := (X : ℝ) ^ a
  let theta : ℝ := 1 / Real.log G
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    exact Real.rpow_nonneg (Nat.cast_nonneg X) a
  have hlogGpos : 0 < Real.log G := by linarith
  have hGone : 1 < G := (Real.log_pos_iff hGnonneg).mp hlogGpos
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have hthetaHalf : theta ≤ 1 / 2 := by
    dsimp [theta]
    exact one_div_le_one_div_of_le (by norm_num) hlogGtwo
  have hscale : theta * Real.log G = 1 := by
    dsimp [theta]
    field_simp [hlogGpos.ne']
  have hlow := selbergJLowMass_le_exp_one_mul_J_unconditional
    hdelta hdeltaOne hX hGone htheta.le hscale
  have hJone := hJ a ha.le haOne X delta 1 theta hdelta hdeltaOne hX
    hXexp hXpow (le_refl 1) hGone.le htheta hthetaHalf
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

/-- High physical Fourier mass with a constant uniform for `0 < a ≤ 1`.  The
pointwise `J` estimate is taken at exponent one, while the theta-average
identity retains the actual cutoff `X^a`. -/
theorem exists_integral_normSq_selbergPhysicalThetaKernel_high_le_uniform_unit_window :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X →
        Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-(1 / 32 : ℝ)) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ x in Ioi ((X : ℝ) ^ a),
          Complex.normSq (selbergPhysicalThetaKernel delta x X) /
            Real.log x ^ 2) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) /
            (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
  obtain ⟨C0, hC0, hJ⟩ := exists_abs_selbergJ_le_uniform_unit_window
  let k : ℝ := 1 - 2 / Real.exp 1
  have hk : 0 < k := by
    dsimp [k]
    exact one_sub_two_div_exp_one_pos
  refine ⟨C0 / k, div_nonneg hC0 hk.le, ?_⟩
  intro a ha haOne X delta hdelta hdeltaOne hX hXexp hXpow hlogGtwo
  have hac : (a + 2) * (1 / 32 : ℝ) ≤ 1 / 4 := by
    nlinarith
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
      hdelta hdeltaOne hX).mono_set (fun _x hx => hGone.le.trans_lt hx)
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
    ha.le (by norm_num : (0 : ℝ) ≤ 1 / 32)
    (by norm_num : (1 / 32 : ℝ) < 1 / 8) hac
    hdelta hdeltaOne hX hXexp hXpow hlogGtwo
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
      (X := X) hdelta hdeltaOne hGone.le htheta.1
  have hBint : Integrable B ν := by
    change IntegrableOn B (Ioc (0 : ℝ) (1 / 2))
    exact ((by fun_prop : Continuous B).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hJleB : ∀ᵐ theta ∂ν,
      theta * selbergJ delta G theta X ≤ B theta := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
    have hthetaPos : 0 < theta := htheta.1
    have hJtheta := hJ a ha.le haOne X delta G theta hdelta hdeltaOne hX
      hXexp hXpow hGone.le (le_refl G) hthetaPos htheta.2
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
    ha.le (by norm_num : (0 : ℝ) ≤ 1 / 32)
    (by norm_num : (1 / 32 : ℝ) < 1 / 8) hac
    hdelta hdeltaOne hX hXexp hXpow hlogGtwo
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

/-- Low nonconstant inverse-Fourier mass with a constant uniform for
`0 < a ≤ 1`. -/
theorem exists_integral_normSq_selbergNonconstantInverseFourierKernel_low_le_uniform_unit_window :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-(1 / 32 : ℝ)) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Ioc 0 (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
            (selbergNonconstantInverseFourierKernel delta X y)) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) *
            Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_integral_normSq_selbergPhysicalThetaKernel_low_le_uniform_unit_window
  refine ⟨C, hC, ?_⟩
  intro a ha haOne X delta hdelta hdeltaOne hX hdeltaPi hXexp hXpow hlogGtwo
  have hGnonneg : 0 ≤ (X : ℝ) ^ a :=
    Real.rpow_nonneg (Nat.cast_nonneg X) a
  have hG : 0 < (X : ℝ) ^ a := by
    have hlogpos : 0 < Real.log ((X : ℝ) ^ a) := by linarith
    exact (Real.log_pos_iff hGnonneg).mp hlogpos |>.trans' zero_lt_one
  rw [integral_normSq_selbergNonconstantInverseFourierKernel_Ioc_log
    hdelta hdeltaOne hdeltaPi hG X]
  exact hbound a ha haOne X delta hdelta hdeltaOne hX hXexp hXpow hlogGtwo

/-- High nonconstant inverse-Fourier mass with a constant uniform for
`0 < a ≤ 1`. -/
theorem exists_integral_normSq_selbergNonconstantInverseFourierKernel_high_le_uniform_unit_window :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-(1 / 32 : ℝ)) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Ioi (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
              (selbergNonconstantInverseFourierKernel delta X y) /
            y ^ 2) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) /
            (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_integral_normSq_selbergPhysicalThetaKernel_high_le_uniform_unit_window
  refine ⟨C, hC, ?_⟩
  intro a ha haOne X delta hdelta hdeltaOne hX hdeltaPi hXexp hXpow hlogGtwo
  have hGnonneg : 0 ≤ (X : ℝ) ^ a :=
    Real.rpow_nonneg (Nat.cast_nonneg X) a
  have hG : 0 < (X : ℝ) ^ a := by
    have hlogpos : 0 < Real.log ((X : ℝ) ^ a) := by linarith
    exact (Real.log_pos_iff hGnonneg).mp hlogpos |>.trans' zero_lt_one
  rw [integral_normSq_selbergNonconstantInverseFourierKernel_div_sq_Ioi_log
    hdelta hdeltaOne hdeltaPi hG X]
  exact hbound a ha haOne X delta hdelta hdeltaOne hX hXexp hXpow hlogGtwo

end HardyTheorem
