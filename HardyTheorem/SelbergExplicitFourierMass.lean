import HardyTheorem.SelbergResidueFourierMass

open Complex MeasureTheory Set

namespace HardyTheorem

set_option maxHeartbeats 800000

/-! # Positive-frequency mass of Selberg's full explicit S1 kernel -/

private theorem integrableOn_comp_exp_Ioc_real (g : ℝ → ℝ) (a b : ℝ) :
    IntegrableOn (fun y => Real.exp y * g (Real.exp y)) (Ioc a b) ↔
      IntegrableOn g (Ioc (Real.exp a) (Real.exp b)) := by
  rw [← Real.image_exp_Ioc]
  simpa [abs_of_pos (Real.exp_pos _)] using
    (integrableOn_image_iff_integrableOn_abs_deriv_smul
      (measurableSet_Ioc (a := a) (b := b))
      (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
      (fun _ _ _ _ h => Real.exp_injective h) g).symm

theorem normSq_selbergExplicitInverseFourierKernel_le
    (delta : ℝ) (X : ℕ) (y : ℝ) :
    Complex.normSq (selbergExplicitInverseFourierKernel delta X y) ≤
      2 * Complex.normSq (selbergResidueInverseFourierKernel delta X y) +
        2 * Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y) := by
  rw [selbergExplicitInverseFourierKernel_eq_residue_add_nonconstant]
  simp only [Complex.normSq_eq_norm_sq]
  have hnorm := norm_add_le
    (selbergResidueInverseFourierKernel delta X y)
    (selbergNonconstantInverseFourierKernel delta X y)
  have hsq :
      ‖selbergResidueInverseFourierKernel delta X y +
          selbergNonconstantInverseFourierKernel delta X y‖ ^ 2 ≤
        (‖selbergResidueInverseFourierKernel delta X y‖ +
          ‖selbergNonconstantInverseFourierKernel delta X y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ‖selbergResidueInverseFourierKernel delta X y +
        selbergNonconstantInverseFourierKernel delta X y‖ ^ 2 ≤
      (‖selbergResidueInverseFourierKernel delta X y‖ +
        ‖selbergNonconstantInverseFourierKernel delta X y‖) ^ 2 := hsq
    _ ≤ 2 * ‖selbergResidueInverseFourierKernel delta X y‖ ^ 2 +
        2 * ‖selbergNonconstantInverseFourierKernel delta X y‖ ^ 2 := by
      nlinarith [sq_nonneg
        (‖selbergResidueInverseFourierKernel delta X y‖ -
          ‖selbergNonconstantInverseFourierKernel delta X y‖)]

private theorem integrableOn_normSq_selbergResidue_low
    {delta L : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    IntegrableOn
      (fun y => Complex.normSq
        (selbergResidueInverseFourierKernel delta X y)) (Ioc 0 L) := by
  let B : ℝ := Complex.normSq
    (selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0)
  have hmajor : IntegrableOn
      (fun y : ℝ => ((1 / 4 : ℝ) * B) * Real.exp (-y)) (Ioc 0 L) :=
    ((integrableOn_exp_neg_Ioi 0).mono_set Ioc_subset_Ioi_self).const_mul _
  apply hmajor.congr
  filter_upwards with y
  rw [normSq_selbergResidueInverseFourierKernel hdelta hdeltaPi X y]
  dsimp [B]
  ring

private theorem integrableOn_normSq_selbergNonconstant_low
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) {G : ℝ} (hG : 1 < G)
    {X : ℕ} (hX : 2 ≤ X) :
    IntegrableOn
      (fun y => Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y))
      (Ioc 0 (Real.log G)) := by
  let q : ℝ → ℝ := fun x => Complex.normSq
    (selbergPhysicalThetaKernel delta x X)
  have hq : IntegrableOn q (Ioc 1 G) :=
    (integrableOn_selbergPhysicalThetaKernel_normSq
      hdelta hdelta1 hX).mono_set (fun _x hx => hx.1)
  have hcomp : IntegrableOn
      (fun y => Real.exp y * q (Real.exp y))
      (Ioc 0 (Real.log G)) := by
    rw [integrableOn_comp_exp_Ioc_real]
    simpa [q, Real.exp_log (zero_lt_one.trans hG)] using hq
  apply hcomp.congr
  filter_upwards with y
  simpa only [q, Real.log_exp] using
    (normSq_selbergNonconstantInverseFourierKernel_log
      hdelta hdelta1 hdeltaPi (Real.exp_pos y) X).symm

private theorem integrableOn_normSq_selbergResidue_div_sq_high
    {delta L : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (hL : 0 < L) (X : ℕ) :
    IntegrableOn
      (fun y => Complex.normSq
          (selbergResidueInverseFourierKernel delta X y) / y ^ 2)
      (Ioi L) := by
  let B : ℝ := Complex.normSq
    (selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0)
  let μ : Measure ℝ := volume.restrict (Ioi L)
  have hexp : Integrable (fun y : ℝ => Real.exp (-y)) μ :=
    integrableOn_exp_neg_Ioi L
  have hfactorMeas : AEStronglyMeasurable
      (fun y : ℝ => 1 / y ^ 2) μ :=
    (measurable_const.div (measurable_id.pow_const 2)).aestronglyMeasurable
  have hfactor : ∀ᵐ y ∂μ, ‖1 / y ^ 2‖ ≤ 1 / L ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hypos : 0 < y := hL.trans hy
    have hsq : L ^ 2 ≤ y ^ 2 :=
      (sq_le_sq₀ hL.le hypos.le).2 hy.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hL) hsq
  have hprod : Integrable
      (fun y : ℝ => Real.exp (-y) * (1 / y ^ 2)) μ :=
    hexp.mul_bdd hfactorMeas hfactor
  have hscaled : Integrable
      (fun y : ℝ => ((1 / 4 : ℝ) * B) *
        (Real.exp (-y) * (1 / y ^ 2))) μ := hprod.const_mul _
  apply hscaled.congr
  filter_upwards with y
  rw [normSq_selbergResidueInverseFourierKernel hdelta hdeltaPi X y]
  dsimp [B]
  ring

private theorem integrableOn_normSq_selbergNonconstant_div_sq_high
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) {G : ℝ} (hG : 1 < G)
    {X : ℕ} (hX : 2 ≤ X) :
    IntegrableOn
      (fun y => Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2)
      (Ioi (Real.log G)) := by
  let q : ℝ → ℝ := fun x => Complex.normSq
    (selbergPhysicalThetaKernel delta x X)
  let r : ℝ → ℝ := fun x => q x / Real.log x ^ 2
  let μ : Measure ℝ := volume.restrict (Ioi G)
  have hq : Integrable q μ := by
    change IntegrableOn q (Ioi G)
    exact (integrableOn_selbergPhysicalThetaKernel_normSq
      hdelta hdelta1 hX).mono_set (fun _x hx => hG.le.trans_lt hx)
  have hlogG : 0 < Real.log G := Real.log_pos hG
  have hfactorMeas : AEStronglyMeasurable
      (fun x : ℝ => 1 / Real.log x ^ 2) μ :=
    (measurable_const.div (Real.measurable_log.pow_const 2)).aestronglyMeasurable
  have hfactor : ∀ᵐ x ∂μ,
      ‖1 / Real.log x ^ 2‖ ≤ 1 / Real.log G ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := zero_lt_one.trans (hG.trans hx)
    have hlogle : Real.log G ≤ Real.log x :=
      Real.log_le_log (zero_lt_one.trans hG) hx.le
    have hsq : Real.log G ^ 2 ≤ Real.log x ^ 2 :=
      (sq_le_sq₀ hlogG.le (Real.log_pos (hG.trans hx)).le).2 hlogle
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hlogG) hsq
  have hr : Integrable r μ := by
    simpa [r, div_eq_mul_inv] using hq.mul_bdd hfactorMeas hfactor
  have hrOn : IntegrableOn r (Ioi G) := by
    change Integrable r (volume.restrict (Ioi G))
    simpa only [μ] using hr
  have hcomp : IntegrableOn
      (fun y => Real.exp y * r (Real.exp y)) (Ioi (Real.log G)) :=
    (integrableOn_comp_exp_Ioi r (Real.log G)).2 (by
      simpa only [Real.exp_log (zero_lt_one.trans hG)] using hrOn)
  apply hcomp.congr
  filter_upwards with y
  have hn : Complex.normSq
      (selbergNonconstantInverseFourierKernel delta X y) =
        Real.exp y * q (Real.exp y) := by
    simpa only [q, Real.log_exp] using
      (normSq_selbergNonconstantInverseFourierKernel_log
        hdelta hdelta1 hdeltaPi (Real.exp_pos y) X)
  rw [hn]
  simp only [r, Real.log_exp]
  ring

theorem exists_integral_normSq_selbergExplicitInverseFourierKernel_low_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Ioc 0 (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
            (selbergExplicitInverseFourierKernel delta X y)) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) *
            Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
  rcases exists_integral_normSq_selbergResidueInverseFourierKernel_low_le
    ha hc hcEight hac with ⟨CR, hCR, hR⟩
  rcases exists_integral_normSq_selbergNonconstantInverseFourierKernel_low_le
    ha hc hcEight hac with ⟨CN, hCN, hN⟩
  refine ⟨2 * CR + 2 * CN, by positivity, ?_⟩
  intro X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
  let G : ℝ := (X : ℝ) ^ a
  let S : ℝ := delta ^ (-(1 / 2 : ℝ)) * Real.log G / Real.log (X : ℝ)
  have hGone : 1 < G := by
    have hG0 : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg X) a
    exact (Real.log_pos_iff hG0).mp (by linarith)
  have hRint := integrableOn_normSq_selbergResidue_low
    hdelta hdeltaPi X (L := Real.log G)
  have hNint := integrableOn_normSq_selbergNonconstant_low
    hdelta hdelta1 hdeltaPi hGone hX
  have hmajor : IntegrableOn (fun y =>
      2 * Complex.normSq (selbergResidueInverseFourierKernel delta X y) +
      2 * Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y))
      (Ioc 0 (Real.log G)) :=
    (hRint.const_mul 2).add (hNint.const_mul 2)
  have hRi : (∫ y in Ioc 0 (Real.log G),
      Complex.normSq (selbergResidueInverseFourierKernel delta X y)) ≤
      CR * S := by
    simpa only [G, S] using hR X delta hdelta hdelta1 hX hdeltaPi
      hXexp hXpow hlogGtwo
  have hNi : (∫ y in Ioc 0 (Real.log G),
      Complex.normSq (selbergNonconstantInverseFourierKernel delta X y)) ≤
      CN * S := by
    simpa only [G, S] using hN X delta hdelta hdelta1 hX hdeltaPi
      hXexp hXpow hlogGtwo
  have hS : 0 ≤ S := by
    dsimp [S, G]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    positivity
  calc
    (∫ y in Ioc 0 (Real.log ((X : ℝ) ^ a)),
        Complex.normSq (selbergExplicitInverseFourierKernel delta X y)) ≤
      ∫ y in Ioc 0 (Real.log G),
        (2 * Complex.normSq
          (selbergResidueInverseFourierKernel delta X y) +
         2 * Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y)) := by
        apply integral_mono_of_nonneg
        · filter_upwards with y
          exact Complex.normSq_nonneg _
        · exact hmajor
        · filter_upwards with y
          exact normSq_selbergExplicitInverseFourierKernel_le delta X y
    _ = 2 * (∫ y in Ioc 0 (Real.log G),
          Complex.normSq (selbergResidueInverseFourierKernel delta X y)) +
        2 * (∫ y in Ioc 0 (Real.log G),
          Complex.normSq
            (selbergNonconstantInverseFourierKernel delta X y)) := by
      rw [integral_add (hRint.const_mul 2) (hNint.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * (CR * S) + 2 * (CN * S) := by
      gcongr
    _ = (2 * CR + 2 * CN) *
        (delta ^ (-(1 / 2 : ℝ)) *
          Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
      dsimp [S, G]
      ring

theorem exists_integral_normSq_selbergExplicitInverseFourierKernel_high_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Ioi (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
              (selbergExplicitInverseFourierKernel delta X y) / y ^ 2) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) /
            (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
  rcases exists_integral_normSq_selbergResidueInverseFourierKernel_high_le
    ha hc hcEight hac with ⟨CR, hCR, hR⟩
  rcases exists_integral_normSq_selbergNonconstantInverseFourierKernel_high_le
    ha hc hcEight hac with ⟨CN, hCN, hN⟩
  refine ⟨2 * CR + 2 * CN, by positivity, ?_⟩
  intro X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
  let G : ℝ := (X : ℝ) ^ a
  let L : ℝ := Real.log G
  let S : ℝ := delta ^ (-(1 / 2 : ℝ)) /
    (L * Real.log (X : ℝ))
  have hGone : 1 < G := by
    have hG0 : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg X) a
    exact (Real.log_pos_iff hG0).mp (by linarith)
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos hGone
  have hRint := integrableOn_normSq_selbergResidue_div_sq_high
    hdelta hdeltaPi hL X
  have hNint := integrableOn_normSq_selbergNonconstant_div_sq_high
    hdelta hdelta1 hdeltaPi hGone hX
  have hmajor : IntegrableOn (fun y =>
      2 * (Complex.normSq
        (selbergResidueInverseFourierKernel delta X y) / y ^ 2) +
      2 * (Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2))
      (Ioi L) := (hRint.const_mul 2).add (hNint.const_mul 2)
  have hRi : (∫ y in Ioi L,
      Complex.normSq (selbergResidueInverseFourierKernel delta X y) /
        y ^ 2) ≤ CR * S := by
    simpa only [G, L, S] using hR X delta hdelta hdelta1 hX hdeltaPi
      hXexp hXpow hlogGtwo
  have hNi : (∫ y in Ioi L,
      Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2) ≤
      CN * S := by
    simpa only [G, L, S] using hN X delta hdelta hdelta1 hX hdeltaPi
      hXexp hXpow hlogGtwo
  calc
    (∫ y in Ioi (Real.log ((X : ℝ) ^ a)),
        Complex.normSq
          (selbergExplicitInverseFourierKernel delta X y) / y ^ 2) ≤
      ∫ y in Ioi L,
        (2 * (Complex.normSq
          (selbergResidueInverseFourierKernel delta X y) / y ^ 2) +
         2 * (Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2)) := by
        apply integral_mono_of_nonneg
        · filter_upwards with y
          exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg y)
        · exact hmajor
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          convert div_le_div_of_nonneg_right
            (normSq_selbergExplicitInverseFourierKernel_le delta X y)
            (sq_nonneg y) using 1
          all_goals ring
    _ = 2 * (∫ y in Ioi L,
          Complex.normSq (selbergResidueInverseFourierKernel delta X y) /
            y ^ 2) +
        2 * (∫ y in Ioi L,
          Complex.normSq
            (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2) := by
      rw [integral_add (hRint.const_mul 2) (hNint.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * (CR * S) + 2 * (CN * S) := by
      gcongr
    _ = (2 * CR + 2 * CN) *
        (delta ^ (-(1 / 2 : ℝ)) /
          (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
      dsimp [S, L, G]
      ring

end HardyTheorem
