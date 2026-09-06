import HardyTheorem.SelbergGlobalLowMass
import HardyTheorem.SelbergPhysicalThetaGaussianTail
import HardyTheorem.SelbergFourierEnergyTransport
import MathlibAux.SlidingWindowParseval

open Complex FourierTransform MeasureTheory Set
open scoped ComplexConjugate FourierTransform

namespace HardyTheorem

set_option maxHeartbeats 800000

/-! # Selberg S3 global Fourier and time-domain mass -/

theorem integral_normSq_selbergNonconstantInverseFourierKernel_Ioi_log
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) {G : ℝ} (hG : 0 < G) (X : ℕ) :
    (∫ y in Ioi (Real.log G),
      Complex.normSq (selbergNonconstantInverseFourierKernel delta X y)) =
      ∫ x in Ioi G,
        Complex.normSq (selbergPhysicalThetaKernel delta x X) := by
  rw [← integral_comp_log_Ioi
    (fun y => Complex.normSq
      (selbergNonconstantInverseFourierKernel delta X y)) hG]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := hG.trans hx
  rw [normSq_selbergNonconstantInverseFourierKernel_log
    hdelta hdelta1 hdeltaPi hxpos X]
  rw [smul_eq_mul]
  field_simp [hxpos.ne']

theorem integrableOn_normSq_selbergNonconstantInverseFourierKernel_Ioi_zero
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) {X : ℕ} (hX : 2 ≤ X) :
    IntegrableOn
      (fun y => Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y)) (Ioi 0) := by
  let q : ℝ → ℝ := fun x =>
    Complex.normSq (selbergPhysicalThetaKernel delta x X)
  have hq : IntegrableOn q (Ioi (1 : ℝ)) :=
    integrableOn_selbergPhysicalThetaKernel_normSq hdelta hdelta1 hX
  have hcomp : IntegrableOn
      (fun y => Real.exp y * q (Real.exp y)) (Ioi (0 : ℝ)) := by
    exact (integrableOn_comp_exp_Ioi q 0).2 (by
      simpa only [Real.exp_zero] using hq)
  apply hcomp.congr
  filter_upwards with y
  simpa only [q, Real.log_exp] using
    (normSq_selbergNonconstantInverseFourierKernel_log
      hdelta hdelta1 hdeltaPi (Real.exp_pos y) X).symm

private theorem selberg_log_X_le_log_one_div_delta
    {c delta : ℝ} (hdelta : 0 < delta) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) {X : ℕ}
    (hXexp : Real.exp 1 ≤ (X : ℝ))
    (hXpow : (X : ℝ) ≤ delta ^ (-c)) :
    Real.log (X : ℝ) ≤ Real.log (1 / delta) := by
  have hXpos : 0 < (X : ℝ) :=
    (Real.exp_pos 1).trans_le hXexp
  have hpowPos : 0 < delta ^ (-c) := Real.rpow_pos_of_pos hdelta _
  have hlog := Real.log_le_log hXpos hXpow
  have hlogPow : Real.log (delta ^ (-c)) =
      c * Real.log (1 / delta) := by
    rw [Real.log_rpow hdelta (-c), one_div, Real.log_inv]
    ring
  rw [hlogPow] at hlog
  have hlogInv0 : 0 ≤ Real.log (1 / delta) := by
    have hlogX0 : 0 < Real.log (X : ℝ) :=
      Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hXexp)
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_ge hneg)
    linarith
  have hcOne : c ≤ 1 := by linarith
  exact hlog.trans (mul_le_of_le_one_left hlogInv0 hcOne)

private theorem delta_neg_half_le_log_target
    {c delta : ℝ} (hdelta : 0 < delta) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) {X : ℕ}
    (hXexp : Real.exp 1 ≤ (X : ℝ))
    (hXpow : (X : ℝ) ≤ delta ^ (-c)) :
    delta ^ (-(1 / 2 : ℝ)) ≤
      delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
        Real.log (X : ℝ) := by
  have hXone : 1 < (X : ℝ) :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hXexp
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hlog := selberg_log_X_le_log_one_div_delta
    hdelta hc hcEight hXexp hXpow
  rw [le_div_iff₀ hlogX]
  exact mul_le_mul_of_nonneg_left hlog
    (Real.rpow_nonneg hdelta.le _)

theorem exists_integral_normSq_selbergNonconstantInverseFourierKernel_positive_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log (delta ^ (-2 : ℝ)) →
        (∫ y in Ioi (0 : ℝ),
          Complex.normSq
            (selbergNonconstantInverseFourierKernel delta X y)) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
            Real.log (X : ℝ)) := by
  rcases exists_integral_normSq_selbergPhysicalThetaKernel_delta_low_le
    ha hc hcEight hac with ⟨C0, hC0, hlow⟩
  rcases exists_integral_normSq_selbergPhysicalThetaKernel_delta_tail_le
    hc hcEight with ⟨C1, hC1, htail⟩
  refine ⟨C0 + C1, add_nonneg hC0 hC1, ?_⟩
  intro X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
  let G : ℝ := delta ^ (-2 : ℝ)
  let L : ℝ := Real.log G
  let D : ℝ := delta ^ (-(1 / 2 : ℝ))
  let R : ℝ := D * Real.log (1 / delta) / Real.log (X : ℝ)
  have hG : 0 < G := by dsimp [G]; exact Real.rpow_pos_of_pos hdelta _
  have hL : 0 ≤ L := by dsimp only [L, G]; linarith
  have hposInt :=
    integrableOn_normSq_selbergNonconstantInverseFourierKernel_Ioi_zero
      hdelta hdelta1 hdeltaPi hX
  have htailInt := hposInt.mono_set (Ioi_subset_Ioi hL)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hposInt htailInt
  rw [intervalIntegral.integral_of_le hL] at hsplit
  have hlowKernel := hlow X delta hdelta hdelta1 hX hXexp hXpow hlogGtwo
  have hlowInv :
      (∫ y in Ioc 0 L,
        Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y)) ≤ C0 * R := by
    rw [integral_normSq_selbergNonconstantInverseFourierKernel_Ioc_log
      hdelta hdelta1 hdeltaPi hG X]
    simpa only [G, L, D, R] using hlowKernel
  have htailKernel := htail X delta hdelta hdelta1 hX hXpow
  have htailInv :
      (∫ y in Ioi L,
        Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y)) ≤ C1 * D := by
    rw [integral_normSq_selbergNonconstantInverseFourierKernel_Ioi_log
      hdelta hdelta1 hdeltaPi hG X]
    simpa only [G, L, D] using htailKernel
  have hDtoR : D ≤ R := by
    dsimp only [D, R]
    exact delta_neg_half_le_log_target hdelta hc hcEight hXexp hXpow
  calc
    (∫ y in Ioi (0 : ℝ),
        Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y)) =
      (∫ y in Ioc 0 L,
        Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y)) +
      ∫ y in Ioi L,
        Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y) := hsplit.symm
    _ ≤ C0 * R + C1 * D := add_le_add hlowInv htailInv
    _ ≤ C0 * R + C1 * R :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hDtoR hC1)
    _ = (C0 + C1) * R := by ring
    _ = _ := rfl

theorem integral_normSq_selbergResidueInverseFourierKernel_Ioi_zero_le
    {c delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) {X : ℕ} (hX : 2 ≤ X)
    (hXpow : (X : ℝ) ≤ delta ^ (-c)) :
    (∫ y in Ioi (0 : ℝ),
      Complex.normSq (selbergResidueInverseFourierKernel delta X y)) ≤
      delta ^ (-(1 / 2 : ℝ)) := by
  let D : ℝ := delta ^ (-(1 / 2 : ℝ))
  have hD0 : 0 ≤ D := Real.rpow_nonneg hdelta.le _
  have hmajor : IntegrableOn (fun y : ℝ => D * Real.exp (-y)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul D
  calc
    (∫ y in Ioi (0 : ℝ),
        Complex.normSq (selbergResidueInverseFourierKernel delta X y)) ≤
      ∫ y in Ioi (0 : ℝ), D * Real.exp (-y) := by
        apply integral_mono_of_nonneg
        · filter_upwards with y
          exact Complex.normSq_nonneg _
        · exact hmajor
        · filter_upwards with y
          exact normSq_selbergResidueInverseFourierKernel_le_exp_mul_delta_neg_half
            hdelta hdelta1 hdeltaPi hc hcEight hX hXpow y
    _ = D := by
      rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
    _ = _ := rfl

private theorem integrableOn_normSq_selbergResidueInverseFourierKernel_Ioi_zero
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    IntegrableOn
      (fun y => Complex.normSq
        (selbergResidueInverseFourierKernel delta X y)) (Ioi 0) := by
  let B : ℝ := Complex.normSq
    (selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0)
  have hmajor : IntegrableOn
      (fun y : ℝ => ((1 / 4 : ℝ) * B) * Real.exp (-y)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  apply hmajor.congr
  filter_upwards with y
  rw [normSq_selbergResidueInverseFourierKernel hdelta hdeltaPi X y]
  dsimp [B]
  ring

theorem exists_integral_normSq_selbergExplicitInverseFourierKernel_positive_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log (delta ^ (-2 : ℝ)) →
        (∫ y in Ioi (0 : ℝ),
          Complex.normSq
            (selbergExplicitInverseFourierKernel delta X y)) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
            Real.log (X : ℝ)) := by
  rcases exists_integral_normSq_selbergNonconstantInverseFourierKernel_positive_le
    ha hc hcEight hac with ⟨CN, hCN, hN⟩
  refine ⟨2 + 2 * CN, by positivity, ?_⟩
  intro X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
  let D : ℝ := delta ^ (-(1 / 2 : ℝ))
  let R : ℝ := D * Real.log (1 / delta) / Real.log (X : ℝ)
  have hRint := integrableOn_normSq_selbergResidueInverseFourierKernel_Ioi_zero
    hdelta hdeltaPi X
  have hNint :=
    integrableOn_normSq_selbergNonconstantInverseFourierKernel_Ioi_zero
      hdelta hdelta1 hdeltaPi hX
  have hmajor : IntegrableOn (fun y =>
      2 * Complex.normSq (selbergResidueInverseFourierKernel delta X y) +
      2 * Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y)) (Ioi 0) :=
    (hRint.const_mul 2).add (hNint.const_mul 2)
  have hRi := integral_normSq_selbergResidueInverseFourierKernel_Ioi_zero_le
    hdelta hdelta1 hdeltaPi hc hcEight hX hXpow
  have hNi := hN X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
  have hDtoR : D ≤ R := by
    dsimp only [D, R]
    exact delta_neg_half_le_log_target hdelta hc hcEight hXexp hXpow
  calc
    (∫ y in Ioi (0 : ℝ),
        Complex.normSq
          (selbergExplicitInverseFourierKernel delta X y)) ≤
      ∫ y in Ioi (0 : ℝ),
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
    _ = 2 * (∫ y in Ioi (0 : ℝ),
          Complex.normSq (selbergResidueInverseFourierKernel delta X y)) +
        2 * (∫ y in Ioi (0 : ℝ),
          Complex.normSq
            (selbergNonconstantInverseFourierKernel delta X y)) := by
      rw [integral_add (hRint.const_mul 2) (hNint.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * D + 2 * (CN * R) := by
      gcongr
    _ ≤ 2 * R + 2 * (CN * R) := by
      gcongr
    _ = (2 + 2 * CN) * R := by ring
    _ = _ := rfl

private theorem integral_normSq_fourier_selberg_Ioi_zero_eq
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    (∫ w in Ioi (0 : ℝ),
      Complex.normSq (𝓕 (selbergCompletedMollifiedFComplex delta X) w)) =
      ∫ y in Ioi (0 : ℝ),
        Complex.normSq (selbergExplicitInverseFourierKernel delta X y) := by
  let p : ℝ := 2 * Real.pi
  let m : ℝ → ℝ := fun y => Complex.normSq
    (selbergExplicitInverseFourierKernel delta X y)
  have hp : 0 < p := by dsimp [p]; positivity
  rw [setIntegral_congr_fun measurableSet_Ioi (fun w _ =>
    normSq_fourier_selbergCompletedMollifiedF_eq hdelta hdeltaPi X w)]
  have hform : ∀ w : ℝ,
      (2 * Real.pi) * Complex.normSq
          (selbergExplicitInverseFourierKernel delta X (2 * Real.pi * w)) =
        p * m (p * w) := by
    intro w
    rfl
  rw [setIntegral_congr_fun measurableSet_Ioi (fun w _ => hform w)]
  rw [integral_const_mul]
  have hscale := integral_comp_mul_left_Ioi m 0 hp
  change p * (∫ w in Ioi (0 : ℝ), m (p * w)) = _
  rw [hscale]
  simp only [smul_eq_mul, mul_zero]
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]

private theorem integral_normSq_scalar_fourier_selberg_eq_two_mul_positive
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    (∫ w : ℝ,
      Complex.normSq (𝓕 (selbergCompletedMollifiedFComplex delta X) w)) =
      2 * ∫ y in Ioi (0 : ℝ),
        Complex.normSq (selbergExplicitInverseFourierKernel delta X y) := by
  let Q : ℝ → ℝ := fun w =>
    Complex.normSq (𝓕 (selbergCompletedMollifiedFComplex delta X) w)
  have hreal : ∀ t,
      conj (selbergCompletedMollifiedFComplex delta X t) =
        selbergCompletedMollifiedFComplex delta X t := by
    intro t
    simp [selbergCompletedMollifiedFComplex]
  have heven : Function.Even Q :=
    MathlibAux.normSq_fourier_even_of_conj_eq_self hreal
  have habs : ∀ w : ℝ, Q w = Q |w| := by
    intro w
    rcases le_total 0 w with hw | hw
    · rw [abs_of_nonneg hw]
    · rw [abs_of_nonpos hw, heven w]
  calc
    (∫ w : ℝ,
        Complex.normSq (𝓕 (selbergCompletedMollifiedFComplex delta X) w)) =
      ∫ w : ℝ, Q |w| := by
        apply integral_congr_ae
        filter_upwards with w
        exact habs w
    _ = 2 * ∫ w in Ioi (0 : ℝ), Q w := integral_comp_abs
    _ = 2 * ∫ y in Ioi (0 : ℝ),
        Complex.normSq (selbergExplicitInverseFourierKernel delta X y) := by
      rw [integral_normSq_fourier_selberg_Ioi_zero_eq hdelta hdeltaPi X]

theorem integral_normSq_selbergCompletedMollifiedF_eq_two_mul_positive
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    (∫ t : ℝ, ‖selbergCompletedMollifiedFComplex delta X t‖ ^ 2) =
      2 * ∫ y in Ioi (0 : ℝ),
        Complex.normSq (selbergExplicitInverseFourierKernel delta X y) := by
  let F : ℝ → ℂ := selbergCompletedMollifiedFComplex delta X
  let hF2 : MemLp F 2 :=
    memLp_two_selbergCompletedMollifiedF_complex hdelta hdeltaPi X
  let FLp : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) := hF2.toLp F
  let Fhat : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) := 𝓕 FLp
  have hcoe := hF2.coeFn_toLp
  have hcompat := MathlibAux.coe_fourier_toLp_two_ae_eq_of_integrable
    (integrable_selbergCompletedMollifiedF_complex hdelta hdeltaPi X) hF2
  calc
    (∫ t : ℝ, ‖selbergCompletedMollifiedFComplex delta X t‖ ^ 2) =
      ∫ t : ℝ, ‖FLp t‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hcoe] with t ht
        rw [ht]
    _ = ‖FLp‖ ^ 2 := MathlibAux.integral_norm_sq_coeFn_eq_norm_sq FLp
    _ = ‖Fhat‖ ^ 2 := by
      dsimp only [Fhat]
      rw [MeasureTheory.Lp.norm_fourier_eq]
    _ = ∫ w : ℝ, ‖Fhat w‖ ^ 2 :=
      (MathlibAux.integral_norm_sq_coeFn_eq_norm_sq Fhat).symm
    _ = ∫ w : ℝ,
        Complex.normSq (𝓕 (selbergCompletedMollifiedFComplex delta X) w) := by
      apply integral_congr_ae
      filter_upwards [hcompat] with w hw
      rw [hw]
      exact (Complex.normSq_eq_norm_sq _).symm
    _ = 2 * ∫ y in Ioi (0 : ℝ),
        Complex.normSq (selbergExplicitInverseFourierKernel delta X y) :=
      integral_normSq_scalar_fourier_selberg_eq_two_mul_positive
        hdelta hdeltaPi X

theorem exists_integral_normSq_selbergCompletedMollifiedF_global_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log (delta ^ (-2 : ℝ)) →
        (∫ t : ℝ, ‖selbergCompletedMollifiedFComplex delta X t‖ ^ 2) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
            Real.log (X : ℝ)) := by
  rcases exists_integral_normSq_selbergExplicitInverseFourierKernel_positive_le
    ha hc hcEight hac with ⟨C0, hC0, hmass⟩
  refine ⟨2 * C0, mul_nonneg (by norm_num) hC0, ?_⟩
  intro X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
  rw [integral_normSq_selbergCompletedMollifiedF_eq_two_mul_positive
    hdelta hdeltaPi X]
  calc
    2 * (∫ y in Ioi (0 : ℝ),
        Complex.normSq (selbergExplicitInverseFourierKernel delta X y)) ≤
      2 * (C0 * (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
        Real.log (X : ℝ))) := by
        gcongr
        exact hmass X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
    _ = (2 * C0) * (delta ^ (-(1 / 2 : ℝ)) * Real.log (1 / delta) /
        Real.log (X : ℝ)) := by ring

end HardyTheorem
