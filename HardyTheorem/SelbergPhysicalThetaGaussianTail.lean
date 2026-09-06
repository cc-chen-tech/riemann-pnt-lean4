import HardyTheorem.SelbergJPointwiseExpansion
import HardyTheorem.SelbergResidueFourierMass
import HardyTheorem.SelbergGaussianHarmonicSum
import HardyTheorem.SelbergDiagonalRemainderParameter

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-! # Direct Gaussian tail for Selberg's physical theta kernel -/

noncomputable def selbergS3GaussianScale (delta : ℝ) (X : ℕ) : ℝ :=
  delta / (2 * (X : ℝ) ^ 2)

theorem norm_selbergPhysicalGaussianTerm
    (delta u : ℝ) (n kappa lambda : ℕ) :
    ‖selbergPhysicalGaussianTerm delta u n kappa lambda‖ =
      Real.exp (-Real.pi * Real.sin delta *
        selbergPhysicalSquareRatio n kappa lambda * u ^ 2) := by
  unfold selbergPhysicalGaussianTerm
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero,
    add_zero]
  ring

theorem norm_selbergPhysicalGaussianTerm_le_s3Mass
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X n kappa lambda : ℕ} (hX : 1 ≤ X) (hn : 1 ≤ n)
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hlambdaX : lambda ≤ X) (u : ℝ) :
    ‖selbergPhysicalGaussianTerm delta u n kappa lambda‖ ≤
      Real.exp (-(selbergS3GaussianScale delta X *
        (n : ℝ) ^ 2 * u ^ 2)) := by
  rw [norm_selbergPhysicalGaussianTerm]
  apply Real.exp_le_exp.mpr
  have hpiSin : delta / 2 ≤ Real.pi * Real.sin delta := by
    linarith [delta_le_two_pi_mul_sin hdelta hdelta1]
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX.trans_lt' zero_lt_one
  have hlambdaPos : (0 : ℝ) < (lambda : ℝ) := by exact_mod_cast hlambda
  have hkappaR : (1 : ℝ) ≤ (kappa : ℝ) := by exact_mod_cast hkappa
  have hlambdaXR : (lambda : ℝ) ≤ (X : ℝ) := by exact_mod_cast hlambdaX
  have hratio : (1 : ℝ) / (X : ℝ) ^ 2 ≤
      (kappa : ℝ) ^ 2 / (lambda : ℝ) ^ 2 := by
    have hden : (lambda : ℝ) ^ 2 ≤ (X : ℝ) ^ 2 :=
      (sq_le_sq₀ hlambdaPos.le hXpos.le).2 hlambdaXR
    exact div_le_div₀ (sq_nonneg _) (by nlinarith)
      (sq_pos_of_pos hlambdaPos) hden
  have hscale : selbergS3GaussianScale delta X ≤
      Real.pi * Real.sin delta * ((kappa : ℝ) ^ 2 / (lambda : ℝ) ^ 2) := by
    unfold selbergS3GaussianScale
    calc
      delta / (2 * (X : ℝ) ^ 2) =
          (delta / 2) * (1 / (X : ℝ) ^ 2) := by ring
      _ ≤ (Real.pi * Real.sin delta) *
          ((kappa : ℝ) ^ 2 / (lambda : ℝ) ^ 2) := by
        exact mul_le_mul hpiSin hratio (by positivity)
          (mul_nonneg Real.pi_pos.le
            (Real.sin_nonneg_of_nonneg_of_le_pi hdelta.le
              (hdelta1.trans (by linarith [Real.pi_gt_three]))))
  have hmul : selbergS3GaussianScale delta X * (n : ℝ) ^ 2 * u ^ 2 ≤
      Real.pi * Real.sin delta *
        selbergPhysicalSquareRatio n kappa lambda * u ^ 2 := by
    unfold selbergPhysicalSquareRatio
    have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hnk : ((n * kappa : ℕ) : ℝ) ^ 2 =
        (n : ℝ) ^ 2 * (kappa : ℝ) ^ 2 := by
      push_cast
      ring
    rw [hnk]
    calc
      selbergS3GaussianScale delta X * (n : ℝ) ^ 2 * u ^ 2 =
          (n : ℝ) ^ 2 * selbergS3GaussianScale delta X * u ^ 2 := by ring
      _ ≤ (n : ℝ) ^ 2 *
          (Real.pi * Real.sin delta *
            ((kappa : ℝ) ^ 2 / (lambda : ℝ) ^ 2)) * u ^ 2 := by
        gcongr
      _ = Real.pi * Real.sin delta *
          ((n : ℝ) ^ 2 * (kappa : ℝ) ^ 2 / (lambda : ℝ) ^ 2) *
            u ^ 2 := by ring
  linarith

theorem tsum_selbergGaussianMass_le_eight_mul_exp_half
    {z : ℝ} (hz : 1 / 2 ≤ z) :
    (∑' j : ℕ, selbergGaussianMass z j) ≤
      8 * Real.exp (-z / 2) := by
  have hz0 : 0 < z := by linarith
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hquarterOne : (1 / 4 : ℝ) ≤ 1 := by norm_num
  have hmassQuarter := mul_tsum_selbergGaussianMass_le_two
    hquarter hquarterOne
  have hquarterSum : (∑' j : ℕ, selbergGaussianMass (1 / 4) j) ≤ 8 := by
    nlinarith
  have hleft := summable_selbergGaussianMass hz0
  have hright := (summable_selbergGaussianMass hquarter).mul_left
    (Real.exp (-z / 2))
  have hpoint : ∀ j : ℕ,
      selbergGaussianMass z j ≤
        Real.exp (-z / 2) * selbergGaussianMass (1 / 4) j := by
    intro j
    have hm : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
      have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 j
      nlinarith
    unfold selbergGaussianMass
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hzquarter : 1 / 4 ≤ z / 2 := by linarith
    nlinarith
  calc
    (∑' j : ℕ, selbergGaussianMass z j) ≤
        ∑' j : ℕ, Real.exp (-z / 2) *
          selbergGaussianMass (1 / 4) j :=
      hleft.tsum_le_tsum hpoint hright
    _ = Real.exp (-z / 2) *
        (∑' j : ℕ, selbergGaussianMass (1 / 4) j) := by
      rw [Summable.tsum_mul_left _ (summable_selbergGaussianMass hquarter)]
    _ ≤ Real.exp (-z / 2) * 8 :=
      mul_le_mul_of_nonneg_left hquarterSum (Real.exp_pos _).le
    _ = 8 * Real.exp (-z / 2) := by ring

theorem norm_selbergPhysicalThetaRay_le_s3
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda : ℕ} (hX : 1 ≤ X)
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hlambdaX : lambda ≤ X) {u : ℝ} (hu : 0 < u)
    (hscale : 1 / 2 ≤ selbergS3GaussianScale delta X * u ^ 2) :
    ‖selbergPhysicalThetaRay delta u kappa lambda‖ ≤
      8 * Real.exp (-(selbergS3GaussianScale delta X * u ^ 2) / 2) := by
  let z : ℝ := selbergS3GaussianScale delta X * u ^ 2
  have hz0 : 0 < z := by dsimp only [z]; linarith
  have hsum := summable_selbergPhysicalGaussianTerm_add_one
    hdelta hdelta1 hu hkappa hlambda
  have hnorm := hsum.norm
  have hmass := summable_selbergGaussianMass hz0
  have hpoint : ∀ j : ℕ,
      ‖selbergPhysicalGaussianTerm delta u (j + 1) kappa lambda‖ ≤
        selbergGaussianMass z j := by
    intro j
    have hterm := norm_selbergPhysicalGaussianTerm_le_s3Mass
      hdelta hdelta1 hX (Nat.le_add_left 1 j) hkappa hlambda hlambdaX u
    have hmassEq : selbergGaussianMass z j =
        Real.exp (-(selbergS3GaussianScale delta X *
          ((j + 1 : ℕ) : ℝ) ^ 2 * u ^ 2)) := by
      unfold selbergGaussianMass
      dsimp only [z]
      congr 1
      ring
    rw [hmassEq]
    exact hterm
  unfold selbergPhysicalThetaRay
  calc
    ‖∑' j : ℕ, selbergPhysicalGaussianTerm delta u (j + 1) kappa lambda‖ ≤
        ∑' j : ℕ,
          ‖selbergPhysicalGaussianTerm delta u (j + 1) kappa lambda‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, selbergGaussianMass z j :=
      hnorm.tsum_le_tsum hpoint hmass
    _ ≤ 8 * Real.exp (-z / 2) :=
      tsum_selbergGaussianMass_le_eight_mul_exp_half hscale
    _ = _ := rfl

private theorem abs_selbergS3TaperedCoeff_le_one
    {X n : ℕ} (hX : 2 ≤ X) (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    |selbergSqrtZetaTaperedCoeff X n| ≤ 1 := by
  have hweight := selbergMoebiusWeight_mem_Icc hX hn1 hnX
  rw [selbergSqrtZetaTaperedCoeff, abs_mul, abs_of_nonneg hweight.1]
  calc
    |selbergSqrtZetaCoeff n| * selbergMoebiusWeight X n ≤
        1 * selbergMoebiusWeight X n :=
      mul_le_mul_of_nonneg_right
        (abs_selbergSqrtZetaCoeff_le_one_light n) hweight.1
    _ ≤ 1 := by simpa using hweight.2

private theorem norm_selbergPhysicalThetaOuterTerm_le_ray
    {X kappa lambda : ℕ} (hX : 2 ≤ X)
    (hkappa : kappa ∈ Finset.Icc 1 X)
    (hlambda : lambda ∈ Finset.Icc 1 X) (ray : ℂ) :
    ‖((selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
        (selbergSqrtZetaTaperedCoeff X lambda : ℂ) / (lambda : ℂ)) * ray‖ ≤
      ‖ray‖ := by
  have hk := Finset.mem_Icc.mp hkappa
  have hl := Finset.mem_Icc.mp hlambda
  have hbk := abs_selbergS3TaperedCoeff_le_one hX hk.1 hk.2
  have hbl := abs_selbergS3TaperedCoeff_le_one hX hl.1 hl.2
  have hlR : (1 : ℝ) ≤ (lambda : ℝ) := by exact_mod_cast hl.1
  have hcoeff :
      ‖(selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
          (selbergSqrtZetaTaperedCoeff X lambda : ℂ) / (lambda : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_natCast]
    have hnum :
        |selbergSqrtZetaTaperedCoeff X kappa| *
            |selbergSqrtZetaTaperedCoeff X lambda| ≤ 1 := by
      nlinarith [abs_nonneg (selbergSqrtZetaTaperedCoeff X kappa),
        abs_nonneg (selbergSqrtZetaTaperedCoeff X lambda)]
    exact (div_le_one (by positivity)).2 (hnum.trans hlR)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg ray) hcoeff

theorem norm_selbergPhysicalThetaKernel_le_s3
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 2 ≤ X) {u : ℝ} (hu : 0 < u)
    (hscale : 1 / 2 ≤ selbergS3GaussianScale delta X * u ^ 2) :
    ‖selbergPhysicalThetaKernel delta u X‖ ≤
      8 * (X : ℝ) ^ 2 *
        Real.exp (-(selbergS3GaussianScale delta X * u ^ 2) / 2) := by
  let C : ℝ := 8 * Real.exp
    (-(selbergS3GaussianScale delta X * u ^ 2) / 2)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hXone : 1 ≤ X := hX.trans' (by norm_num)
  unfold selbergPhysicalThetaKernel
  calc
    ‖∑ kappa ∈ Finset.Icc 1 X, ∑ lambda ∈ Finset.Icc 1 X,
        ((selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
          (selbergSqrtZetaTaperedCoeff X lambda : ℂ) / (lambda : ℂ)) *
          selbergPhysicalThetaRay delta u kappa lambda‖ ≤
      ∑ kappa ∈ Finset.Icc 1 X,
        ‖∑ lambda ∈ Finset.Icc 1 X,
          ((selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
            (selbergSqrtZetaTaperedCoeff X lambda : ℂ) / (lambda : ℂ)) *
            selbergPhysicalThetaRay delta u kappa lambda‖ := by
      simpa only using norm_sum_le (Finset.Icc 1 X) (fun kappa =>
        ∑ lambda ∈ Finset.Icc 1 X,
          ((selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
            (selbergSqrtZetaTaperedCoeff X lambda : ℂ) / (lambda : ℂ)) *
            selbergPhysicalThetaRay delta u kappa lambda)
    _ ≤ ∑ kappa ∈ Finset.Icc 1 X, ∑ lambda ∈ Finset.Icc 1 X,
        ‖((selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
          (selbergSqrtZetaTaperedCoeff X lambda : ℂ) / (lambda : ℂ)) *
          selbergPhysicalThetaRay delta u kappa lambda‖ := by
      apply Finset.sum_le_sum
      intro kappa hkappa
      exact norm_sum_le _ _
    _ ≤ ∑ _kappa ∈ Finset.Icc 1 X, ∑ _lambda ∈ Finset.Icc 1 X, C := by
      apply Finset.sum_le_sum
      intro kappa hkappa
      apply Finset.sum_le_sum
      intro lambda hlambda
      calc
        ‖((selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
            (selbergSqrtZetaTaperedCoeff X lambda : ℂ) / (lambda : ℂ)) *
            selbergPhysicalThetaRay delta u kappa lambda‖ ≤
          ‖selbergPhysicalThetaRay delta u kappa lambda‖ :=
            norm_selbergPhysicalThetaOuterTerm_le_ray hX hkappa hlambda _
        _ ≤ C := norm_selbergPhysicalThetaRay_le_s3 hdelta hdelta1 hXone
          (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hlambda).1
          (Finset.mem_Icc.mp hlambda).2 hu hscale
    _ = 8 * (X : ℝ) ^ 2 *
        Real.exp (-(selbergS3GaussianScale delta X * u ^ 2) / 2) := by
      simp only [Finset.sum_const, Nat.card_Icc, C]
      push_cast
      ring

theorem normSq_selbergPhysicalThetaKernel_le_s3
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 2 ≤ X) {u : ℝ} (hu : 0 < u)
    (hscale : 1 / 2 ≤ selbergS3GaussianScale delta X * u ^ 2) :
    Complex.normSq (selbergPhysicalThetaKernel delta u X) ≤
      64 * (X : ℝ) ^ 4 *
        Real.exp (-(selbergS3GaussianScale delta X * u ^ 2)) := by
  have hnorm := norm_selbergPhysicalThetaKernel_le_s3
    hdelta hdelta1 hX hu hscale
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖selbergPhysicalThetaKernel delta u X‖ ^ 2 ≤
        (8 * (X : ℝ) ^ 2 *
          Real.exp (-(selbergS3GaussianScale delta X * u ^ 2) / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = 64 * (X : ℝ) ^ 4 *
        Real.exp (-(selbergS3GaussianScale delta X * u ^ 2)) := by
      calc
        (8 * (X : ℝ) ^ 2 *
            Real.exp (-(selbergS3GaussianScale delta X * u ^ 2) / 2)) ^ 2 =
          64 * (X : ℝ) ^ 4 *
            (Real.exp (-(selbergS3GaussianScale delta X * u ^ 2) / 2) ^ 2) := by
              ring
        _ = 64 * (X : ℝ) ^ 4 *
            Real.exp (-(selbergS3GaussianScale delta X * u ^ 2)) := by
          rw [pow_two, ← Real.exp_add]
          congr 2
          ring

theorem exp_neg_le_inv {z : ℝ} (hz : 0 < z) :
    Real.exp (-z) ≤ z⁻¹ := by
  rw [Real.exp_neg]
  have hzexp : z ≤ Real.exp z := by
    exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (by simpa [add_comm] using Real.add_one_le_exp z)
  exact (inv_le_inv₀ (Real.exp_pos z) hz).2 hzexp

theorem integral_normSq_selbergPhysicalThetaKernel_delta_tail_le_raw
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 2 ≤ X)
    (hendpoint : 1 / 2 ≤ selbergS3GaussianScale delta X *
      (delta ^ (-2 : ℝ)) ^ 2) :
    (∫ u in Ioi (delta ^ (-2 : ℝ)),
      Complex.normSq (selbergPhysicalThetaKernel delta u X)) ≤
      64 * (X : ℝ) ^ 4 /
        (selbergS3GaussianScale delta X ^ 2 *
          (delta ^ (-2 : ℝ)) ^ 3) := by
  let B : ℝ := selbergS3GaussianScale delta X
  let G : ℝ := delta ^ (-2 : ℝ)
  let K : ℝ := 64 * (X : ℝ) ^ 4
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hB : 0 < B := by
    dsimp [B, selbergS3GaussianScale]
    positivity
  have hG : 0 < G := by
    dsimp [G]
    exact Real.rpow_pos_of_pos hdelta _
  have hGone : 1 ≤ G := by
    dsimp [G]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta hdelta1 (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hBG : 0 < B * G := mul_pos hB hG
  have hz : 0 < B * G ^ 2 := by positivity
  have hmajor : IntegrableOn
      (fun u : ℝ => K * Real.exp (-(B * G) * u)) (Ioi G) := by
    exact (integrableOn_exp_mul_Ioi (a := -(B * G)) (by linarith) G).const_mul K
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioi G),
      Complex.normSq (selbergPhysicalThetaKernel delta u X) ≤
        K * Real.exp (-(B * G) * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hG.trans hu
    have hsq : G ^ 2 ≤ u ^ 2 :=
      (sq_le_sq₀ hG.le hu0.le).2 hu.le
    have hscaleU : 1 / 2 ≤ B * u ^ 2 := by
      have hmono : B * G ^ 2 ≤ B * u ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hB.le
      have hend : 1 / 2 ≤ B * G ^ 2 := by
        simpa only [B, G] using hendpoint
      exact hend.trans hmono
    have hkernel := normSq_selbergPhysicalThetaKernel_le_s3
      hdelta hdelta1 hX hu0 (by simpa only [B] using hscaleU)
    have hexp : Real.exp (-(B * u ^ 2)) ≤
        Real.exp (-(B * G) * u) := by
      apply Real.exp_le_exp.mpr
      have hGu : G * u ≤ u ^ 2 := by nlinarith
      nlinarith
    calc
      Complex.normSq (selbergPhysicalThetaKernel delta u X) ≤
          64 * (X : ℝ) ^ 4 * Real.exp (-(B * u ^ 2)) := by
        simpa only [B] using hkernel
      _ ≤ K * Real.exp (-(B * G) * u) := by
        dsimp only [K]
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hmain :
      (∫ u in Ioi G,
        Complex.normSq (selbergPhysicalThetaKernel delta u X)) ≤
        ∫ u in Ioi G, K * Real.exp (-(B * G) * u) := by
    apply integral_mono_ae
    · exact (integrableOn_selbergPhysicalThetaKernel_normSq
        hdelta hdelta1 hX).mono_set (fun _u hu => hGone.trans_lt hu)
    · exact hmajor
    · exact hpoint
  have hvalue :
      (∫ u in Ioi G, K * Real.exp (-(B * G) * u)) =
        K * (Real.exp (-(B * G ^ 2)) / (B * G)) := by
    rw [integral_const_mul,
      integral_exp_mul_Ioi (a := -(B * G)) (by linarith) G]
    congr 1
    field_simp [hBG.ne']
  have hexpInv : Real.exp (-(B * G ^ 2)) ≤ (B * G ^ 2)⁻¹ :=
    exp_neg_le_inv hz
  calc
    (∫ u in Ioi (delta ^ (-2 : ℝ)),
        Complex.normSq (selbergPhysicalThetaKernel delta u X)) =
      ∫ u in Ioi G,
        Complex.normSq (selbergPhysicalThetaKernel delta u X) := rfl
    _ ≤ ∫ u in Ioi G, K * Real.exp (-(B * G) * u) := hmain
    _ = K * (Real.exp (-(B * G ^ 2)) / (B * G)) := hvalue
    _ ≤ K * ((B * G ^ 2)⁻¹ / (B * G)) := by
      gcongr
    _ = 64 * (X : ℝ) ^ 4 /
        (selbergS3GaussianScale delta X ^ 2 *
          (delta ^ (-2 : ℝ)) ^ 3) := by
      dsimp [K, B, G]
      field_simp [hB.ne', hG.ne']

theorem selbergS3GaussianScale_delta_endpoint
    {c delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hc : 0 ≤ c) (hcEight : c < 1 / 8)
    {X : ℕ} (hX : 2 ≤ X) (hXpow : (X : ℝ) ≤ delta ^ (-c)) :
    1 / 2 ≤ selbergS3GaussianScale delta X *
      (delta ^ (-2 : ℝ)) ^ 2 := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  let D : ℝ := delta ^ (-(1 / 2 : ℝ))
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hfourth : (X : ℝ) ^ 4 ≤ D := by
    dsimp only [D]
    exact selberg_fourth_power_le_delta_neg_half
      hdelta hdelta1 hc hcEight hX hXpow
  have hXone : (1 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hXtwoFour : (X : ℝ) ^ 2 ≤ (X : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((X : ℝ) ^ 2 - 1)]
  have hDdelta : D * delta ^ 3 ≤ 1 := by
    have heq : D * delta ^ 3 = delta ^ (5 / 2 : ℝ) := by
      dsimp [D]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hdelta]
      congr 1
      norm_num
    rw [heq]
    exact Real.rpow_le_one hdelta.le hdelta1 (by norm_num)
  have hprod : (X : ℝ) ^ 2 * delta ^ 3 ≤ 1 := by
    calc
      (X : ℝ) ^ 2 * delta ^ 3 ≤ D * delta ^ 3 :=
        mul_le_mul_of_nonneg_right (hXtwoFour.trans hfourth) (by positivity)
      _ ≤ 1 := hDdelta
  have hden : 0 < 2 * (X : ℝ) ^ 2 * delta ^ 3 := by positivity
  have hform : selbergS3GaussianScale delta X *
      (delta ^ (-2 : ℝ)) ^ 2 =
        1 / (2 * (X : ℝ) ^ 2 * delta ^ 3) := by
    unfold selbergS3GaussianScale
    rw [Real.rpow_neg hdelta.le, Real.rpow_two]
    field_simp [hdelta.ne', hXpos.ne']
  rw [hform, le_div_iff₀ hden]
  nlinarith

theorem selbergS3_raw_tail_rhs_eq
    {delta : ℝ} (hdelta : 0 < delta) {X : ℕ} (hX : 1 ≤ X) :
    64 * (X : ℝ) ^ 4 /
        (selbergS3GaussianScale delta X ^ 2 *
          (delta ^ (-2 : ℝ)) ^ 3) =
      256 * (X : ℝ) ^ 8 * delta ^ 4 := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX.trans_lt' zero_lt_one
  unfold selbergS3GaussianScale
  rw [Real.rpow_neg hdelta.le, Real.rpow_two]
  field_simp [hdelta.ne', hXpos.ne']
  ring

theorem exists_integral_normSq_selbergPhysicalThetaKernel_delta_tail_le
    {c : ℝ} (hc : 0 ≤ c) (hcEight : c < 1 / 8) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X →
        (X : ℝ) ≤ delta ^ (-c) →
        (∫ u in Ioi (delta ^ (-2 : ℝ)),
          Complex.normSq (selbergPhysicalThetaKernel delta u X)) ≤
          C * delta ^ (-(1 / 2 : ℝ)) := by
  refine ⟨256, by norm_num, ?_⟩
  intro X delta hdelta hdelta1 hX hXpow
  have hraw := integral_normSq_selbergPhysicalThetaKernel_delta_tail_le_raw
    hdelta hdelta1 hX
      (selbergS3GaussianScale_delta_endpoint
        hdelta hdelta1 hc hcEight hX hXpow)
  have hrawForm := selbergS3_raw_tail_rhs_eq hdelta
    (hX.trans' (by norm_num))
  have hfourth := selberg_fourth_power_le_delta_neg_half
    hdelta hdelta1 hc hcEight hX hXpow
  let D : ℝ := delta ^ (-(1 / 2 : ℝ))
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hX8 : (X : ℝ) ^ 8 ≤ D ^ 2 := by
    calc
      (X : ℝ) ^ 8 = ((X : ℝ) ^ 4) ^ 2 := by ring
      _ ≤ D ^ 2 := pow_le_pow_left₀ (by positivity) hfourth 2
  have hDsq : D ^ 2 = delta⁻¹ := by
    dsimp [D]
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul hdelta.le]
    norm_num [Real.rpow_neg_one]
  have hdeltaBound : D ^ 2 * delta ^ 4 ≤ D := by
    rw [hDsq]
    field_simp [hdelta.ne']
    have hdeltaCube : delta ^ 3 ≤ 1 := by
      exact pow_le_one₀ hdelta.le hdelta1
    have hDone : 1 ≤ D := by
      dsimp [D]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdelta1 (by norm_num)
    nlinarith
  calc
    (∫ u in Ioi (delta ^ (-2 : ℝ)),
        Complex.normSq (selbergPhysicalThetaKernel delta u X)) ≤
      64 * (X : ℝ) ^ 4 /
        (selbergS3GaussianScale delta X ^ 2 *
          (delta ^ (-2 : ℝ)) ^ 3) := hraw
    _ = 256 * (X : ℝ) ^ 8 * delta ^ 4 := hrawForm
    _ ≤ 256 * (D ^ 2 * delta ^ 4) := by
      rw [show 256 * (X : ℝ) ^ 8 * delta ^ 4 =
        256 * ((X : ℝ) ^ 8 * delta ^ 4) by ring]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hX8 (by positivity)) (by norm_num)
    _ ≤ 256 * D := by gcongr
    _ = 256 * delta ^ (-(1 / 2 : ℝ)) := rfl

end HardyTheorem
