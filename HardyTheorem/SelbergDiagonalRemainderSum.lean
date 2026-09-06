import HardyTheorem.SelbergDiagonalRemainderParameter

open Complex
open scoped BigOperators

namespace HardyTheorem

/-! # The summed non-arithmetic remainder in Selberg's diagonal estimate. -/

private theorem abs_selbergDiagonalTaperedCoeff_le_one
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

noncomputable def selbergDiagonalMollifierBase
    (X kappa nu mu lambda : ℕ) : ℂ :=
  selbergDiagonalMollifierProduct X kappa nu mu lambda /
    ((nu : ℂ) * (lambda : ℂ))

theorem norm_selbergDiagonalMollifierBase_le_one
    {X kappa nu mu lambda : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X) :
    ‖selbergDiagonalMollifierBase X kappa nu mu lambda‖ ≤ 1 := by
  have hk := abs_selbergDiagonalTaperedCoeff_le_one hX hkappa hkappaX
  have hn := abs_selbergDiagonalTaperedCoeff_le_one hX hnu hnuX
  have hm := abs_selbergDiagonalTaperedCoeff_le_one hX hmu hmuX
  have hl := abs_selbergDiagonalTaperedCoeff_le_one hX hlambda hlambdaX
  have hprod :
      |selbergSqrtZetaTaperedCoeff X kappa| *
          |selbergSqrtZetaTaperedCoeff X nu| *
          |selbergSqrtZetaTaperedCoeff X mu| *
          |selbergSqrtZetaTaperedCoeff X lambda| ≤ 1 := by
    calc
      |selbergSqrtZetaTaperedCoeff X kappa| *
            |selbergSqrtZetaTaperedCoeff X nu| *
            |selbergSqrtZetaTaperedCoeff X mu| *
            |selbergSqrtZetaTaperedCoeff X lambda| ≤
          1 * 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hden : (1 : ℝ) ≤ (nu : ℝ) * (lambda : ℝ) := by
    exact_mod_cast Nat.mul_le_mul hnu hlambda
  unfold selbergDiagonalMollifierBase selbergDiagonalMollifierProduct
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hnNorm : ‖(nu : ℂ)‖ = (nu : ℝ) := by simp
  have hlNorm : ‖(lambda : ℂ)‖ = (lambda : ℝ) := by simp
  rw [hnNorm, hlNorm]
  rw [div_le_iff₀ (by positivity : 0 < (nu : ℝ) * (lambda : ℝ))]
  simpa only [one_mul] using hprod.trans hden

theorem selbergArithmeticDiagonalGcd_le_sq
    {X : ℕ} (p q : selbergTaperIndex X × selbergTaperIndex X) :
    selbergArithmeticDiagonalGcd p q ≤ X ^ 2 := by
  have hp1 : 1 ≤ p.1.1 := (Finset.mem_Icc.mp p.1.2).1
  have hpX : p.1.1 ≤ X := (Finset.mem_Icc.mp p.1.2).2
  have hp2X : p.2.1 ≤ X := (Finset.mem_Icc.mp p.2.2).2
  calc
    selbergArithmeticDiagonalGcd p q ≤ p.1.1 * p.2.1 := by
      exact Nat.gcd_le_left _ (Nat.mul_pos hp1 (Finset.mem_Icc.mp p.2.2).1)
    _ ≤ X ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hpX hp2X

noncomputable def selbergDiagonalPhysicalRemainderPairTerm
    (delta x theta : ℝ) (X : ℕ)
    (p q : selbergTaperIndex X × selbergTaperIndex X) : ℂ :=
  selbergDiagonalMollifierBase X p.1.1 p.2.1 q.1.1 q.2.1 *
    ((selbergDiagonalFloorKernel
        (selbergDiagonalGaussianParameter delta p.1.1 q.1.1
          (selbergArithmeticDiagonalGcd p q)) x theta -
      selbergDiagonalTitchMain
        (selbergDiagonalGaussianParameter delta p.1.1 q.1.1
          (selbergArithmeticDiagonalGcd p q)) x theta : ℝ) : ℂ)

theorem norm_selbergDiagonalPhysicalRemainderPairTerm_le
    {delta x theta : ℝ} {X : ℕ}
    (p q : selbergTaperIndex X × selbergTaperIndex X)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : 2 ≤ X) (hx : 1 ≤ x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    ‖selbergDiagonalPhysicalRemainderPairTerm delta x theta X p q‖ ≤
      3 * (x ^ (1 - theta) / theta) +
        x ^ (1 - theta) * Real.log (2 + (X : ℝ) ^ 4 / delta) := by
  have hkappa : 1 ≤ p.1.1 := (Finset.mem_Icc.mp p.1.2).1
  have hkappaX : p.1.1 ≤ X := (Finset.mem_Icc.mp p.1.2).2
  have hnu : 1 ≤ p.2.1 := (Finset.mem_Icc.mp p.2.2).1
  have hnuX : p.2.1 ≤ X := (Finset.mem_Icc.mp p.2.2).2
  have hmu : 1 ≤ q.1.1 := (Finset.mem_Icc.mp q.1.2).1
  have hmuX : q.1.1 ≤ X := (Finset.mem_Icc.mp q.1.2).2
  have hlambda : 1 ≤ q.2.1 := (Finset.mem_Icc.mp q.2.2).1
  have hlambdaX : q.2.1 ≤ X := (Finset.mem_Icc.mp q.2.2).2
  have hg : 1 ≤ selbergArithmeticDiagonalGcd p q :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
      (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hkappa hnu)))
  let eta := selbergDiagonalGaussianParameter delta p.1.1 q.1.1
    (selbergArithmeticDiagonalGcd p q)
  have heta : 0 < eta := selbergDiagonalGaussianParameter_pos
    hdelta0 (hdelta1.trans_lt (by linarith [Real.pi_gt_three]))
      hkappa hmu hg
  have hbase := norm_selbergDiagonalMollifierBase_le_one hX
    hkappa hkappaX hnu hnuX hmu hmuX hlambda hlambdaX
  have hkernel := abs_selbergDiagonalFloorKernel_sub_titchMain_le
    heta hx htheta0 hthetaHalf
  have hlog := log_two_add_inv_selbergDiagonalGaussianParameter_le
    hdelta0 hdelta1 (hX.trans' (by norm_num)) hkappa hmu hg
      (selbergArithmeticDiagonalGcd_le_sq p q)
  have hkernelUniform :
      |selbergDiagonalFloorKernel eta x theta -
          selbergDiagonalTitchMain eta x theta| ≤
        3 * (x ^ (1 - theta) / theta) +
          x ^ (1 - theta) * Real.log (2 + (X : ℝ) ^ 4 / delta) := by
    exact hkernel.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hlog
        (Real.rpow_nonneg (zero_le_one.trans hx) _)))
  unfold selbergDiagonalPhysicalRemainderPairTerm
  change ‖selbergDiagonalMollifierBase X p.1.1 p.2.1 q.1.1 q.2.1 *
    ((selbergDiagonalFloorKernel eta x theta -
      selbergDiagonalTitchMain eta x theta : ℝ) : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖selbergDiagonalMollifierBase X p.1.1 p.2.1 q.1.1 q.2.1‖ *
        |selbergDiagonalFloorKernel eta x theta -
          selbergDiagonalTitchMain eta x theta| ≤
      1 * (3 * (x ^ (1 - theta) / theta) +
        x ^ (1 - theta) * Real.log (2 + (X : ℝ) ^ 4 / delta)) := by
        gcongr
    _ = _ := one_mul _

noncomputable def selbergDiagonalPhysicalRemainderSum
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑ p : selbergTaperIndex X × selbergTaperIndex X,
    ∑ q : selbergTaperIndex X × selbergTaperIndex X,
      selbergDiagonalPhysicalRemainderPairTerm delta x theta X p q

private noncomputable def selbergTaperIndexEquivAttach (X : ℕ) :
    selbergTaperIndex X ≃
      {n // n ∈ (Finset.Icc 1 X).attach} where
  toFun n := ⟨n, Finset.mem_attach (Finset.Icc 1 X) n⟩
  invFun n := n.1
  left_inv _ := rfl
  right_inv n := by ext; rfl

private theorem card_selbergTaperIndex
    {X : ℕ} (hX : 1 ≤ X) :
    Fintype.card (selbergTaperIndex X) = X := by
  calc
    Fintype.card (selbergTaperIndex X) =
        Fintype.card {n // n ∈ (Finset.Icc 1 X).attach} :=
      Fintype.card_congr (selbergTaperIndexEquivAttach X)
    _ = (Finset.Icc 1 X).attach.card := Fintype.card_coe _
    _ = (Finset.Icc 1 X).card := Finset.card_attach
    _ = X := by rw [Nat.card_Icc]; omega

theorem norm_selbergDiagonalPhysicalRemainderSum_le
    {delta x theta : ℝ} {X : ℕ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hX : 2 ≤ X) (hx : 1 ≤ x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    ‖selbergDiagonalPhysicalRemainderSum delta x theta X‖ ≤
      (X : ℝ) ^ 4 *
        (3 * (x ^ (1 - theta) / theta) +
          x ^ (1 - theta) * Real.log (2 + (X : ℝ) ^ 4 / delta)) := by
  classical
  let P := selbergTaperIndex X × selbergTaperIndex X
  let E := 3 * (x ^ (1 - theta) / theta) +
    x ^ (1 - theta) * Real.log (2 + (X : ℝ) ^ 4 / delta)
  have hpair (p q : P) :
      ‖selbergDiagonalPhysicalRemainderPairTerm delta x theta X p q‖ ≤ E :=
    norm_selbergDiagonalPhysicalRemainderPairTerm_le p q
      hdelta0 hdelta1 hX hx htheta0 hthetaHalf
  have hcardT : Fintype.card (selbergTaperIndex X) = X :=
    card_selbergTaperIndex (hX.trans' (by norm_num))
  have hcardP : Fintype.card P = X ^ 2 := by
    dsimp [P]
    rw [Fintype.card_prod, hcardT]
    ring
  unfold selbergDiagonalPhysicalRemainderSum
  change ‖∑ p : P, ∑ q : P,
    selbergDiagonalPhysicalRemainderPairTerm delta x theta X p q‖ ≤ _
  calc
    ‖∑ p : P, ∑ q : P,
        selbergDiagonalPhysicalRemainderPairTerm delta x theta X p q‖ ≤
      ∑ p : P, ‖∑ q : P,
        selbergDiagonalPhysicalRemainderPairTerm delta x theta X p q‖ := by
          simpa only using norm_sum_le Finset.univ _
    _ ≤ ∑ p : P, ∑ q : P,
        ‖selbergDiagonalPhysicalRemainderPairTerm delta x theta X p q‖ := by
      apply Finset.sum_le_sum
      intro p _hp
      simpa only using norm_sum_le Finset.univ
        (fun q : P => selbergDiagonalPhysicalRemainderPairTerm
          delta x theta X p q)
    _ ≤ ∑ _p : P, ∑ _q : P, E := by
      apply Finset.sum_le_sum
      intro p _hp
      apply Finset.sum_le_sum
      intro q _hq
      exact hpair p q
    _ = (X : ℝ) ^ 4 * E := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ, hcardP]
      push_cast
      ring
    _ = _ := rfl

noncomputable def selbergDiagonalPhysicalFloorKernelSum
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑ p : selbergTaperIndex X × selbergTaperIndex X,
    ∑ q : selbergTaperIndex X × selbergTaperIndex X,
      selbergDiagonalMollifierBase X p.1.1 p.2.1 q.1.1 q.2.1 *
        (selbergDiagonalFloorKernel
          (selbergDiagonalGaussianParameter delta p.1.1 q.1.1
            (selbergArithmeticDiagonalGcd p q)) x theta : ℂ)

private theorem selbergDiagonalPhysicalFloorKernelPair_eq
    {delta x theta : ℝ} {X : ℕ}
    (p q : selbergTaperIndex X × selbergTaperIndex X) :
    selbergDiagonalMollifierBase X p.1.1 p.2.1 q.1.1 q.2.1 *
        (selbergDiagonalFloorKernel
          (selbergDiagonalGaussianParameter delta p.1.1 q.1.1
            (selbergArithmeticDiagonalGcd p q)) x theta : ℂ) =
      selbergDiagonalPhysicalMainPairTerm delta x theta X p q +
        selbergDiagonalPhysicalRemainderPairTerm delta x theta X p q := by
  unfold selbergDiagonalPhysicalMainPairTerm
    selbergDiagonalPhysicalMainTerm selbergDiagonalMollifierBase
    selbergDiagonalPhysicalRemainderPairTerm
  simp only [selbergDiagonalMollifierBase]
  push_cast
  ring

theorem selbergDiagonalPhysicalFloorKernelSum_eq_main_add_remainder
    {delta x theta : ℝ} {X : ℕ} :
    selbergDiagonalPhysicalFloorKernelSum delta x theta X =
      selbergDiagonalPhysicalMainSum delta x theta X +
        selbergDiagonalPhysicalRemainderSum delta x theta X := by
  classical
  unfold selbergDiagonalPhysicalFloorKernelSum
    selbergDiagonalPhysicalMainSum selbergDiagonalPhysicalRemainderSum
  simp_rw [selbergDiagonalPhysicalFloorKernelPair_eq]
  simp only [Finset.sum_add_distrib]

theorem exists_norm_selbergDiagonalPhysicalFloorKernelSum_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta x theta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → Real.exp 1 ≤ (X : ℝ) →
        1 ≤ x → 0 < theta → theta ≤ 1 / 2 →
        ‖selbergDiagonalPhysicalFloorKernelSum delta x theta X‖ ≤
          |selbergDiagonalSZeroCoefficient delta x theta| *
              (C / Real.log (X : ℝ)) +
            |selbergDiagonalSThetaCoefficient delta theta| *
              (C * ((X : ℝ) ^ (2 * theta)) /
                Real.log (X : ℝ)) +
            (X : ℝ) ^ 4 *
              (3 * (x ^ (1 - theta) / theta) +
                x ^ (1 - theta) *
                  Real.log (2 + (X : ℝ) ^ 4 / delta)) := by
  rcases exists_norm_selbergDiagonalPhysicalMainSum_le with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro X delta x theta hdelta0 hdelta1 hX hXexp hx htheta0 hthetaHalf
  have hdeltaPi : delta < Real.pi :=
    hdelta1.trans_lt (by linarith [Real.pi_gt_three])
  have hm := hmain X delta x theta hdelta0 hdeltaPi
    htheta0 hthetaHalf hXexp
  have hr := norm_selbergDiagonalPhysicalRemainderSum_le
    hdelta0 hdelta1 hX hx htheta0 hthetaHalf
  rw [selbergDiagonalPhysicalFloorKernelSum_eq_main_add_remainder]
  exact (norm_add_le _ _).trans (add_le_add hm hr)

noncomputable def selbergDiagonalPhysicalOriginalSum
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑ p : selbergTaperIndex X × selbergTaperIndex X,
    ∑ q : selbergTaperIndex X × selbergTaperIndex X,
      selbergDiagonalMollifierBase X p.1.1 p.2.1 q.1.1 q.2.1 *
        ((∑' n : ℕ,
          ∫ u in Set.Ioi x,
            selbergDiagonalOriginalIntegrand
              (selbergDiagonalGaussianParameter delta p.1.1 q.1.1
                (selbergArithmeticDiagonalGcd p q)) theta n u : ℝ) : ℂ)

theorem selbergDiagonalPhysicalOriginalSum_eq_floorKernelSum
    {delta x theta : ℝ} {X : ℕ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 0 < x) (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    selbergDiagonalPhysicalOriginalSum delta x theta X =
      selbergDiagonalPhysicalFloorKernelSum delta x theta X := by
  classical
  unfold selbergDiagonalPhysicalOriginalSum
    selbergDiagonalPhysicalFloorKernelSum
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  have hkappa : 0 < p.1.1 := (Finset.mem_Icc.mp p.1.2).1
  have hmu : 0 < q.1.1 := (Finset.mem_Icc.mp q.1.2).1
  have hg : 0 < selbergArithmeticDiagonalGcd p q :=
    Nat.gcd_pos_of_pos_left _
      (Nat.mul_pos hkappa (Finset.mem_Icc.mp p.2.2).1)
  have heta : 0 < selbergDiagonalGaussianParameter delta p.1.1 q.1.1
      (selbergArithmeticDiagonalGcd p q) :=
    selbergDiagonalGaussianParameter_pos hdelta0
      (hdelta1.trans_lt (by linarith [Real.pi_gt_three])) hkappa hmu hg
  rw [tsum_integral_selbergDiagonalOriginalIntegrand_eq_floorKernel
    heta hx htheta0 hthetaHalf]

end HardyTheorem
