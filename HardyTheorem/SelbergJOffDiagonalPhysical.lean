import HardyTheorem.SelbergJPairAlgebra
import HardyTheorem.SelbergDiagonalRemainderSum
import HardyTheorem.SelbergOffDiagonalParameter
import HardyTheorem.SelbergOffDiagonalTwoSides

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-! # Physical ordered off-diagonal pair sums for Selberg's `J` -/

noncomputable def selbergPhysicalPairMollifierCoefficient
    (X kappa lambda mu nu : ℕ) : ℂ :=
  ((selbergSqrtZetaTaperedCoeff X kappa : ℂ) *
      (selbergSqrtZetaTaperedCoeff X lambda : ℂ) /
      (lambda : ℂ)) *
    ((selbergSqrtZetaTaperedCoeff X mu : ℂ) *
      (selbergSqrtZetaTaperedCoeff X nu : ℂ) /
      (nu : ℂ))

private theorem abs_selbergPhysicalTaperedCoeff_le_one
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

theorem norm_selbergPhysicalPairMollifierCoefficient_le
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    ‖selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu‖ ≤
      (((lambda * nu : ℕ) : ℝ))⁻¹ := by
  have hk := abs_selbergPhysicalTaperedCoeff_le_one hX hkappa hkappaX
  have hl := abs_selbergPhysicalTaperedCoeff_le_one hX hlambda hlambdaX
  have hm := abs_selbergPhysicalTaperedCoeff_le_one hX hmu hmuX
  have hn := abs_selbergPhysicalTaperedCoeff_le_one hX hnu hnuX
  have hprod :
      |selbergSqrtZetaTaperedCoeff X kappa| *
          |selbergSqrtZetaTaperedCoeff X lambda| *
          |selbergSqrtZetaTaperedCoeff X mu| *
          |selbergSqrtZetaTaperedCoeff X nu| ≤ 1 := by
    calc
      |selbergSqrtZetaTaperedCoeff X kappa| *
            |selbergSqrtZetaTaperedCoeff X lambda| *
            |selbergSqrtZetaTaperedCoeff X mu| *
            |selbergSqrtZetaTaperedCoeff X nu| ≤
          1 * 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  unfold selbergPhysicalPairMollifierCoefficient
  rw [norm_mul, norm_div, norm_div, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_nonneg, abs_of_nonneg]
  have hl0 : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hn0 : (0 : ℝ) < nu := by exact_mod_cast hnu
  rw [show ‖(lambda : ℂ)‖ = (lambda : ℝ) by simp,
    show ‖(nu : ℂ)‖ = (nu : ℝ) by simp]
  push_cast
  rw [inv_eq_one_div]
  calc
    (|selbergSqrtZetaTaperedCoeff X kappa| *
          |selbergSqrtZetaTaperedCoeff X lambda| / lambda) *
        (|selbergSqrtZetaTaperedCoeff X mu| *
          |selbergSqrtZetaTaperedCoeff X nu| / nu) =
      (|selbergSqrtZetaTaperedCoeff X kappa| *
          |selbergSqrtZetaTaperedCoeff X lambda| *
          |selbergSqrtZetaTaperedCoeff X mu| *
          |selbergSqrtZetaTaperedCoeff X nu|) /
        ((lambda : ℝ) * (nu : ℝ)) := by field_simp
    _ ≤ 1 / ((lambda : ℝ) * (nu : ℝ)) := by
      exact div_le_div_of_nonneg_right hprod (by positivity)

noncomputable def selbergPhysicalOffDiagonalPairContribution
    (delta x theta : ℝ) (X m kappa lambda n mu nu : ℕ) : ℂ :=
  selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu *
    ∫ u in Ioi x,
      selbergPhysicalPairIntegrand delta theta u
        m kappa lambda n mu nu

theorem selbergPhysicalPairDamping_first_le
    {delta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 0 ≤ x) (m kappa lambda n mu nu : ℕ) :
    Real.exp
        (-selbergPhysicalPairDamping delta m kappa lambda n mu nu * x ^ 2) ≤
      Real.exp
        (-(selbergOffDiagonalGaussianParameter delta kappa lambda *
          (m : ℝ) ^ 2) * x ^ 2) := by
  have hsin0 : 0 ≤ Real.sin delta := by
    have hdeltaPi : delta < Real.pi :=
      hdelta1.trans_lt (by linarith [Real.pi_gt_three])
    exact (Real.sin_pos_of_pos_of_lt_pi hdelta hdeltaPi).le
  have hratio2 : 0 ≤ selbergPhysicalSquareRatio n mu nu := by
    unfold selbergPhysicalSquareRatio
    positivity
  have hfirst : selbergOffDiagonalGaussianParameter delta kappa lambda *
      (m : ℝ) ^ 2 =
      Real.pi * Real.sin delta * selbergPhysicalSquareRatio m kappa lambda := by
    unfold selbergOffDiagonalGaussianParameter selbergPhysicalSquareRatio
    push_cast
    ring
  apply Real.exp_le_exp.mpr
  rw [hfirst]
  unfold selbergPhysicalPairDamping
  have hcoef : 0 ≤ Real.pi * Real.sin delta :=
    mul_nonneg Real.pi_pos.le hsin0
  nlinarith [mul_nonneg hcoef hratio2, sq_nonneg x]

theorem norm_selbergPhysicalOffDiagonalPairContribution_forward_le
    {delta x theta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    {X m kappa lambda n mu nu : ℕ} (hX : 2 ≤ X)
    (hm : 1 ≤ m)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X)
    (hgap : n * lambda * mu < m * kappa * nu) :
    ‖selbergPhysicalOffDiagonalPairContribution
        delta x theta X m kappa lambda n mu nu‖ ≤
      (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
        (Real.exp
            (-selbergOffDiagonalGaussianParameter delta kappa lambda *
              (m : ℝ) ^ 2) *
          ((((lambda * nu : ℕ) : ℝ))⁻¹ *
            ((selbergPhysicalSquareRatio m kappa lambda -
              selbergPhysicalSquareRatio n mu nu)⁻¹))) := by
  have hcoeff := norm_selbergPhysicalPairMollifierCoefficient_le hX
    hkappa hkappaX hlambda hlambdaX hmu hmuX hnu hnuX
  have hint := norm_integral_Ioi_selbergPhysicalPairIntegrand_forward_le
    hdelta hdelta1 htheta hx hm hkappa hlambda hnu hgap
  have hexp := selbergPhysicalPairDamping_first_le
    hdelta hdelta1 (zero_le_one.trans hx) m kappa lambda n mu nu
  have ha0 : 0 ≤ selbergOffDiagonalGaussianParameter delta kappa lambda *
      (m : ℝ) ^ 2 := by
    unfold selbergOffDiagonalGaussianParameter
    have hsin0 : 0 ≤ Real.sin delta :=
      (Real.sin_pos_of_pos_of_lt_pi hdelta
        (hdelta1.trans_lt (by linarith [Real.pi_gt_three]))).le
    positivity
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hexpDrop : Real.exp
      (-(selbergOffDiagonalGaussianParameter delta kappa lambda *
        (m : ℝ) ^ 2) * x ^ 2) ≤
      Real.exp
        (-selbergOffDiagonalGaussianParameter delta kappa lambda *
          (m : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexpFinal := hexp.trans hexpDrop
  have hcos : 0 < Real.cos delta :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have hD := selberg_nat_square_gap_pos hm hkappa hlambda hnu hgap
  have hQpos := selbergPhysicalPairGapFrequency_pos_of_forward
    hdelta.le hdelta1 hm hkappa hlambda hnu hgap
  have hQ : selbergPhysicalPairGapFrequency delta m kappa lambda n mu nu =
      Real.pi * Real.cos delta *
        (selbergPhysicalSquareRatio m kappa lambda -
          selbergPhysicalSquareRatio n mu nu) := rfl
  unfold selbergPhysicalOffDiagonalPairContribution
  rw [norm_mul]
  calc
    ‖selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu‖ *
        ‖∫ u in Ioi x,
          selbergPhysicalPairIntegrand delta theta u
            m kappa lambda n mu nu‖ ≤
      (((lambda * nu : ℕ) : ℝ))⁻¹ *
        (2 * Real.exp
            (-selbergPhysicalPairDamping delta m kappa lambda n mu nu * x ^ 2) *
          x ^ (-theta - 1) /
            selbergPhysicalPairGapFrequency delta m kappa lambda n mu nu) := by
      gcongr
    _ ≤ (((lambda * nu : ℕ) : ℝ))⁻¹ *
        (2 * Real.exp
            (-selbergOffDiagonalGaussianParameter delta kappa lambda *
              (m : ℝ) ^ 2) *
          x ^ (-theta - 1) /
            selbergPhysicalPairGapFrequency delta m kappa lambda n mu nu) := by
      gcongr
    _ = (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
        (Real.exp
            (-selbergOffDiagonalGaussianParameter delta kappa lambda *
              (m : ℝ) ^ 2) *
          ((((lambda * nu : ℕ) : ℝ))⁻¹ *
            ((selbergPhysicalSquareRatio m kappa lambda -
              selbergPhysicalSquareRatio n mu nu)⁻¹))) := by
      rw [hQ]
      field_simp [Real.pi_ne_zero, hcos.ne', hD.ne']

noncomputable def selbergPhysicalForwardFixedSum
    (delta x theta : ℝ) (X m kappa lambda mu nu : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1
      (selbergPositiveGapCount (m * kappa * nu) (lambda * mu)),
    selbergPhysicalOffDiagonalPairContribution
      delta x theta X m kappa lambda n mu nu

theorem norm_selbergPhysicalForwardFixedSum_le
    {delta x theta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    {X m kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hm : 1 ≤ m)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    ‖selbergPhysicalForwardFixedSum
        delta x theta X m kappa lambda mu nu‖ ≤
      (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
        selbergFixedSideSquareSum
          (selbergOffDiagonalGaussianParameter delta kappa lambda)
          m kappa lambda mu nu := by
  have hd : 1 ≤ lambda * mu := Nat.mul_pos hlambda hmu
  unfold selbergPhysicalForwardFixedSum selbergFixedSideSquareSum
  calc
    ‖∑ n ∈ Finset.Icc 1
        (selbergPositiveGapCount (m * kappa * nu) (lambda * mu)),
      selbergPhysicalOffDiagonalPairContribution
        delta x theta X m kappa lambda n mu nu‖ ≤
      ∑ n ∈ Finset.Icc 1
        (selbergPositiveGapCount (m * kappa * nu) (lambda * mu)),
        ‖selbergPhysicalOffDiagonalPairContribution
          delta x theta X m kappa lambda n mu nu‖ := by
      simpa only using norm_sum_le (Finset.Icc 1
        (selbergPositiveGapCount (m * kappa * nu) (lambda * mu)))
        (fun n => selbergPhysicalOffDiagonalPairContribution
          delta x theta X m kappa lambda n mu nu)
    _ ≤ ∑ n ∈ Finset.Icc 1
        (selbergPositiveGapCount (m * kappa * nu) (lambda * mu)),
        (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
          (Real.exp
              (-selbergOffDiagonalGaussianParameter delta kappa lambda *
                (m : ℝ) ^ 2) *
            ((((lambda * nu : ℕ) : ℝ))⁻¹ *
              ((((m * kappa : ℕ) : ℝ) ^ 2 / (lambda : ℝ) ^ 2 -
                ((n * mu : ℕ) : ℝ) ^ 2 / (nu : ℝ) ^ 2)⁻¹))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hgap : n * lambda * mu < m * kappa * nu := by
        simpa only [mul_assoc] using
          ((selberg_positive_gap_admissible_iff hd).mpr hn |>.2)
      simpa only [selbergPhysicalSquareRatio] using
        (norm_selbergPhysicalOffDiagonalPairContribution_forward_le
          hdelta hdelta1 hx htheta hX hm hkappa hkappaX
          hlambda hlambdaX hmu hmuX hnu hnuX hgap)
    _ = (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
        (∑ n ∈ Finset.Icc 1
          (selbergPositiveGapCount (m * kappa * nu) (lambda * mu)),
          Real.exp
              (-selbergOffDiagonalGaussianParameter delta kappa lambda *
                (m : ℝ) ^ 2) *
            ((((lambda * nu : ℕ) : ℝ))⁻¹ *
              ((((m * kappa : ℕ) : ℝ) ^ 2 / (lambda : ℝ) ^ 2 -
                ((n * mu : ℕ) : ℝ) ^ 2 / (nu : ℝ) ^ 2)⁻¹))) := by
      rw [Finset.mul_sum]

noncomputable def selbergPhysicalForwardRaySum
    (delta x theta : ℝ) (X kappa lambda mu nu : ℕ) : ℂ :=
  ∑' j : ℕ, selbergPhysicalForwardFixedSum
    delta x theta X (j + 1) kappa lambda mu nu

theorem summable_selbergPhysicalForwardFixedSum_add_one
    {delta x theta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    Summable (fun j : ℕ => selbergPhysicalForwardFixedSum
      delta x theta X (j + 1) kappa lambda mu nu) := by
  let C : ℝ := 2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)
  have hcos : 0 < Real.cos delta :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have ha0 : 0 < selbergOffDiagonalGaussianParameter delta kappa lambda := by
    unfold selbergOffDiagonalGaussianParameter
    have hsin : 0 < Real.sin delta :=
      Real.sin_pos_of_pos_of_lt_pi hdelta
        (hdelta1.trans_lt (by linarith [Real.pi_gt_three]))
    positivity
  have hsquare := summable_selbergFixedSideSquareSum_add_one
    ha0 hkappa hlambda hmu hnu hkappaX hnuX
      (hX.trans' (by norm_num))
  have hmajor : Summable (fun j : ℕ => C *
      selbergFixedSideSquareSum
        (selbergOffDiagonalGaussianParameter delta kappa lambda)
        (j + 1) kappa lambda mu nu) := hsquare.mul_left C
  apply Summable.of_norm_bounded hmajor
  intro j
  exact norm_selbergPhysicalForwardFixedSum_le
    hdelta hdelta1 hx htheta hX (Nat.le_add_left 1 j)
      hkappa hkappaX hlambda hlambdaX hmu hmuX hnu hnuX

theorem norm_selbergPhysicalForwardRaySum_le
    {delta x theta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    ‖selbergPhysicalForwardRaySum
        delta x theta X kappa lambda mu nu‖ ≤
      (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
        (∑' j : ℕ, selbergFixedSideSquareSum
          (selbergOffDiagonalGaussianParameter delta kappa lambda)
          (j + 1) kappa lambda mu nu) := by
  let C : ℝ := 2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)
  have hsum := summable_selbergPhysicalForwardFixedSum_add_one
    hdelta hdelta1 hx htheta hX hkappa hkappaX hlambda hlambdaX
      hmu hmuX hnu hnuX
  have hnorm := hsum.norm
  have ha0 : 0 < selbergOffDiagonalGaussianParameter delta kappa lambda := by
    unfold selbergOffDiagonalGaussianParameter
    have hsin : 0 < Real.sin delta :=
      Real.sin_pos_of_pos_of_lt_pi hdelta
        (hdelta1.trans_lt (by linarith [Real.pi_gt_three]))
    positivity
  have hsquare := summable_selbergFixedSideSquareSum_add_one
    ha0 hkappa hlambda hmu hnu hkappaX hnuX
      (hX.trans' (by norm_num))
  have hcos : 0 < Real.cos delta :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hmajor := hsquare.mul_left C
  unfold selbergPhysicalForwardRaySum
  calc
    ‖∑' j : ℕ, selbergPhysicalForwardFixedSum
        delta x theta X (j + 1) kappa lambda mu nu‖ ≤
      ∑' j : ℕ, ‖selbergPhysicalForwardFixedSum
        delta x theta X (j + 1) kappa lambda mu nu‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, C * selbergFixedSideSquareSum
        (selbergOffDiagonalGaussianParameter delta kappa lambda)
        (j + 1) kappa lambda mu nu := by
      exact hnorm.tsum_le_tsum
        (fun j => norm_selbergPhysicalForwardFixedSum_le
          hdelta hdelta1 hx htheta hX (Nat.le_add_left 1 j)
            hkappa hkappaX hlambda hlambdaX hmu hmuX hnu hnuX)
        hmajor
    _ = C * (∑' j : ℕ, selbergFixedSideSquareSum
        (selbergOffDiagonalGaussianParameter delta kappa lambda)
        (j + 1) kappa lambda mu nu) :=
      Summable.tsum_mul_left C hsquare
    _ = _ := rfl

noncomputable def selbergPhysicalPositiveOffDiagonalSum
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑ kappa ∈ Finset.Icc 1 X,
    ∑ lambda ∈ Finset.Icc 1 X,
      ∑ mu ∈ Finset.Icc 1 X,
        ∑ nu ∈ Finset.Icc 1 X,
          selbergPhysicalForwardRaySum
            delta x theta X kappa lambda mu nu

theorem norm_selbergPhysicalPositiveOffDiagonalSum_le
    {delta x theta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    {X : ℕ} (hX : 2 ≤ X) :
    ‖selbergPhysicalPositiveOffDiagonalSum delta x theta X‖ ≤
      (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
        selbergOffDiagonalPositiveSquareSum delta X := by
  let C : ℝ := 2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)
  have hcos : 0 < Real.cos delta :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  unfold selbergPhysicalPositiveOffDiagonalSum
    selbergOffDiagonalPositiveSquareSum
  calc
    ‖∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              selbergPhysicalForwardRaySum
                delta x theta X kappa lambda mu nu‖ ≤
      ∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              ‖selbergPhysicalForwardRaySum
                delta x theta X kappa lambda mu nu‖ := by
      calc
        _ ≤ ∑ kappa ∈ Finset.Icc 1 X,
            ‖∑ lambda ∈ Finset.Icc 1 X,
              ∑ mu ∈ Finset.Icc 1 X,
                ∑ nu ∈ Finset.Icc 1 X,
                  selbergPhysicalForwardRaySum
                    delta x theta X kappa lambda mu nu‖ :=
          norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro kappa hkappa
          calc
            _ ≤ ∑ lambda ∈ Finset.Icc 1 X,
                ‖∑ mu ∈ Finset.Icc 1 X,
                  ∑ nu ∈ Finset.Icc 1 X,
                    selbergPhysicalForwardRaySum
                      delta x theta X kappa lambda mu nu‖ := norm_sum_le _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro lambda hlambda
              calc
                _ ≤ ∑ mu ∈ Finset.Icc 1 X,
                    ‖∑ nu ∈ Finset.Icc 1 X,
                      selbergPhysicalForwardRaySum
                        delta x theta X kappa lambda mu nu‖ := norm_sum_le _ _
                _ ≤ _ := by
                  apply Finset.sum_le_sum
                  intro mu hmu
                  exact norm_sum_le _ _
    _ ≤ ∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              C * (∑' j : ℕ, selbergFixedSideSquareSum
                (selbergOffDiagonalGaussianParameter delta kappa lambda)
                (j + 1) kappa lambda mu nu) := by
      apply Finset.sum_le_sum
      intro kappa hkappa
      apply Finset.sum_le_sum
      intro lambda hlambda
      apply Finset.sum_le_sum
      intro mu hmu
      apply Finset.sum_le_sum
      intro nu hnu
      exact norm_selbergPhysicalForwardRaySum_le
        hdelta hdelta1 hx htheta hX
        (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hkappa).2
        (Finset.mem_Icc.mp hlambda).1 (Finset.mem_Icc.mp hlambda).2
        (Finset.mem_Icc.mp hmu).1 (Finset.mem_Icc.mp hmu).2
        (Finset.mem_Icc.mp hnu).1 (Finset.mem_Icc.mp hnu).2
    _ = C * (∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              ∑' j : ℕ, selbergFixedSideSquareSum
                (selbergOffDiagonalGaussianParameter delta kappa lambda)
                (j + 1) kappa lambda mu nu) := by
      simp_rw [Finset.mul_sum]
    _ = _ := rfl

/-- The reverse ordered side after the simultaneous swap
`(m,kappa,lambda) <-> (n,mu,nu)`. -/
noncomputable def selbergPhysicalReverseOffDiagonalSum
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  ∑ kappa ∈ Finset.Icc 1 X,
    ∑ lambda ∈ Finset.Icc 1 X,
      ∑ mu ∈ Finset.Icc 1 X,
        ∑ nu ∈ Finset.Icc 1 X,
          (starRingEnd ℂ) (selbergPhysicalForwardRaySum
            delta x theta X mu nu kappa lambda)

theorem norm_selbergPhysicalReverseOffDiagonalSum_le
    {delta x theta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    {X : ℕ} (hX : 2 ≤ X) :
    ‖selbergPhysicalReverseOffDiagonalSum delta x theta X‖ ≤
      (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
        selbergOffDiagonalReverseSquareSum delta X := by
  let C : ℝ := 2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)
  unfold selbergPhysicalReverseOffDiagonalSum
    selbergOffDiagonalReverseSquareSum
  calc
    ‖∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              (starRingEnd ℂ) (selbergPhysicalForwardRaySum
                delta x theta X mu nu kappa lambda)‖ ≤
      ∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              ‖(starRingEnd ℂ) (selbergPhysicalForwardRaySum
                delta x theta X mu nu kappa lambda)‖ := by
      calc
        _ ≤ ∑ kappa ∈ Finset.Icc 1 X,
            ‖∑ lambda ∈ Finset.Icc 1 X,
              ∑ mu ∈ Finset.Icc 1 X,
                ∑ nu ∈ Finset.Icc 1 X,
                  (starRingEnd ℂ) (selbergPhysicalForwardRaySum
                    delta x theta X mu nu kappa lambda)‖ := norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro kappa hkappa
          calc
            _ ≤ ∑ lambda ∈ Finset.Icc 1 X,
                ‖∑ mu ∈ Finset.Icc 1 X,
                  ∑ nu ∈ Finset.Icc 1 X,
                    (starRingEnd ℂ) (selbergPhysicalForwardRaySum
                      delta x theta X mu nu kappa lambda)‖ := norm_sum_le _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro lambda hlambda
              calc
                _ ≤ ∑ mu ∈ Finset.Icc 1 X,
                    ‖∑ nu ∈ Finset.Icc 1 X,
                      (starRingEnd ℂ) (selbergPhysicalForwardRaySum
                        delta x theta X mu nu kappa lambda)‖ := norm_sum_le _ _
                _ ≤ _ := by
                  apply Finset.sum_le_sum
                  intro mu hmu
                  exact norm_sum_le _ _
    _ = ∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              ‖selbergPhysicalForwardRaySum
                delta x theta X mu nu kappa lambda‖ := by
      simp only [Complex.norm_conj]
    _ ≤ ∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              C * (∑' j : ℕ, selbergFixedSideSquareSum
                (selbergOffDiagonalGaussianParameter delta mu nu)
                (j + 1) mu nu kappa lambda) := by
      apply Finset.sum_le_sum
      intro kappa hkappa
      apply Finset.sum_le_sum
      intro lambda hlambda
      apply Finset.sum_le_sum
      intro mu hmu
      apply Finset.sum_le_sum
      intro nu hnu
      exact norm_selbergPhysicalForwardRaySum_le
        hdelta hdelta1 hx htheta hX
        (Finset.mem_Icc.mp hmu).1 (Finset.mem_Icc.mp hmu).2
        (Finset.mem_Icc.mp hnu).1 (Finset.mem_Icc.mp hnu).2
        (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hkappa).2
        (Finset.mem_Icc.mp hlambda).1 (Finset.mem_Icc.mp hlambda).2
    _ = C * (∑ kappa ∈ Finset.Icc 1 X,
        ∑ lambda ∈ Finset.Icc 1 X,
          ∑ mu ∈ Finset.Icc 1 X,
            ∑ nu ∈ Finset.Icc 1 X,
              ∑' j : ℕ, selbergFixedSideSquareSum
                (selbergOffDiagonalGaussianParameter delta mu nu)
                (j + 1) mu nu kappa lambda) := by
      simp_rw [Finset.mul_sum]
    _ = _ := rfl

noncomputable def selbergPhysicalOffDiagonalSum
    (delta x theta : ℝ) (X : ℕ) : ℂ :=
  selbergPhysicalPositiveOffDiagonalSum delta x theta X +
    selbergPhysicalReverseOffDiagonalSum delta x theta X

theorem norm_selbergPhysicalOffDiagonalSum_le_oscillatoryMajorant
    {delta x theta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    {X : ℕ} (hX : 2 ≤ X) :
    ‖selbergPhysicalOffDiagonalSum delta x theta X‖ ≤
      selbergOffDiagonalOscillatoryMajorant delta x theta X := by
  have hpos := norm_selbergPhysicalPositiveOffDiagonalSum_le
    hdelta hdelta1 hx htheta hX
  have hrev := norm_selbergPhysicalReverseOffDiagonalSum_le
    hdelta hdelta1 hx htheta hX
  unfold selbergPhysicalOffDiagonalSum
    selbergOffDiagonalOscillatoryMajorant
    selbergOffDiagonalTwoSideSquareSum
  calc
    ‖selbergPhysicalPositiveOffDiagonalSum delta x theta X +
        selbergPhysicalReverseOffDiagonalSum delta x theta X‖ ≤
      ‖selbergPhysicalPositiveOffDiagonalSum delta x theta X‖ +
        ‖selbergPhysicalReverseOffDiagonalSum delta x theta X‖ := norm_add_le _ _
    _ ≤ (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
          selbergOffDiagonalPositiveSquareSum delta X +
        (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
          selbergOffDiagonalReverseSquareSum delta X := add_le_add hpos hrev
    _ = (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
        (selbergOffDiagonalPositiveSquareSum delta X +
          selbergOffDiagonalReverseSquareSum delta X) := by ring

end HardyTheorem
