import HardyTheorem.SelbergDiagonalKernelPointwise
import Mathlib.MeasureTheory.Function.Floor

open Filter MeasureTheory Real Set Topology

namespace HardyTheorem

/-! # Integrating the Euler remainder in Selberg's diagonal kernel. -/

theorem measurable_selbergEulerFloorPowerSum (theta : ℝ) :
    Measurable (selbergEulerFloorPowerSum theta) := by
  let A : ℕ → ℝ := fun N =>
    ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ) ^ (theta - 1))
  have hA : Measurable A := measurable_of_countable A
  have hfloor : Measurable (fun z : ℝ => Nat.floor z) := Nat.measurable_floor
  change Measurable (fun z : ℝ => A (Nat.floor z))
  exact hA.comp hfloor

theorem measurable_selbergEulerFloorError (theta : ℝ) :
    Measurable (selbergEulerFloorError theta) := by
  unfold selbergEulerFloorError
  apply Measurable.sub (measurable_selbergEulerFloorPowerSum theta)
  measurability

theorem aestronglyMeasurable_selbergDiagonalEulerErrorIntegrand_Ioi
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x) :
    AEStronglyMeasurable (selbergDiagonalEulerErrorIntegrand eta x theta)
      (volume.restrict (Set.Ioi (x * Real.sqrt eta))) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi |>.mul ?_
  · intro y hy
    have hy0 : 0 < y := (mul_pos hx (Real.sqrt_pos.2 heta)).trans hy
    have hweighted : ContinuousAt (selbergWeightedGaussian theta) y := by
      unfold selbergWeightedGaussian
      exact (Real.continuousAt_rpow_const y (-theta) (Or.inl hy0.ne')).mul
        (by fun_prop)
    exact (continuousAt_const.mul hweighted).continuousWithinAt
  · exact ((measurable_selbergEulerFloorError theta).comp
      (by fun_prop : Measurable (fun y : ℝ => y / (x * Real.sqrt eta))))
      |>.aestronglyMeasurable.restrict

theorem integrableOn_selbergDiagonalEulerErrorIntegrand_Ioi
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    IntegrableOn (selbergDiagonalEulerErrorIntegrand eta x theta)
      (Set.Ioi (x * Real.sqrt eta)) := by
  let C : ℝ := x ^ (1 - theta)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  have htail := integrableOn_selbergDiagonalLogTail_Ioi ha
  have hmajor : IntegrableOn (fun y : ℝ => C * selbergDiagonalLogTail y)
      (Set.Ioi (x * Real.sqrt eta)) := htail.const_mul C
  apply Integrable.mono' hmajor
  · exact aestronglyMeasurable_selbergDiagonalEulerErrorIntegrand_Ioi heta hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs]
    exact abs_selbergDiagonalEulerErrorIntegrand_le
      heta hx htheta0 hthetaHalf hy.le

theorem norm_integral_selbergDiagonalEulerErrorIntegrand_Ioi_le
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 1 ≤ x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    ‖∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalEulerErrorIntegrand eta x theta y‖ ≤
      x ^ (1 - theta) * Real.log (2 + eta⁻¹) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let C : ℝ := x ^ (1 - theta)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have ha : 0 < x * Real.sqrt eta := mul_pos hx0 (Real.sqrt_pos.2 heta)
  have htail := integrableOn_selbergDiagonalLogTail_Ioi ha
  have hmajor : IntegrableOn (fun y : ℝ => C * selbergDiagonalLogTail y)
      (Set.Ioi (x * Real.sqrt eta)) := htail.const_mul C
  calc
    ‖∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalEulerErrorIntegrand eta x theta y‖ ≤
        ∫ y in Set.Ioi (x * Real.sqrt eta),
          C * selbergDiagonalLogTail y := by
      apply MeasureTheory.norm_integral_le_of_norm_le hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [Real.norm_eq_abs]
      exact abs_selbergDiagonalEulerErrorIntegrand_le
        heta hx0 htheta0 hthetaHalf hy.le
    _ = C * ∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalLogTail y := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ C * Real.log (2 + (x * Real.sqrt eta)⁻¹ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (integral_selbergDiagonalLogTail_Ioi_le_log ha) hC0
    _ ≤ C * Real.log (2 + eta⁻¹) := by
      exact mul_le_mul_of_nonneg_left (log_tail_argument_le_eta hx heta) hC0
    _ = x ^ (1 - theta) * Real.log (2 + eta⁻¹) := rfl

noncomputable def selbergDiagonalMainCoefficient
    (eta x theta : ℝ) : ℝ :=
  eta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) / theta

theorem selberg_rpow_main_algebra
    {a y theta : ℝ} (ha : 0 < a) (hy : 0 < y) :
    y ^ (-theta) * (y / a) ^ theta = a ^ (-theta) := by
  rw [Real.div_rpow hy.le ha.le]
  calc
    y ^ (-theta) * (y ^ theta / a ^ theta) =
        (y ^ (-theta) * y ^ theta) / a ^ theta := by ring
    _ = 1 / a ^ theta := by
      rw [← Real.rpow_add hy]
      norm_num
    _ = a ^ (-theta) := by
      rw [Real.rpow_neg ha.le]
      exact one_div (a ^ theta)

theorem selbergEtaSqrtMainCancellation
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x) :
    eta ^ ((theta - 1) / 2) *
        (x * Real.sqrt eta) ^ (-theta) =
      eta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) := by
  have hsqrt0 : 0 < Real.sqrt eta := Real.sqrt_pos.2 heta
  rw [Real.mul_rpow hx.le hsqrt0.le]
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul heta.le]
  calc
    eta ^ ((theta - 1) / 2) *
        (x ^ (-theta) * eta ^ ((1 / 2 : ℝ) * (-theta))) =
        x ^ (-theta) *
          (eta ^ ((theta - 1) / 2) * eta ^ ((1 / 2 : ℝ) * (-theta))) := by
      ring
    _ = x ^ (-theta) *
        eta ^ ((theta - 1) / 2 + (1 / 2 : ℝ) * (-theta)) := by
      rw [Real.rpow_add heta]
    _ = x ^ (-theta) * eta ^ (-(1 / 2 : ℝ)) := by
      congr 1
      ring
    _ = eta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) := by ring

theorem selbergDiagonalEulerMainIntegrand_eq
    {eta x theta y : ℝ} (heta : 0 < eta) (hx : 0 < x) (hy : 0 < y) :
    selbergDiagonalEulerMainIntegrand eta x theta y =
      selbergDiagonalMainCoefficient eta x theta * Real.exp (-y ^ 2) := by
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  unfold selbergDiagonalEulerMainIntegrand selbergWeightedGaussian
  unfold selbergDiagonalMainCoefficient
  calc
    eta ^ ((theta - 1) / 2) * (y ^ (-theta) * Real.exp (-y ^ 2)) *
        ((y / (x * Real.sqrt eta)) ^ theta / theta) =
        (eta ^ ((theta - 1) / 2) *
          (y ^ (-theta) * (y / (x * Real.sqrt eta)) ^ theta)) /
            theta * Real.exp (-y ^ 2) := by ring
    _ = (eta ^ ((theta - 1) / 2) *
          (x * Real.sqrt eta) ^ (-theta)) / theta *
            Real.exp (-y ^ 2) := by
      rw [selberg_rpow_main_algebra ha hy]
    _ = (eta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) / theta) *
        Real.exp (-y ^ 2) := by
      rw [selbergEtaSqrtMainCancellation heta hx]

noncomputable def selbergDiagonalConstantCoefficient
    (eta theta : ℝ) : ℝ :=
  eta ^ ((theta - 1) / 2) *
    (selbergEulerPowerConstant theta / theta)

theorem selbergDiagonalEulerConstantIntegrand_eq
    {eta x theta y : ℝ} :
    selbergDiagonalEulerConstantIntegrand eta x theta y =
      selbergDiagonalConstantCoefficient eta theta *
        selbergWeightedGaussian theta y := by
  unfold selbergDiagonalEulerConstantIntegrand
  unfold selbergDiagonalConstantCoefficient
  ring

theorem integral_Ioi_gaussian_eq_full_sub_lower
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ y in Set.Ioi a, Real.exp (-y ^ 2)) =
      Real.sqrt Real.pi / 2 - ∫ y in 0..a, Real.exp (-y ^ 2) := by
  have hfull : IntegrableOn (fun y : ℝ => Real.exp (-y ^ 2)) (Set.Ioi 0) := by
    simpa only [neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn
  have htail := hfull.mono_set (Set.Ioi_subset_Ioi ha)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull htail
  have hgauss : (∫ y in Set.Ioi (0 : ℝ), Real.exp (-y ^ 2)) =
      Real.sqrt Real.pi / 2 := by
    simpa using integral_gaussian_Ioi (1 : ℝ)
  linarith

theorem integral_Ioi_weightedGaussian_eq_full_sub_lower
    {theta a : ℝ} (htheta1 : theta < 1) (ha : 0 ≤ a) :
    (∫ y in Set.Ioi a, selbergWeightedGaussian theta y) =
      (1 / 2 : ℝ) * Real.Gamma ((1 - theta) / 2) -
        ∫ y in 0..a, selbergWeightedGaussian theta y := by
  have hfull : IntegrableOn (selbergWeightedGaussian theta) (Set.Ioi 0) := by
    unfold selbergWeightedGaussian
    simpa only [neg_mul, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_sq
        (s := -theta) (by norm_num : (0 : ℝ) < 1) (by linarith))
  have htail := hfull.mono_set (Set.Ioi_subset_Ioi ha)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull htail
  rw [integral_selbergWeightedGaussian_Ioi htheta1] at hsplit
  linarith

theorem integral_selbergDiagonalEulerMainIntegrand_Ioi
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x) :
    (∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalEulerMainIntegrand eta x theta y) =
      selbergDiagonalMainCoefficient eta x theta *
        (Real.sqrt Real.pi / 2 -
          ∫ y in 0..(x * Real.sqrt eta), Real.exp (-y ^ 2)) := by
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  calc
    (∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalEulerMainIntegrand eta x theta y) =
        ∫ y in Set.Ioi (x * Real.sqrt eta),
          selbergDiagonalMainCoefficient eta x theta * Real.exp (-y ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact selbergDiagonalEulerMainIntegrand_eq heta hx (ha.trans hy)
    _ = selbergDiagonalMainCoefficient eta x theta *
        ∫ y in Set.Ioi (x * Real.sqrt eta), Real.exp (-y ^ 2) := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by rw [integral_Ioi_gaussian_eq_full_sub_lower ha.le]

theorem integral_selbergDiagonalEulerConstantIntegrand_Ioi
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta1 : theta < 1) :
    (∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalEulerConstantIntegrand eta x theta y) =
      selbergDiagonalConstantCoefficient eta theta *
        ((1 / 2 : ℝ) * Real.Gamma ((1 - theta) / 2) -
          ∫ y in 0..(x * Real.sqrt eta),
            selbergWeightedGaussian theta y) := by
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  calc
    (∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalEulerConstantIntegrand eta x theta y) =
        ∫ y in Set.Ioi (x * Real.sqrt eta),
          selbergDiagonalConstantCoefficient eta theta *
            selbergWeightedGaussian theta y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      exact selbergDiagonalEulerConstantIntegrand_eq
    _ = selbergDiagonalConstantCoefficient eta theta *
        ∫ y in Set.Ioi (x * Real.sqrt eta),
          selbergWeightedGaussian theta y := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [integral_Ioi_weightedGaussian_eq_full_sub_lower htheta1 ha.le]

noncomputable def selbergDiagonalFloorKernel
    (eta x theta : ℝ) : ℝ :=
  ∫ y in Set.Ioi (x * Real.sqrt eta),
    selbergDiagonalFloorKernelIntegrand eta x theta y

noncomputable def selbergDiagonalEulerRemainder
    (eta x theta : ℝ) : ℝ :=
  ∫ y in Set.Ioi (x * Real.sqrt eta),
    selbergDiagonalEulerErrorIntegrand eta x theta y

theorem integrableOn_selbergDiagonalEulerMainIntegrand_Ioi
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x) :
    IntegrableOn (selbergDiagonalEulerMainIntegrand eta x theta)
      (Set.Ioi (x * Real.sqrt eta)) := by
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  have hgauss : IntegrableOn (fun y : ℝ => Real.exp (-y ^ 2))
      (Set.Ioi (x * Real.sqrt eta)) := by
    have hfull : IntegrableOn (fun y : ℝ => Real.exp (-y ^ 2))
        (Set.Ioi 0) := by
      simpa only [neg_mul, one_mul] using
        (integrable_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1)).integrableOn
    exact hfull.mono_set (Set.Ioi_subset_Ioi ha.le)
  refine IntegrableOn.congr_fun
    (hgauss.const_mul (selbergDiagonalMainCoefficient eta x theta))
    ?_ measurableSet_Ioi
  intro y hy
  exact (selbergDiagonalEulerMainIntegrand_eq heta hx (ha.trans hy)).symm

theorem integrableOn_selbergDiagonalEulerConstantIntegrand_Ioi
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta1 : theta < 1) :
    IntegrableOn (selbergDiagonalEulerConstantIntegrand eta x theta)
      (Set.Ioi (x * Real.sqrt eta)) := by
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  have hweighted : IntegrableOn (selbergWeightedGaussian theta)
      (Set.Ioi (x * Real.sqrt eta)) := by
    have hfull : IntegrableOn (selbergWeightedGaussian theta) (Set.Ioi 0) := by
      unfold selbergWeightedGaussian
      simpa only [neg_mul, one_mul] using
        (integrableOn_rpow_mul_exp_neg_mul_sq
          (s := -theta) (by norm_num : (0 : ℝ) < 1) (by linarith))
    exact hfull.mono_set (Set.Ioi_subset_Ioi ha.le)
  refine IntegrableOn.congr_fun
    (hweighted.const_mul (selbergDiagonalConstantCoefficient eta theta))
    ?_ measurableSet_Ioi
  intro y _hy
  exact selbergDiagonalEulerConstantIntegrand_eq.symm

theorem integrableOn_selbergDiagonalFloorKernelIntegrand_Ioi
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    IntegrableOn (selbergDiagonalFloorKernelIntegrand eta x theta)
      (Set.Ioi (x * Real.sqrt eta)) := by
  have htheta1 : theta < 1 := hthetaHalf.trans_lt (by norm_num)
  have hmain := integrableOn_selbergDiagonalEulerMainIntegrand_Ioi
    (theta := theta) heta hx
  have hconst := integrableOn_selbergDiagonalEulerConstantIntegrand_Ioi
    heta hx htheta1
  have herr := integrableOn_selbergDiagonalEulerErrorIntegrand_Ioi
    heta hx htheta0 hthetaHalf
  refine IntegrableOn.congr_fun ((hmain.add hconst).add herr) ?_
    measurableSet_Ioi
  intro y _hy
  exact selbergDiagonalFloorKernelIntegrand_decomposition.symm

theorem selbergDiagonalFloorKernel_eq_three_integrals
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    selbergDiagonalFloorKernel eta x theta =
      (∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalEulerMainIntegrand eta x theta y) +
      (∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalEulerConstantIntegrand eta x theta y) +
      selbergDiagonalEulerRemainder eta x theta := by
  have htheta1 : theta < 1 := hthetaHalf.trans_lt (by norm_num)
  have hmain := integrableOn_selbergDiagonalEulerMainIntegrand_Ioi
    (theta := theta) heta hx
  have hconst := integrableOn_selbergDiagonalEulerConstantIntegrand_Ioi
    heta hx htheta1
  have herr := integrableOn_selbergDiagonalEulerErrorIntegrand_Ioi
    heta hx htheta0 hthetaHalf
  unfold selbergDiagonalFloorKernel selbergDiagonalEulerRemainder
  calc
    (∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalFloorKernelIntegrand eta x theta y) =
        ∫ y in Set.Ioi (x * Real.sqrt eta),
          (selbergDiagonalEulerMainIntegrand eta x theta y +
            selbergDiagonalEulerConstantIntegrand eta x theta y) +
              selbergDiagonalEulerErrorIntegrand eta x theta y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      exact selbergDiagonalFloorKernelIntegrand_decomposition
    _ = ∫ y in Set.Ioi (x * Real.sqrt eta),
          (((selbergDiagonalEulerMainIntegrand eta x theta) +
            (selbergDiagonalEulerConstantIntegrand eta x theta)) +
              (selbergDiagonalEulerErrorIntegrand eta x theta)) y := rfl
    _ = (∫ y in Set.Ioi (x * Real.sqrt eta),
          ((selbergDiagonalEulerMainIntegrand eta x theta) +
            (selbergDiagonalEulerConstantIntegrand eta x theta)) y) +
        ∫ y in Set.Ioi (x * Real.sqrt eta),
          selbergDiagonalEulerErrorIntegrand eta x theta y := by
      exact MeasureTheory.integral_add (hmain.add hconst) herr
    _ = _ := by
      exact congrArg
        (fun z : ℝ => z + ∫ y in Set.Ioi (x * Real.sqrt eta),
          selbergDiagonalEulerErrorIntegrand eta x theta y)
        (MeasureTheory.integral_add hmain hconst)

theorem selbergDiagonalFloorKernel_exact_decomposition
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    selbergDiagonalFloorKernel eta x theta =
      selbergDiagonalMainCoefficient eta x theta *
        (Real.sqrt Real.pi / 2 -
          ∫ y in 0..(x * Real.sqrt eta), Real.exp (-y ^ 2)) +
      selbergDiagonalConstantCoefficient eta theta *
        ((1 / 2 : ℝ) * Real.Gamma ((1 - theta) / 2) -
          ∫ y in 0..(x * Real.sqrt eta),
            selbergWeightedGaussian theta y) +
      selbergDiagonalEulerRemainder eta x theta := by
  rw [selbergDiagonalFloorKernel_eq_three_integrals
    heta hx htheta0 hthetaHalf]
  rw [integral_selbergDiagonalEulerMainIntegrand_Ioi heta hx]
  rw [integral_selbergDiagonalEulerConstantIntegrand_Ioi
    heta hx (hthetaHalf.trans_lt (by norm_num))]

noncomputable def selbergDiagonalTitchMain
    (eta x theta : ℝ) : ℝ :=
  selbergDiagonalMainCoefficient eta x theta *
      (Real.sqrt Real.pi / 2) +
    (selbergDiagonalK1 theta / theta) *
      eta ^ ((theta - 1) / 2)

noncomputable def selbergDiagonalLowCorrection
    (eta x theta : ℝ) : ℝ :=
  selbergDiagonalMainCoefficient eta x theta *
      (∫ y in 0..(x * Real.sqrt eta), Real.exp (-y ^ 2)) +
    selbergDiagonalConstantCoefficient eta theta *
      (∫ y in 0..(x * Real.sqrt eta),
        selbergWeightedGaussian theta y)

theorem selbergDiagonalFullConstantTerm_eq
    {eta theta : ℝ} :
    selbergDiagonalConstantCoefficient eta theta *
        ((1 / 2 : ℝ) * Real.Gamma ((1 - theta) / 2)) =
      (selbergDiagonalK1 theta / theta) *
        eta ^ ((theta - 1) / 2) := by
  unfold selbergDiagonalConstantCoefficient selbergDiagonalK1
  ring

theorem selbergDiagonalFloorKernel_eq_titchMain_sub_correction_add_remainder
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    selbergDiagonalFloorKernel eta x theta =
      selbergDiagonalTitchMain eta x theta -
        selbergDiagonalLowCorrection eta x theta +
          selbergDiagonalEulerRemainder eta x theta := by
  rw [selbergDiagonalFloorKernel_exact_decomposition
    heta hx htheta0 hthetaHalf]
  rw [mul_sub, mul_sub]
  rw [selbergDiagonalFullConstantTerm_eq]
  unfold selbergDiagonalTitchMain selbergDiagonalLowCorrection
  ring

theorem norm_selbergDiagonalEulerRemainder_le
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 1 ≤ x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    ‖selbergDiagonalEulerRemainder eta x theta‖ ≤
      x ^ (1 - theta) * Real.log (2 + eta⁻¹) := by
  unfold selbergDiagonalEulerRemainder
  exact norm_integral_selbergDiagonalEulerErrorIntegrand_Ioi_le
    heta hx htheta0 hthetaHalf

theorem selbergDiagonalMainCoefficient_nonneg
    {eta x theta : ℝ} (heta : 0 ≤ eta) (hx : 0 ≤ x)
    (htheta : 0 ≤ theta) :
    0 ≤ selbergDiagonalMainCoefficient eta x theta := by
  unfold selbergDiagonalMainCoefficient
  positivity

theorem selbergDiagonalMainCoefficient_mul_scale
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x) :
    selbergDiagonalMainCoefficient eta x theta *
        (x * Real.sqrt eta) =
      x ^ (1 - theta) / theta := by
  have hetaProd : eta ^ (-(1 / 2 : ℝ)) * Real.sqrt eta = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add heta]
    norm_num
  have hxProd : x ^ (-theta) * x = x ^ (1 - theta) := by
    calc
      x ^ (-theta) * x = x ^ (-theta) * x ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = x ^ (-theta + 1) := by rw [Real.rpow_add hx]
      _ = x ^ (1 - theta) := by congr 1 <;> ring
  unfold selbergDiagonalMainCoefficient
  calc
    (eta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) / theta) *
        (x * Real.sqrt eta) =
      (x ^ (-theta) * x) *
        (eta ^ (-(1 / 2 : ℝ)) * Real.sqrt eta) / theta := by ring
    _ = x ^ (1 - theta) / theta := by rw [hetaProd, hxProd, mul_one]

theorem abs_selbergDiagonalMainLowTerm_le
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta : 0 < theta) :
    |selbergDiagonalMainCoefficient eta x theta *
        (∫ y in 0..(x * Real.sqrt eta), Real.exp (-y ^ 2))| ≤
      x ^ (1 - theta) / theta := by
  have ha : 0 ≤ x * Real.sqrt eta :=
    (mul_pos hx (Real.sqrt_pos.2 heta)).le
  have hC : 0 ≤ selbergDiagonalMainCoefficient eta x theta :=
    selbergDiagonalMainCoefficient_nonneg heta.le hx.le htheta.le
  have hI0 := intervalIntegral_selbergGaussian_zero_le ha
  have hIle := intervalIntegral_selbergGaussian_le_length ha
  rw [abs_mul, abs_of_nonneg hC, abs_of_nonneg hI0]
  calc
    selbergDiagonalMainCoefficient eta x theta *
        (∫ y in 0..(x * Real.sqrt eta), Real.exp (-y ^ 2)) ≤
      selbergDiagonalMainCoefficient eta x theta *
        (x * Real.sqrt eta) := mul_le_mul_of_nonneg_left hIle hC
    _ = x ^ (1 - theta) / theta :=
      selbergDiagonalMainCoefficient_mul_scale heta hx

theorem abs_selbergDiagonalConstantCoefficient_le
    {eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 < theta)
    (hthetaHalf : theta ≤ 1 / 2) :
    |selbergDiagonalConstantCoefficient eta theta| ≤
      eta ^ ((theta - 1) / 2) / theta := by
  unfold selbergDiagonalConstantCoefficient
  rw [abs_mul, abs_div,
    abs_of_nonneg (Real.rpow_nonneg heta ((theta - 1) / 2)),
    abs_of_pos htheta]
  have hK := abs_selbergEulerPowerConstant_le_one htheta hthetaHalf
  calc
    eta ^ ((theta - 1) / 2) *
        (|selbergEulerPowerConstant theta| / theta) =
      (eta ^ ((theta - 1) / 2) *
        |selbergEulerPowerConstant theta|) / theta := by ring
    _ ≤ (eta ^ ((theta - 1) / 2) * 1) / theta :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK
          (Real.rpow_nonneg heta ((theta - 1) / 2))) htheta.le
    _ = eta ^ ((theta - 1) / 2) / theta := by rw [mul_one]

theorem selbergDiagonalConstantScaleCancellation
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x) :
    (eta ^ ((theta - 1) / 2) / theta) *
        ((x * Real.sqrt eta) ^ (1 - theta) / (1 - theta)) =
      x ^ (1 - theta) / (theta * (1 - theta)) := by
  have hcancel := selbergEtaSqrtCancellation
    (theta := theta) heta hx
  calc
    (eta ^ ((theta - 1) / 2) / theta) *
        ((x * Real.sqrt eta) ^ (1 - theta) / (1 - theta)) =
      (eta ^ ((theta - 1) / 2) *
        (x * Real.sqrt eta) ^ (1 - theta)) /
          (theta * (1 - theta)) := by
        simp only [div_eq_mul_inv]
        rw [mul_inv_rev]
        ring
    _ = x ^ (1 - theta) / (theta * (1 - theta)) := by rw [hcancel]

theorem abs_selbergDiagonalConstantLowTerm_le
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta : 0 < theta) (htheta1 : theta < 1)
    (hthetaHalf : theta ≤ 1 / 2) :
    |selbergDiagonalConstantCoefficient eta theta *
        (∫ y in 0..(x * Real.sqrt eta),
          selbergWeightedGaussian theta y)| ≤
      x ^ (1 - theta) / (theta * (1 - theta)) := by
  have ha : 0 ≤ x * Real.sqrt eta :=
    (mul_pos hx (Real.sqrt_pos.2 heta)).le
  have hI0 := intervalIntegral_selbergWeightedGaussian_zero_le
    (theta := theta) ha
  have hIle := intervalIntegral_selbergWeightedGaussian_le_rpow
    htheta.le htheta1 ha
  have hCoeff := abs_selbergDiagonalConstantCoefficient_le
    heta.le htheta hthetaHalf
  have hScale0 : 0 ≤ eta ^ ((theta - 1) / 2) / theta :=
    div_nonneg (Real.rpow_nonneg heta.le _) htheta.le
  rw [abs_mul, abs_of_nonneg hI0]
  calc
    |selbergDiagonalConstantCoefficient eta theta| *
        (∫ y in 0..(x * Real.sqrt eta),
          selbergWeightedGaussian theta y) ≤
      (eta ^ ((theta - 1) / 2) / theta) *
        (∫ y in 0..(x * Real.sqrt eta),
          selbergWeightedGaussian theta y) :=
        mul_le_mul_of_nonneg_right hCoeff hI0
    _ ≤ (eta ^ ((theta - 1) / 2) / theta) *
        ((x * Real.sqrt eta) ^ (1 - theta) / (1 - theta)) :=
      mul_le_mul_of_nonneg_left hIle hScale0
    _ = x ^ (1 - theta) / (theta * (1 - theta)) :=
      selbergDiagonalConstantScaleCancellation heta hx

theorem abs_selbergDiagonalLowCorrection_le
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    |selbergDiagonalLowCorrection eta x theta| ≤
      x ^ (1 - theta) / theta +
        x ^ (1 - theta) / (theta * (1 - theta)) := by
  unfold selbergDiagonalLowCorrection
  calc
    |selbergDiagonalMainCoefficient eta x theta *
          (∫ y in 0..(x * Real.sqrt eta), Real.exp (-y ^ 2)) +
        selbergDiagonalConstantCoefficient eta theta *
          (∫ y in 0..(x * Real.sqrt eta),
            selbergWeightedGaussian theta y)| ≤
      |selbergDiagonalMainCoefficient eta x theta *
          (∫ y in 0..(x * Real.sqrt eta), Real.exp (-y ^ 2))| +
        |selbergDiagonalConstantCoefficient eta theta *
          (∫ y in 0..(x * Real.sqrt eta),
            selbergWeightedGaussian theta y)| := abs_add_le _ _
    _ ≤ x ^ (1 - theta) / theta +
        x ^ (1 - theta) / (theta * (1 - theta)) :=
      add_le_add
        (abs_selbergDiagonalMainLowTerm_le heta hx htheta)
        (abs_selbergDiagonalConstantLowTerm_le heta hx htheta
          (hthetaHalf.trans_lt (by norm_num)) hthetaHalf)

theorem abs_selbergDiagonalLowCorrection_le_three
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    |selbergDiagonalLowCorrection eta x theta| ≤
      3 * (x ^ (1 - theta) / theta) := by
  have hbase0 : 0 ≤ x ^ (1 - theta) / theta :=
    div_nonneg (Real.rpow_nonneg hx.le _) htheta.le
  have honeTheta : 0 < 1 - theta := by linarith
  have hsecond :
      x ^ (1 - theta) / (theta * (1 - theta)) ≤
        2 * (x ^ (1 - theta) / theta) := by
    rw [← div_div]
    apply (div_le_iff₀ honeTheta).2
    nlinarith
  calc
    |selbergDiagonalLowCorrection eta x theta| ≤
        x ^ (1 - theta) / theta +
          x ^ (1 - theta) / (theta * (1 - theta)) :=
      abs_selbergDiagonalLowCorrection_le heta hx htheta hthetaHalf
    _ ≤ x ^ (1 - theta) / theta +
        2 * (x ^ (1 - theta) / theta) :=
      add_le_add le_rfl hsecond
    _ = 3 * (x ^ (1 - theta) / theta) := by ring

theorem abs_selbergDiagonalFloorKernel_sub_titchMain_le
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 1 ≤ x)
    (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    |selbergDiagonalFloorKernel eta x theta -
        selbergDiagonalTitchMain eta x theta| ≤
      3 * (x ^ (1 - theta) / theta) +
        x ^ (1 - theta) * Real.log (2 + eta⁻¹) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  rw [selbergDiagonalFloorKernel_eq_titchMain_sub_correction_add_remainder
    heta hx0 htheta hthetaHalf]
  have hrewrite :
      selbergDiagonalTitchMain eta x theta -
          selbergDiagonalLowCorrection eta x theta +
            selbergDiagonalEulerRemainder eta x theta -
              selbergDiagonalTitchMain eta x theta =
        -selbergDiagonalLowCorrection eta x theta +
          selbergDiagonalEulerRemainder eta x theta := by ring
  rw [hrewrite]
  calc
    |-selbergDiagonalLowCorrection eta x theta +
        selbergDiagonalEulerRemainder eta x theta| ≤
      |-selbergDiagonalLowCorrection eta x theta| +
        |selbergDiagonalEulerRemainder eta x theta| := abs_add_le _ _
    _ = |selbergDiagonalLowCorrection eta x theta| +
        |selbergDiagonalEulerRemainder eta x theta| := by rw [abs_neg]
    _ ≤ 3 * (x ^ (1 - theta) / theta) +
        x ^ (1 - theta) * Real.log (2 + eta⁻¹) := by
      apply add_le_add
      · exact abs_selbergDiagonalLowCorrection_le_three
          heta hx0 htheta hthetaHalf
      · simpa only [Real.norm_eq_abs] using
          norm_selbergDiagonalEulerRemainder_le
            heta hx htheta hthetaHalf

end HardyTheorem
