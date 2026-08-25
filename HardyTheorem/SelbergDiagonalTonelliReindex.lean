import HardyTheorem.SelbergDiagonalTermSubstitution

open MeasureTheory Real Set
open scoped BigOperators

namespace HardyTheorem

/-! # Exact floor reindexing for Selberg's diagonal Tonelli step. -/

noncomputable def selbergFloorCutoffSummand
    (theta z : ℝ) (n : ℕ) : ℝ :=
  if (((n + 1 : ℕ) : ℝ) ≤ z) then
    (((n + 1 : ℕ) : ℝ) ^ (theta - 1))
  else 0

theorem tsum_selbergFloorCutoffSummand
    {theta z : ℝ} (hz : 0 ≤ z) :
    ∑' n : ℕ, selbergFloorCutoffSummand theta z n =
      selbergEulerFloorPowerSum theta z := by
  classical
  rw [tsum_eq_sum (s := Finset.range (Nat.floor z))]
  · unfold selbergEulerFloorPowerSum
    apply Finset.sum_congr rfl
    intro n hn
    rw [selbergFloorCutoffSummand, if_pos]
    have hnlt : n < Nat.floor z := Finset.mem_range.1 hn
    have hnle : n + 1 ≤ Nat.floor z := Nat.succ_le_iff.2 hnlt
    exact (Nat.cast_le.2 hnle).trans (Nat.floor_le hz)
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [selbergFloorCutoffSummand, if_neg]
    have hzlt : z < (((Nat.floor z + 1 : ℕ) : ℝ)) :=
      by simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one z
    have hcast : (((Nat.floor z + 1 : ℕ) : ℝ)) ≤
        (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.add_le_add_right hn 1
    exact not_le_of_gt (hzlt.trans_le hcast)

noncomputable def selbergDiagonalTonelliSummand
    (eta x theta y : ℝ) (n : ℕ) : ℝ :=
  (eta ^ ((theta - 1) / 2) * selbergWeightedGaussian theta y) *
    selbergFloorCutoffSummand theta
      (y / (x * Real.sqrt eta)) n

theorem tsum_selbergDiagonalTonelliSummand_eq_floorKernelIntegrand
    {eta x theta y : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (hy : 0 ≤ y) :
    ∑' n : ℕ, selbergDiagonalTonelliSummand eta x theta y n =
      selbergDiagonalFloorKernelIntegrand eta x theta y := by
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  have hz : 0 ≤ y / (x * Real.sqrt eta) := div_nonneg hy ha.le
  have hfloor := tsum_selbergFloorCutoffSummand
    (theta := theta) hz
  unfold selbergDiagonalTonelliSummand
  rw [tsum_mul_left]
  rw [hfloor]
  unfold selbergDiagonalFloorKernelIntegrand
  rfl

theorem selbergDiagonalScale_mul_x
    {eta x : ℝ} {n : ℕ} :
    selbergDiagonalScale eta n * x =
      (x * Real.sqrt eta) * (((n + 1 : ℕ) : ℝ)) := by
  unfold selbergDiagonalScale
  ring

theorem selbergDiagonalCutoff_iff_closedTail
    {eta x y : ℝ} {n : ℕ} (heta : 0 < eta) (hx : 0 < x) :
    (((n + 1 : ℕ) : ℝ) ≤ y / (x * Real.sqrt eta)) ↔
      selbergDiagonalScale eta n * x ≤ y := by
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  rw [selbergDiagonalScale_mul_x]
  simpa only [mul_comm] using
    (le_div_iff₀ ha :
      (((n + 1 : ℕ) : ℝ) ≤ y / (x * Real.sqrt eta)) ↔
        (((n + 1 : ℕ) : ℝ) * (x * Real.sqrt eta) ≤ y))

noncomputable def selbergDiagonalClosedTailSummand
    (eta x theta : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  (eta ^ ((theta - 1) / 2) *
      (((n + 1 : ℕ) : ℝ) ^ (theta - 1))) *
    (Set.Ici (selbergDiagonalScale eta n * x)).indicator
      (selbergWeightedGaussian theta) y

theorem selbergDiagonalTonelliSummand_eq_closedTail
    {eta x theta y : ℝ} {n : ℕ} (heta : 0 < eta) (hx : 0 < x) :
    selbergDiagonalTonelliSummand eta x theta y n =
      selbergDiagonalClosedTailSummand eta x theta n y := by
  by_cases hcut : (((n + 1 : ℕ) : ℝ) ≤
      y / (x * Real.sqrt eta))
  · have htail : y ∈ Set.Ici (selbergDiagonalScale eta n * x) :=
      selbergDiagonalCutoff_iff_closedTail heta hx |>.mp hcut
    unfold selbergDiagonalTonelliSummand selbergFloorCutoffSummand
    unfold selbergDiagonalClosedTailSummand
    rw [if_pos hcut, Set.indicator_of_mem htail]
    ring
  · have htail : y ∉ Set.Ici (selbergDiagonalScale eta n * x) := by
      intro hy
      exact hcut (selbergDiagonalCutoff_iff_closedTail heta hx |>.mpr hy)
    unfold selbergDiagonalTonelliSummand selbergFloorCutoffSummand
    unfold selbergDiagonalClosedTailSummand
    rw [if_neg hcut, Set.indicator_of_notMem htail]
    ring

theorem summable_selbergFloorCutoffSummand
    {theta z : ℝ} (hz : 0 ≤ z) :
    Summable (selbergFloorCutoffSummand theta z) := by
  classical
  apply summable_of_ne_finset_zero (s := Finset.range (Nat.floor z))
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  rw [selbergFloorCutoffSummand, if_neg]
  have hzlt : z < (((Nat.floor z + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one z
  have hcast : (((Nat.floor z + 1 : ℕ) : ℝ)) ≤
      (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_le_add_right hn 1
  exact not_le_of_gt (hzlt.trans_le hcast)

theorem summable_selbergDiagonalClosedTailSummand
    {eta x theta y : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (hy : 0 ≤ y) :
    Summable (fun n : ℕ =>
      selbergDiagonalClosedTailSummand eta x theta n y) := by
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  have hz : 0 ≤ y / (x * Real.sqrt eta) := div_nonneg hy ha.le
  have hs := (summable_selbergFloorCutoffSummand
    (theta := theta) hz).mul_left
      (eta ^ ((theta - 1) / 2) * selbergWeightedGaussian theta y)
  have hsTonelli : Summable (fun n : ℕ =>
      selbergDiagonalTonelliSummand eta x theta y n) := by
    simpa only [selbergDiagonalTonelliSummand] using hs
  exact hsTonelli.congr fun n =>
    selbergDiagonalTonelliSummand_eq_closedTail heta hx

theorem selbergDiagonalClosedTailSummand_nonneg
    {eta x theta y : ℝ} {n : ℕ} (heta : 0 < eta) (hx : 0 < x) :
    0 ≤ selbergDiagonalClosedTailSummand eta x theta n y := by
  by_cases hy : y ∈ Set.Ici (selbergDiagonalScale eta n * x)
  · have hb : 0 < selbergDiagonalScale eta n * x := by
      unfold selbergDiagonalScale
      positivity
    have hy0 : 0 < y := hb.trans_le hy
    unfold selbergDiagonalClosedTailSummand selbergWeightedGaussian
    rw [Set.indicator_of_mem hy]
    positivity
  · unfold selbergDiagonalClosedTailSummand
    rw [Set.indicator_of_notMem hy, mul_zero]

theorem integrable_selbergDiagonalClosedTailSummand
    {eta x theta : ℝ} {n : ℕ} (heta : 0 < eta) (hx : 0 < x)
    (htheta1 : theta < 1) :
    Integrable (selbergDiagonalClosedTailSummand eta x theta n) := by
  let b : ℝ := selbergDiagonalScale eta n * x
  have hb : 0 < b := by
    dsimp [b, selbergDiagonalScale]
    positivity
  have hfull : IntegrableOn (selbergWeightedGaussian theta) (Set.Ioi 0) := by
    unfold selbergWeightedGaussian
    simpa only [neg_mul, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_sq
        (s := -theta) (by norm_num : (0 : ℝ) < 1) (by linarith))
  have htail : IntegrableOn (selbergWeightedGaussian theta) (Set.Ici b) :=
    hfull.mono_set fun y hy => hb.trans_le hy
  have hscaled := htail.const_mul
    (eta ^ ((theta - 1) / 2) *
      (((n + 1 : ℕ) : ℝ) ^ (theta - 1)))
  have hind := IntegrableOn.integrable_indicator hscaled measurableSet_Ici
  apply hind.congr
  filter_upwards [] with y
  by_cases hy : y ∈ Set.Ici b
  · simp only [Set.indicator_of_mem hy, selbergDiagonalClosedTailSummand, b]
  · simp only [Set.indicator_of_notMem hy, selbergDiagonalClosedTailSummand,
      b, mul_zero]

theorem tsum_selbergDiagonalClosedTailSummand_eq_floorKernelIntegrand
    {eta x theta y : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (hy : 0 ≤ y) :
    ∑' n : ℕ, selbergDiagonalClosedTailSummand eta x theta n y =
      selbergDiagonalFloorKernelIntegrand eta x theta y := by
  calc
    ∑' n : ℕ, selbergDiagonalClosedTailSummand eta x theta n y =
        ∑' n : ℕ, selbergDiagonalTonelliSummand eta x theta y n := by
      apply tsum_congr
      intro n
      exact (selbergDiagonalTonelliSummand_eq_closedTail heta hx).symm
    _ = selbergDiagonalFloorKernelIntegrand eta x theta y :=
      tsum_selbergDiagonalTonelliSummand_eq_floorKernelIntegrand
        heta hx hy

theorem hasSum_integral_selbergDiagonalClosedTailSummand
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    HasSum
      (fun n : ℕ => ∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalClosedTailSummand eta x theta n y)
      (selbergDiagonalFloorKernel eta x theta) := by
  let s : Set ℝ := Set.Ioi (x * Real.sqrt eta)
  have ha : 0 < x * Real.sqrt eta := mul_pos hx (Real.sqrt_pos.2 heta)
  have htheta1 : theta < 1 := hthetaHalf.trans_lt (by norm_num)
  have htermInt (n : ℕ) :
      Integrable (selbergDiagonalClosedTailSummand eta x theta n) :=
    integrable_selbergDiagonalClosedTailSummand heta hx htheta1
  have hsumInt : IntegrableOn
      (fun y : ℝ => ∑' n : ℕ,
        selbergDiagonalClosedTailSummand eta x theta n y) s := by
    refine IntegrableOn.congr_fun
      (integrableOn_selbergDiagonalFloorKernelIntegrand_Ioi
        heta hx htheta0 hthetaHalf) ?_ measurableSet_Ioi
    intro y hy
    exact (tsum_selbergDiagonalClosedTailSummand_eq_floorKernelIntegrand
      heta hx (ha.trans hy).le).symm
  have hresult := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict s)
    (F := fun n : ℕ => selbergDiagonalClosedTailSummand eta x theta n)
    (f := selbergDiagonalFloorKernelIntegrand eta x theta)
    (bound := fun n : ℕ => selbergDiagonalClosedTailSummand eta x theta n)
    (fun n => (htermInt n).aestronglyMeasurable.restrict)
    (fun n => by
      filter_upwards with y
      have hnonneg := selbergDiagonalClosedTailSummand_nonneg
        (theta := theta) (n := n) (y := y) heta hx
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg])
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact summable_selbergDiagonalClosedTailSummand
        heta hx (ha.trans hy).le)
    hsumInt
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hs := summable_selbergDiagonalClosedTailSummand
        (theta := theta) heta hx (ha.trans hy).le
      have heq := tsum_selbergDiagonalClosedTailSummand_eq_floorKernelIntegrand
        (theta := theta) heta hx (ha.trans hy).le
      exact heq ▸ hs.hasSum)
  simpa only [s, selbergDiagonalFloorKernel] using hresult

theorem integral_selbergDiagonalClosedTailSummand_Ioi
    {eta x theta : ℝ} {n : ℕ} (heta : 0 < eta) (hx : 0 < x) :
    (∫ y in Set.Ioi (x * Real.sqrt eta),
        selbergDiagonalClosedTailSummand eta x theta n y) =
      eta ^ ((theta - 1) / 2) *
        (((n + 1 : ℕ) : ℝ) ^ (theta - 1)) *
          (∫ y in Set.Ioi (selbergDiagonalScale eta n * x),
            selbergWeightedGaussian theta y) := by
  let a : ℝ := x * Real.sqrt eta
  let b : ℝ := selbergDiagonalScale eta n * x
  have ha : 0 < a := by dsimp [a]; positivity
  have hr : 1 ≤ (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hab : a ≤ b := by
    dsimp [a, b]
    rw [selbergDiagonalScale_mul_x]
    nlinarith
  have hInter : Set.Ici a ∩ Set.Ici b = Set.Ici b := by
    apply Set.inter_eq_right.mpr
    intro y hy
    exact hab.trans hy
  change (∫ y in Set.Ioi a,
      selbergDiagonalClosedTailSummand eta x theta n y) =
    eta ^ ((theta - 1) / 2) *
      (((n + 1 : ℕ) : ℝ) ^ (theta - 1)) *
        (∫ y in Set.Ioi b, selbergWeightedGaussian theta y)
  calc
    (∫ y in Set.Ioi a,
        selbergDiagonalClosedTailSummand eta x theta n y) =
      ∫ y in Set.Ici a,
        selbergDiagonalClosedTailSummand eta x theta n y :=
      MeasureTheory.setIntegral_congr_set Ioi_ae_eq_Ici
    _ = eta ^ ((theta - 1) / 2) *
        (((n + 1 : ℕ) : ℝ) ^ (theta - 1)) *
          (∫ y in Set.Ioi b, selbergWeightedGaussian theta y) := by
      unfold selbergDiagonalClosedTailSummand
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
      rw [hInter]
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]

theorem hasSum_integral_selbergDiagonalOriginalIntegrand
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    HasSum
      (fun n : ℕ => ∫ u in Set.Ioi x,
        selbergDiagonalOriginalIntegrand eta theta n u)
      (selbergDiagonalFloorKernel eta x theta) := by
  apply (hasSum_integral_selbergDiagonalClosedTailSummand
    heta hx htheta0 hthetaHalf).congr_fun
  intro n
  rw [integral_selbergDiagonalOriginalIntegrand_Ioi heta hx]
  exact (integral_selbergDiagonalClosedTailSummand_Ioi heta hx).symm

theorem tsum_integral_selbergDiagonalOriginalIntegrand_eq_floorKernel
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    ∑' n : ℕ, (∫ u in Set.Ioi x,
        selbergDiagonalOriginalIntegrand eta theta n u) =
      selbergDiagonalFloorKernel eta x theta :=
  (hasSum_integral_selbergDiagonalOriginalIntegrand
    heta hx htheta0 hthetaHalf).tsum_eq

end HardyTheorem
