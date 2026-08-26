import HardyTheorem.SelbergGaussianHarmonicSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace HardyTheorem

/-! # Uniformizing Selberg's varying off-diagonal Gaussian parameter. -/

noncomputable def selbergOffDiagonalGaussianParameter
    (delta : ℝ) (kappa lambda : ℕ) : ℝ :=
  Real.pi * Real.sin delta * (kappa : ℝ) ^ 2 / (lambda : ℝ) ^ 2

theorem delta_div_sq_le_selbergOffDiagonalGaussianParameter
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda : ℕ} (_hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hlambda0 : 1 ≤ lambda) (hlambdaX : lambda ≤ X) :
    delta / (X : ℝ) ^ 2 ≤
      selbergOffDiagonalGaussianParameter delta kappa lambda := by
  have hdeltaPi : delta ≤ Real.pi / 2 := by
    nlinarith [Real.two_le_pi]
  have hsin := Real.mul_le_sin hdelta0.le hdeltaPi
  have hpiSin : delta ≤ Real.pi * Real.sin delta := by
    have hmul := mul_le_mul_of_nonneg_left hsin Real.pi_pos.le
    have hid : Real.pi * (2 / Real.pi * delta) = 2 * delta := by
      field_simp [Real.pi_ne_zero]
    rw [hid] at hmul
    linarith
  have hsin0 : 0 ≤ Real.sin delta :=
    (Real.mul_le_sin hdelta0.le hdeltaPi).trans' (by positivity)
  have hkReal : (1 : ℝ) ≤ (kappa : ℝ) := by exact_mod_cast hkappa
  have hkSq : 1 ≤ (kappa : ℝ) ^ 2 := by nlinarith
  have hlReal0 : (0 : ℝ) < (lambda : ℝ) := by exact_mod_cast hlambda0
  have hlX : (lambda : ℝ) ^ 2 ≤ (X : ℝ) ^ 2 := by
    have : (lambda : ℝ) ≤ (X : ℝ) := by exact_mod_cast hlambdaX
    nlinarith
  unfold selbergOffDiagonalGaussianParameter
  calc
    delta / (X : ℝ) ^ 2 ≤ delta / (lambda : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hdelta0.le (sq_pos_of_pos hlReal0) hlX
    _ ≤ (Real.pi * Real.sin delta) / (lambda : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hpiSin (sq_nonneg _)
    _ ≤ (Real.pi * Real.sin delta * (kappa : ℝ) ^ 2) /
        (lambda : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact le_mul_of_one_le_right (mul_nonneg Real.pi_pos.le hsin0) hkSq

theorem delta_div_sq_le_capped_offDiagonalParameter
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda : ℕ} (hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hlambda0 : 1 ≤ lambda) (hlambdaX : lambda ≤ X) :
    delta / (X : ℝ) ^ 2 ≤ selbergCappedGaussianParameter
      (selbergOffDiagonalGaussianParameter delta kappa lambda) := by
  apply le_min
  · exact delta_div_sq_le_selbergOffDiagonalGaussianParameter
      hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX
  · have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hdiv : delta / (X : ℝ) ^ 2 ≤ delta := by
      rw [div_le_iff₀ (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hXr))]
      nlinarith [sq_nonneg ((X : ℝ) - 1)]
    exact hdiv.trans hdelta1

theorem log_two_div_capped_offDiagonalParameter_le
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda : ℕ} (hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hlambda0 : 1 ≤ lambda) (hlambdaX : lambda ≤ X) :
    Real.log (2 / selbergCappedGaussianParameter
      (selbergOffDiagonalGaussianParameter delta kappa lambda)) ≤
        Real.log (2 * (X : ℝ) ^ 2 / delta) := by
  let b := selbergCappedGaussianParameter
    (selbergOffDiagonalGaussianParameter delta kappa lambda)
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hbase0 : 0 < delta / (X : ℝ) ^ 2 := by positivity
  have hbase : delta / (X : ℝ) ^ 2 ≤ b := by
    dsimp [b]
    exact delta_div_sq_le_capped_offDiagonalParameter
      hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX
  have hb0 : 0 < b := hbase0.trans_le hbase
  have hinv : 1 / b ≤ (X : ℝ) ^ 2 / delta := by
    calc
      1 / b ≤ 1 / (delta / (X : ℝ) ^ 2) :=
        one_div_le_one_div_of_le hbase0 hbase
      _ = (X : ℝ) ^ 2 / delta := by
        field_simp [hdelta0.ne', hX0.ne']
  have hratio : 2 / b ≤ 2 * (X : ℝ) ^ 2 / delta := by
    calc
      2 / b = 2 * (1 / b) := by ring
      _ ≤ 2 * ((X : ℝ) ^ 2 / delta) := by gcongr
      _ = 2 * (X : ℝ) ^ 2 / delta := by ring
  simpa only [b] using Real.log_le_log (by positivity : 0 < 2 / b) hratio

theorem log_one_div_capped_offDiagonalParameter_le
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda : ℕ} (hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hlambda0 : 1 ≤ lambda) (hlambdaX : lambda ≤ X) :
    Real.log (1 / selbergCappedGaussianParameter
      (selbergOffDiagonalGaussianParameter delta kappa lambda)) ≤
        Real.log ((X : ℝ) ^ 2 / delta) := by
  let b := selbergCappedGaussianParameter
    (selbergOffDiagonalGaussianParameter delta kappa lambda)
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hbase0 : 0 < delta / (X : ℝ) ^ 2 := by positivity
  have hbase : delta / (X : ℝ) ^ 2 ≤ b := by
    dsimp [b]
    exact delta_div_sq_le_capped_offDiagonalParameter
      hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX
  have hb0 : 0 < b := hbase0.trans_le hbase
  have hinv : 1 / b ≤ (X : ℝ) ^ 2 / delta := by
    calc
      1 / b ≤ 1 / (delta / (X : ℝ) ^ 2) :=
        one_div_le_one_div_of_le hbase0 hbase
      _ = (X : ℝ) ^ 2 / delta := by
        field_simp [hdelta0.ne', hX0.ne']
  simpa only [b] using Real.log_le_log (by positivity : 0 < 1 / b) hinv

theorem tsum_offDiagonalGaussianHarmonic_le_uniform
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda : ℕ} (hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hlambda0 : 1 ≤ lambda) (hlambdaX : lambda ≤ X) :
    (∑' n : ℕ, selbergGaussianHarmonic
      (selbergOffDiagonalGaussianParameter delta kappa lambda) n) ≤
        Real.log (2 * (X : ℝ) ^ 2 / delta) := by
  have hbase0 : 0 < delta / (X : ℝ) ^ 2 := by positivity
  have ha0 : 0 < selbergOffDiagonalGaussianParameter delta kappa lambda :=
    hbase0.trans_le (delta_div_sq_le_selbergOffDiagonalGaussianParameter
      hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX)
  exact (tsum_selbergGaussianHarmonic_le_log_capped ha0).trans
    (log_two_div_capped_offDiagonalParameter_le
      hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX)

theorem tsum_offDiagonalGaussianLogHarmonic_le_uniform
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda : ℕ} (hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hlambda0 : 1 ≤ lambda) (hlambdaX : lambda ≤ X) :
    (∑' n : ℕ, selbergGaussianLogHarmonic
      (selbergOffDiagonalGaussianParameter delta kappa lambda) (X : ℝ) n) ≤
      (Real.log (X : ℝ) + Real.log ((X : ℝ) ^ 2 / delta)) *
        Real.log (2 * (X : ℝ) ^ 2 / delta) + 2 := by
  let a := selbergOffDiagonalGaussianParameter delta kappa lambda
  let b := selbergCappedGaussianParameter a
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hbase0 : 0 < delta / (X : ℝ) ^ 2 := by positivity
  have ha0 : 0 < a := hbase0.trans_le
    (delta_div_sq_le_selbergOffDiagonalGaussianParameter
      hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX)
  have hblog0 : 0 ≤ Real.log (2 / b) := by
    have hb1 : b ≤ 1 := min_le_right _ _
    have hb0 : 0 < b := by
      dsimp [b, selbergCappedGaussianParameter]
      exact lt_min ha0 zero_lt_one
    apply Real.log_nonneg
    exact (one_le_div hb0).2 (by linarith)
  calc
    (∑' n : ℕ, selbergGaussianLogHarmonic a (X : ℝ) n) ≤
        (Real.log (X : ℝ) + Real.log (1 / b)) * Real.log (2 / b) + 2 :=
      tsum_selbergGaussianLogHarmonic_le_capped ha0 hXr
    _ ≤ (Real.log (X : ℝ) + Real.log ((X : ℝ) ^ 2 / delta)) *
          Real.log (2 * (X : ℝ) ^ 2 / delta) + 2 := by
      have hfactor1 : Real.log (X : ℝ) + Real.log (1 / b) ≤
          Real.log (X : ℝ) + Real.log ((X : ℝ) ^ 2 / delta) := by
        have h := log_one_div_capped_offDiagonalParameter_le
          hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX
        dsimp [b, a]
        linarith
      have hfactor2 : Real.log (2 / b) ≤
          Real.log (2 * (X : ℝ) ^ 2 / delta) := by
        simpa only [b, a] using
          (log_two_div_capped_offDiagonalParameter_le
            hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX)
      have hlogX0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXr
      have hratioOne : 1 ≤ (X : ℝ) ^ 2 / delta := by
        rw [one_le_div hdelta0]
        nlinarith [sq_nonneg ((X : ℝ) - 1)]
      have hright0 : 0 ≤ Real.log (X : ℝ) +
          Real.log ((X : ℝ) ^ 2 / delta) :=
        add_nonneg hlogX0 (Real.log_nonneg hratioOne)
      simpa [add_comm] using add_le_add_right
        (mul_le_mul hfactor1 hfactor2 hblog0 hright0) 2
    _ = _ := rfl

theorem tsum_offDiagonalDampedBracket_le_uniform
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda : ℕ} (hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hlambda0 : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    {d : ℝ} (hd0 : 0 < d) :
    (∑' n : ℕ, selbergOffDiagonalDampedBracket
      (selbergOffDiagonalGaussianParameter delta kappa lambda)
        (X : ℝ) d n) ≤
      Real.log (2 * (X : ℝ) ^ 2 / delta) + d⁻¹ *
        ((Real.log (X : ℝ) + Real.log ((X : ℝ) ^ 2 / delta)) *
          Real.log (2 * (X : ℝ) ^ 2 / delta) + 2) := by
  let a := selbergOffDiagonalGaussianParameter delta kappa lambda
  have hbase0 : 0 < delta / (X : ℝ) ^ 2 := by positivity
  have ha0 : 0 < a := hbase0.trans_le
    (delta_div_sq_le_selbergOffDiagonalGaussianParameter
      hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX)
  unfold selbergOffDiagonalDampedBracket
  rw [(summable_selbergGaussianHarmonic ha0).tsum_add
      ((summable_selbergGaussianLogHarmonic_of_pos ha0
        (by exact_mod_cast hX)).mul_left d⁻¹),
    tsum_mul_left]
  exact add_le_add
    (tsum_offDiagonalGaussianHarmonic_le_uniform
      hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX)
    (mul_le_mul_of_nonneg_left
      (tsum_offDiagonalGaussianLogHarmonic_le_uniform
        hdelta0 hdelta1 hX hkappa hlambda0 hlambdaX)
      (inv_nonneg.mpr hd0.le))

end HardyTheorem
