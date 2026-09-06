import HardyTheorem.SelbergOffDiagonalFixedSide
import HardyTheorem.SelbergOffDiagonalOuterSum
import HardyTheorem.SelbergOffDiagonalParameter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open scoped BigOperators

namespace HardyTheorem

/-! # Joining the two ordered sides of Selberg's off-diagonal sum. -/

theorem one_half_le_cos_of_mem_unitInterval
    {delta : ℝ} (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (1 : ℝ) / 2 ≤ Real.cos delta := by
  have hquad : delta ^ 2 ≤ 1 := by nlinarith
  exact (by nlinarith : (1 : ℝ) / 2 ≤ 1 - delta ^ 2 / 2) |>.trans
    Real.one_sub_sq_div_two_le_cos

theorem inv_pi_mul_cos_le_one_of_mem_unitInterval
    {delta : ℝ} (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (Real.pi * Real.cos delta)⁻¹ ≤ 1 := by
  have hcos := one_half_le_cos_of_mem_unitInterval hdelta0 hdelta1
  have hprod : 1 ≤ Real.pi * Real.cos delta := by
    nlinarith [Real.two_le_pi]
  exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hprod)).2 hprod

noncomputable def selbergOffDiagonalOneSideUniformMajorant
    (kappa lambda mu : ℕ) (L W : ℝ) : ℝ :=
  (((kappa : ℝ)⁻¹ * L) * (lambda : ℝ) +
    ((kappa : ℝ)⁻¹ * W) * (mu : ℝ)⁻¹)

theorem tsum_fixedSide_le_two_oneSideUniformMajorant
    {a L W : ℝ} {kappa lambda mu nu Xnat : ℕ}
    (ha0 : 0 < a) (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu) (hkappaX : kappa ≤ Xnat)
    (hnuX : nu ≤ Xnat) (hXnat : 1 ≤ Xnat)
    (hlocal : (∑' n : ℕ, selbergOffDiagonalDampedBracket
      a (Xnat : ℝ) (((lambda * mu : ℕ) : ℝ)) n) ≤
        L + (((lambda * mu : ℕ) : ℝ))⁻¹ * W) :
    (∑' n : ℕ, selbergFixedSideSquareSum
      a (n + 1) kappa lambda mu nu) ≤
        2 * selbergOffDiagonalOneSideUniformMajorant
          kappa lambda mu L W := by
  have hcoeff : 0 ≤ 2 * ((lambda : ℝ) / (kappa : ℝ)) := by positivity
  calc
    (∑' n : ℕ, selbergFixedSideSquareSum
        a (n + 1) kappa lambda mu nu) ≤
        2 * ((lambda : ℝ) / (kappa : ℝ)) *
          (∑' n : ℕ, selbergOffDiagonalDampedBracket
            a (Xnat : ℝ) (((lambda * mu : ℕ) : ℝ)) n) :=
      tsum_selbergFixedSideSquareSum_add_one_le
        ha0 hkappa hlambda hmu hnu hkappaX hnuX hXnat
    _ ≤ 2 * ((lambda : ℝ) / (kappa : ℝ)) *
        (L + (((lambda * mu : ℕ) : ℝ))⁻¹ * W) := by
      exact mul_le_mul_of_nonneg_left (by simpa only using hlocal) hcoeff
    _ = 2 * selbergOffDiagonalOneSideUniformMajorant
        kappa lambda mu L W := by
      unfold selbergOffDiagonalOneSideUniformMajorant
      push_cast
      field_simp [show (kappa : ℝ) ≠ 0 by positivity,
        show (lambda : ℝ) ≠ 0 by positivity,
        show (mu : ℝ) ≠ 0 by positivity]

noncomputable def selbergOffDiagonalUniformL (delta : ℝ) (X : ℕ) : ℝ :=
  Real.log (2 * (X : ℝ) ^ 2 / delta)

noncomputable def selbergOffDiagonalUniformW (delta : ℝ) (X : ℕ) : ℝ :=
  (Real.log (X : ℝ) + Real.log ((X : ℝ) ^ 2 / delta)) *
    selbergOffDiagonalUniformL delta X + 2

theorem tsum_fixedSide_le_two_oneSideUniform
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda mu nu : ℕ} (hX : 1 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    (∑' n : ℕ, selbergFixedSideSquareSum
      (selbergOffDiagonalGaussianParameter delta kappa lambda)
        (n + 1) kappa lambda mu nu) ≤
      2 * selbergOffDiagonalOneSideUniformMajorant kappa lambda mu
        (selbergOffDiagonalUniformL delta X)
        (selbergOffDiagonalUniformW delta X) := by
  have hbase0 : 0 < delta / (X : ℝ) ^ 2 := by positivity
  have ha0 : 0 < selbergOffDiagonalGaussianParameter delta kappa lambda :=
    hbase0.trans_le (delta_div_sq_le_selbergOffDiagonalGaussianParameter
      hdelta0 hdelta1 hX hkappa hlambda hlambdaX)
  apply tsum_fixedSide_le_two_oneSideUniformMajorant
    ha0 hkappa hlambda hmu hnu hkappaX hnuX hX
  simpa only [selbergOffDiagonalUniformL, selbergOffDiagonalUniformW] using
    (tsum_offDiagonalDampedBracket_le_uniform
      hdelta0 hdelta1 hX hkappa hlambda hlambdaX
      (show 0 < (((lambda * mu : ℕ) : ℝ)) by positivity))

noncomputable def selbergOffDiagonalReverseOuterMajorant
    (X : ℕ) (L W : ℝ) : ℝ :=
  ∑ kappa ∈ Finset.Icc 1 X,
    ∑ lambda ∈ Finset.Icc 1 X,
      ∑ mu ∈ Finset.Icc 1 X,
        ∑ nu ∈ Finset.Icc 1 X,
          selbergOffDiagonalOneSideUniformMajorant mu nu kappa L W

private theorem sum_four_separable_twoSides
    (s : Finset ℕ) (f g h j : ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      f a * g b * h c * j d) =
      (∑ a ∈ s, f a) * (∑ b ∈ s, g b) *
        (∑ c ∈ s, h c) * (∑ d ∈ s, j d) := by
  have htwo (u v : ℕ → ℝ) :
      (∑ a ∈ s, ∑ b ∈ s, u a * v b) =
        (∑ a ∈ s, u a) * (∑ b ∈ s, v b) := by
    calc
      (∑ a ∈ s, ∑ b ∈ s, u a * v b) =
          ∑ a ∈ s, u a * (∑ b ∈ s, v b) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  calc
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        f a * g b * h c * j d) =
        ∑ a ∈ s, ∑ b ∈ s,
          (f a * g b) *
            ((∑ c ∈ s, h c) * (∑ d ∈ s, j d)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      calc
        (∑ c ∈ s, ∑ d ∈ s, f a * g b * h c * j d) =
            (f a * g b) * (∑ c ∈ s, ∑ d ∈ s, h c * j d) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _hc
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _hd
          ring
        _ = _ := by rw [htwo]
    _ = ∑ a ∈ s, ∑ b ∈ s, (f a * g b) *
        ((∑ c ∈ s, h c) * (∑ d ∈ s, j d)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = (∑ a ∈ s, ∑ b ∈ s, f a * g b) *
        ((∑ c ∈ s, h c) * (∑ d ∈ s, j d)) := by
      let C : ℝ := (∑ c ∈ s, h c) * (∑ d ∈ s, j d)
      change (∑ a ∈ s, ∑ b ∈ s, (f a * g b) * C) =
        (∑ a ∈ s, ∑ b ∈ s, f a * g b) * C
      calc
        (∑ a ∈ s, ∑ b ∈ s, (f a * g b) * C) =
            ∑ a ∈ s, (∑ b ∈ s, f a * g b) * C := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.sum_mul]
        _ = _ := by rw [Finset.sum_mul]
    _ = _ := by
      rw [htwo]
      ring

theorem selbergOffDiagonalReverseOuterMajorant_eq
    (X : ℕ) (L W : ℝ) :
    selbergOffDiagonalReverseOuterMajorant X L W =
      selbergOffDiagonalOuterMajorant X L W := by
  let s : Finset ℕ := Finset.Icc 1 X
  unfold selbergOffDiagonalReverseOuterMajorant
  unfold selbergOffDiagonalOuterMajorant
  unfold selbergOffDiagonalOneSideUniformMajorant
  change (∑ kappa ∈ s, ∑ lambda ∈ s, ∑ mu ∈ s, ∑ nu ∈ s,
      (((mu : ℝ)⁻¹ * L) * (nu : ℝ) +
        ((mu : ℝ)⁻¹ * W) * (kappa : ℝ)⁻¹)) =
    ∑ kappa ∈ s, ∑ lambda ∈ s, ∑ mu ∈ s, ∑ _nu ∈ s,
      (((kappa : ℝ)⁻¹ * L) * (lambda : ℝ) * 1 * 1 +
        ((kappa : ℝ)⁻¹ * W) * 1 * (mu : ℝ)⁻¹ * 1)
  calc
    (∑ kappa ∈ s, ∑ lambda ∈ s, ∑ mu ∈ s, ∑ nu ∈ s,
        (((mu : ℝ)⁻¹ * L) * (nu : ℝ) +
          ((mu : ℝ)⁻¹ * W) * (kappa : ℝ)⁻¹)) =
        (∑ kappa ∈ s, ∑ lambda ∈ s, ∑ mu ∈ s, ∑ nu ∈ s,
          L * 1 * (mu : ℝ)⁻¹ * (nu : ℝ)) +
        (∑ kappa ∈ s, ∑ lambda ∈ s, ∑ mu ∈ s, ∑ nu ∈ s,
          (kappa : ℝ)⁻¹ * 1 * (mu : ℝ)⁻¹ * W) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro kappa _ <;>
        apply Finset.sum_congr rfl <;> intro lambda _ <;>
        apply Finset.sum_congr rfl <;> intro mu _ <;>
        apply Finset.sum_congr rfl <;> intro nu _ <;> ring
    _ = ((∑ kappa ∈ s, L) * (∑ lambda ∈ s, 1) *
          (∑ mu ∈ s, (mu : ℝ)⁻¹) * (∑ nu ∈ s, (nu : ℝ))) +
        ((∑ kappa ∈ s, (kappa : ℝ)⁻¹) * (∑ lambda ∈ s, 1) *
          (∑ mu ∈ s, (mu : ℝ)⁻¹) * (∑ nu ∈ s, W)) := by
      rw [sum_four_separable_twoSides, sum_four_separable_twoSides]
    _ = ((∑ kappa ∈ s, (kappa : ℝ)⁻¹) *
          (∑ lambda ∈ s, (lambda : ℝ)) * (∑ mu ∈ s, L) *
          (∑ nu ∈ s, 1)) +
        ((∑ kappa ∈ s, (kappa : ℝ)⁻¹) * (∑ lambda ∈ s, 1) *
          (∑ mu ∈ s, (mu : ℝ)⁻¹) * (∑ nu ∈ s, W)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ∑ kappa ∈ s, ∑ lambda ∈ s, ∑ mu ∈ s, ∑ nu ∈ s,
        (((kappa : ℝ)⁻¹ * L) * (lambda : ℝ) * 1 * 1 +
          ((kappa : ℝ)⁻¹ * W) * 1 * (mu : ℝ)⁻¹ * 1) := by
      rw [← sum_four_separable_twoSides, ← sum_four_separable_twoSides]
      simp_rw [Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro kappa _ <;>
        apply Finset.sum_congr rfl <;> intro lambda _ <;>
        apply Finset.sum_congr rfl <;> intro mu _ <;>
        apply Finset.sum_congr rfl <;> intro nu _ <;> ring

noncomputable def selbergOffDiagonalTwoSideOuterMajorant
    (X : ℕ) (L W : ℝ) : ℝ :=
  2 * selbergOffDiagonalOuterMajorant X L W +
    2 * selbergOffDiagonalReverseOuterMajorant X L W

noncomputable def selbergOffDiagonalPositiveSquareSum
    (delta : ℝ) (X : ℕ) : ℝ :=
  ∑ kappa ∈ Finset.Icc 1 X,
    ∑ lambda ∈ Finset.Icc 1 X,
      ∑ mu ∈ Finset.Icc 1 X,
        ∑ nu ∈ Finset.Icc 1 X,
          ∑' n : ℕ, selbergFixedSideSquareSum
            (selbergOffDiagonalGaussianParameter delta kappa lambda)
              (n + 1) kappa lambda mu nu

noncomputable def selbergOffDiagonalReverseSquareSum
    (delta : ℝ) (X : ℕ) : ℝ :=
  ∑ kappa ∈ Finset.Icc 1 X,
    ∑ lambda ∈ Finset.Icc 1 X,
      ∑ mu ∈ Finset.Icc 1 X,
        ∑ nu ∈ Finset.Icc 1 X,
          ∑' n : ℕ, selbergFixedSideSquareSum
            (selbergOffDiagonalGaussianParameter delta mu nu)
              (n + 1) mu nu kappa lambda

noncomputable def selbergOffDiagonalTwoSideSquareSum
    (delta : ℝ) (X : ℕ) : ℝ :=
  selbergOffDiagonalPositiveSquareSum delta X +
    selbergOffDiagonalReverseSquareSum delta X

theorem selbergOffDiagonalPositiveSquareSum_le
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 1 ≤ X) :
    selbergOffDiagonalPositiveSquareSum delta X ≤
      2 * selbergOffDiagonalOuterMajorant X
        (selbergOffDiagonalUniformL delta X)
        (selbergOffDiagonalUniformW delta X) := by
  unfold selbergOffDiagonalPositiveSquareSum selbergOffDiagonalOuterMajorant
  simp only [mul_one]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro kappa hkappaMem
  apply Finset.sum_le_sum
  intro lambda hlambdaMem
  apply Finset.sum_le_sum
  intro mu hmuMem
  apply Finset.sum_le_sum
  intro nu hnuMem
  simpa [selbergOffDiagonalOneSideUniformMajorant, mul_assoc,
    mul_comm, mul_left_comm] using
    (tsum_fixedSide_le_two_oneSideUniform hdelta0 hdelta1 hX
      (Finset.mem_Icc.mp hkappaMem).1 (Finset.mem_Icc.mp hkappaMem).2
      (Finset.mem_Icc.mp hlambdaMem).1 (Finset.mem_Icc.mp hlambdaMem).2
      (Finset.mem_Icc.mp hmuMem).1 (Finset.mem_Icc.mp hnuMem).1
      (Finset.mem_Icc.mp hnuMem).2)

theorem selbergOffDiagonalReverseSquareSum_le
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 1 ≤ X) :
    selbergOffDiagonalReverseSquareSum delta X ≤
      2 * selbergOffDiagonalReverseOuterMajorant X
        (selbergOffDiagonalUniformL delta X)
        (selbergOffDiagonalUniformW delta X) := by
  unfold selbergOffDiagonalReverseSquareSum
  unfold selbergOffDiagonalReverseOuterMajorant
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro kappa hkappaMem
  apply Finset.sum_le_sum
  intro lambda hlambdaMem
  apply Finset.sum_le_sum
  intro mu hmuMem
  apply Finset.sum_le_sum
  intro nu hnuMem
  exact tsum_fixedSide_le_two_oneSideUniform hdelta0 hdelta1 hX
    (Finset.mem_Icc.mp hmuMem).1 (Finset.mem_Icc.mp hmuMem).2
    (Finset.mem_Icc.mp hnuMem).1 (Finset.mem_Icc.mp hnuMem).2
    (Finset.mem_Icc.mp hkappaMem).1 (Finset.mem_Icc.mp hlambdaMem).1
    (Finset.mem_Icc.mp hlambdaMem).2

theorem selbergOffDiagonalTwoSideSquareSum_le
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 1 ≤ X) :
    selbergOffDiagonalTwoSideSquareSum delta X ≤
      selbergOffDiagonalTwoSideOuterMajorant X
        (selbergOffDiagonalUniformL delta X)
        (selbergOffDiagonalUniformW delta X) := by
  exact add_le_add
    (selbergOffDiagonalPositiveSquareSum_le hdelta0 hdelta1 hX)
    (selbergOffDiagonalReverseSquareSum_le hdelta0 hdelta1 hX)

theorem selbergOffDiagonalUniformL_nonneg
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 1 ≤ X) :
    0 ≤ selbergOffDiagonalUniformL delta X := by
  unfold selbergOffDiagonalUniformL
  apply Real.log_nonneg
  rw [one_le_div hdelta0]
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  nlinarith [sq_nonneg ((X : ℝ) - 1)]

theorem selbergOffDiagonalUniformW_nonneg
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 1 ≤ X) :
    0 ≤ selbergOffDiagonalUniformW delta X := by
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hratio : 1 ≤ (X : ℝ) ^ 2 / delta := by
    rw [one_le_div hdelta0]
    nlinarith [sq_nonneg ((X : ℝ) - 1)]
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXr
  have hlogratio : 0 ≤ Real.log ((X : ℝ) ^ 2 / delta) :=
    Real.log_nonneg hratio
  have hL := selbergOffDiagonalUniformL_nonneg hdelta0 hdelta1 hX
  unfold selbergOffDiagonalUniformW
  exact add_nonneg (mul_nonneg (add_nonneg hlogX hlogratio) hL) (by norm_num)

theorem selbergOffDiagonalTwoSideOuterMajorant_eq
    (X : ℕ) (L W : ℝ) :
    selbergOffDiagonalTwoSideOuterMajorant X L W =
      4 * selbergOffDiagonalOuterMajorant X L W := by
  rw [selbergOffDiagonalTwoSideOuterMajorant,
    selbergOffDiagonalReverseOuterMajorant_eq]
  ring

theorem selbergOffDiagonalTwoSideOuterMajorant_le
    {X : ℕ} (hX : 1 ≤ X) {L W : ℝ} (hL : 0 ≤ L) (hW : 0 ≤ W) :
    selbergOffDiagonalTwoSideOuterMajorant X L W ≤
      4 * ((X : ℝ) ^ 4 * (1 + Real.log (X : ℝ)) * L +
        (X : ℝ) ^ 2 * (1 + Real.log (X : ℝ)) ^ 2 * W) := by
  rw [selbergOffDiagonalTwoSideOuterMajorant_eq]
  gcongr
  exact selbergOffDiagonalOuterMajorant_le hX hL hW

theorem selbergOffDiagonalTwoSideSquareSum_le_explicit
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hX : 1 ≤ X) :
    selbergOffDiagonalTwoSideSquareSum delta X ≤
      4 * ((X : ℝ) ^ 4 * (1 + Real.log (X : ℝ)) *
          selbergOffDiagonalUniformL delta X +
        (X : ℝ) ^ 2 * (1 + Real.log (X : ℝ)) ^ 2 *
          selbergOffDiagonalUniformW delta X) := by
  exact (selbergOffDiagonalTwoSideSquareSum_le hdelta0 hdelta1 hX).trans
    (selbergOffDiagonalTwoSideOuterMajorant_le hX
      (selbergOffDiagonalUniformL_nonneg hdelta0 hdelta1 hX)
      (selbergOffDiagonalUniformW_nonneg hdelta0 hdelta1 hX))

theorem selberg_oscillatory_prefactor_le_two
    {delta x theta : ℝ} (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta) :
    2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta) ≤
      2 * x ^ (-theta) := by
  have hden : 1 ≤ Real.pi * Real.cos delta := by
    have hcos := one_half_le_cos_of_mem_unitInterval hdelta0 hdelta1
    nlinarith [Real.two_le_pi]
  have hpow : x ^ (-theta - 1) ≤ x ^ (-theta) := by
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc
    2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta) ≤
        2 * x ^ (-theta - 1) := by
      rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)]
      nlinarith [Real.rpow_nonneg (zero_le_one.trans hx) (-theta - 1)]
    _ ≤ 2 * x ^ (-theta) := by gcongr

noncomputable def selbergOffDiagonalOscillatoryMajorant
    (delta x theta : ℝ) (X : ℕ) : ℝ :=
  (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
    selbergOffDiagonalTwoSideSquareSum delta X

theorem selbergOffDiagonalTwoSideSquareSum_nonneg
    {delta : ℝ} {X : ℕ} :
    0 ≤ selbergOffDiagonalTwoSideSquareSum delta X := by
  unfold selbergOffDiagonalTwoSideSquareSum
  apply add_nonneg
  · unfold selbergOffDiagonalPositiveSquareSum
    apply Finset.sum_nonneg
    intro kappa hkappa
    apply Finset.sum_nonneg
    intro lambda hlambda
    apply Finset.sum_nonneg
    intro mu hmu
    apply Finset.sum_nonneg
    intro nu hnu
    apply tsum_nonneg
    intro n
    exact selbergFixedSideSquareSum_nonneg
      (Nat.le_add_left 1 n)
      (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hlambda).1
      (Finset.mem_Icc.mp hmu).1 (Finset.mem_Icc.mp hnu).1
  · unfold selbergOffDiagonalReverseSquareSum
    apply Finset.sum_nonneg
    intro kappa hkappa
    apply Finset.sum_nonneg
    intro lambda hlambda
    apply Finset.sum_nonneg
    intro mu hmu
    apply Finset.sum_nonneg
    intro nu hnu
    apply tsum_nonneg
    intro n
    exact selbergFixedSideSquareSum_nonneg
      (Nat.le_add_left 1 n)
      (Finset.mem_Icc.mp hmu).1 (Finset.mem_Icc.mp hnu).1
      (Finset.mem_Icc.mp hkappa).1 (Finset.mem_Icc.mp hlambda).1

theorem selbergOffDiagonalOscillatoryMajorant_le_explicit
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {x theta : ℝ} (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    {X : ℕ} (hX : 1 ≤ X) :
    selbergOffDiagonalOscillatoryMajorant delta x theta X ≤
      8 * x ^ (-theta) *
        ((X : ℝ) ^ 4 * (1 + Real.log (X : ℝ)) *
            selbergOffDiagonalUniformL delta X +
          (X : ℝ) ^ 2 * (1 + Real.log (X : ℝ)) ^ 2 *
            selbergOffDiagonalUniformW delta X) := by
  let R := (X : ℝ) ^ 4 * (1 + Real.log (X : ℝ)) *
      selbergOffDiagonalUniformL delta X +
    (X : ℝ) ^ 2 * (1 + Real.log (X : ℝ)) ^ 2 *
      selbergOffDiagonalUniformW delta X
  have hsum := selbergOffDiagonalTwoSideSquareSum_le_explicit
    hdelta0 hdelta1 hX
  have hsum0 := selbergOffDiagonalTwoSideSquareSum_nonneg
    (delta := delta) (X := X)
  have hpref := selberg_oscillatory_prefactor_le_two
    hdelta0.le hdelta1 hx htheta
  have hpref0 : 0 ≤ 2 * x ^ (-theta - 1) /
      (Real.pi * Real.cos delta) := by
    have hcos : 0 < Real.cos delta :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (one_half_le_cos_of_mem_unitInterval hdelta0.le hdelta1)
    positivity
  unfold selbergOffDiagonalOscillatoryMajorant
  calc
    (2 * x ^ (-theta - 1) / (Real.pi * Real.cos delta)) *
        selbergOffDiagonalTwoSideSquareSum delta X ≤
        (2 * x ^ (-theta)) * (4 * R) :=
      mul_le_mul hpref (by simpa only [R] using hsum) hsum0 (by positivity)
    _ = 8 * x ^ (-theta) * R := by ring

end HardyTheorem
