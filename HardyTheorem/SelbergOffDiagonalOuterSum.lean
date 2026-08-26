import HardyTheorem.SelbergGaussianHarmonicSum
import HardyTheorem.SelbergSArithmeticHarmonic

open scoped BigOperators

namespace HardyTheorem

/-! # The outer four-variable sum in Selberg's off-diagonal estimate. -/

noncomputable def selbergOffDiagonalOuterMajorant
    (X : ℕ) (L W : ℝ) : ℝ :=
  ∑ kappa ∈ Finset.Icc 1 X,
    ∑ lambda ∈ Finset.Icc 1 X,
      ∑ mu ∈ Finset.Icc 1 X,
        ∑ _nu ∈ Finset.Icc 1 X,
          (((kappa : ℝ)⁻¹ * L) * (lambda : ℝ) * 1 * 1 +
            ((kappa : ℝ)⁻¹ * W) * 1 * (mu : ℝ)⁻¹ * 1)

private theorem sum_four_separable
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

theorem selbergOffDiagonalOuterMajorant_le
    {X : ℕ} (hX : 1 ≤ X) {L W : ℝ} (hL : 0 ≤ L) (hW : 0 ≤ W) :
    selbergOffDiagonalOuterMajorant X L W ≤
      (X : ℝ) ^ 4 * (1 + Real.log (X : ℝ)) * L +
        (X : ℝ) ^ 2 * (1 + Real.log (X : ℝ)) ^ 2 * W := by
  let s : Finset ℕ := Finset.Icc 1 X
  let H : ℝ := ∑ n ∈ s, (n : ℝ)⁻¹
  let Q : ℝ := ∑ n ∈ s, (n : ℝ)
  let C : ℝ := (s.card : ℝ)
  have hsplit : selbergOffDiagonalOuterMajorant X L W =
      (H * L) * Q * C * C + (H * W) * C * H * C := by
    have hsumL : (∑ n ∈ s, (n : ℝ)⁻¹ * L) = H * L := by
      rw [Finset.sum_mul]
    have hsumW : (∑ n ∈ s, (n : ℝ)⁻¹ * W) = H * W := by
      rw [Finset.sum_mul]
    unfold selbergOffDiagonalOuterMajorant
    change (∑ kappa ∈ s, ∑ lambda ∈ s, ∑ mu ∈ s, ∑ _nu ∈ s,
      (((kappa : ℝ)⁻¹ * L) * (lambda : ℝ) * 1 * 1 +
        ((kappa : ℝ)⁻¹ * W) * 1 * (mu : ℝ)⁻¹ * 1)) = _
    simp_rw [Finset.sum_add_distrib]
    rw [sum_four_separable, sum_four_separable]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsumL, hsumW]
  have hH0 : 0 ≤ H := by
    dsimp [H]
    exact Finset.sum_nonneg fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)
  have hH : H ≤ 1 + Real.log (X : ℝ) := by
    dsimp [H, s]
    exact selberg_sum_Icc_inv_le_one_add_log X
  have hlog0 : 0 ≤ Real.log (X : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hX
  have hHB0 : 0 ≤ 1 + Real.log (X : ℝ) := by positivity
  have hC : C = (X : ℝ) := by
    dsimp [C, s]
    simp [Nat.card_Icc]
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact Finset.sum_nonneg fun n _ => Nat.cast_nonneg n
  have hQ : Q ≤ (X : ℝ) ^ 2 := by
    calc
      Q ≤ ∑ _n ∈ s, (X : ℝ) := by
        dsimp [Q]
        apply Finset.sum_le_sum
        intro n hn
        exact_mod_cast (Finset.mem_Icc.mp hn).2
      _ = C * (X : ℝ) := by
        simp [C]
      _ = (X : ℝ) ^ 2 := by rw [hC]; ring
  rw [hsplit, hC]
  apply add_le_add
  · calc
      (H * L) * Q * (X : ℝ) * (X : ℝ) ≤
          ((1 + Real.log (X : ℝ)) * L) * (X : ℝ) ^ 2 *
            (X : ℝ) * (X : ℝ) := by
        gcongr
      _ = (X : ℝ) ^ 4 * (1 + Real.log (X : ℝ)) * L := by ring
  · calc
      (H * W) * (X : ℝ) * H * (X : ℝ) ≤
          ((1 + Real.log (X : ℝ)) * W) * (X : ℝ) *
            (1 + Real.log (X : ℝ)) * (X : ℝ) := by
        gcongr
      _ = (X : ℝ) ^ 2 * (1 + Real.log (X : ℝ)) ^ 2 * W := by ring

end HardyTheorem
