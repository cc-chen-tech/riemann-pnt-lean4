import HardyTheorem.SelbergNonconstantFourierMass
import HardyTheorem.SelbergSArithmeticHarmonic

open Complex
open scoped BigOperators

namespace HardyTheorem

/-! # The elementary residue in Selberg's S1 kernel -/

private theorem abs_selbergResidueTaperedCoeff_le_one
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

theorem norm_selbergSqrtZetaPsi_zero_le
    {X : ℕ} (hX : 2 ≤ X) :
    ‖selbergSqrtZetaPsi X 0‖ ≤ (X : ℝ) := by
  unfold selbergSqrtZetaPsi selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ (0 : ℂ))‖ ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖(selbergSqrtZetaTaperedCoeff X n : ℂ) *
            (1 / (n : ℂ) ^ (0 : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa using abs_selbergResidueTaperedCoeff_le_one hX
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    _ = (X : ℝ) := by
      simp [Nat.card_Icc]

theorem norm_selbergSqrtZetaPsi_one_le
    {X : ℕ} (hX : 2 ≤ X) :
    ‖selbergSqrtZetaPsi X 1‖ ≤ 1 + Real.log (X : ℝ) := by
  unfold selbergSqrtZetaPsi selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ (1 : ℂ))‖ ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖(selbergSqrtZetaTaperedCoeff X n : ℂ) *
            (1 / (n : ℂ) ^ (1 : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      rw [Complex.cpow_one, norm_mul, norm_div, norm_one,
        Complex.norm_natCast]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have hcoeff := abs_selbergResidueTaperedCoeff_le_one hX
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
      have hnnonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
      simpa [one_div] using
        mul_le_mul_of_nonneg_right hcoeff hnnonneg
    _ ≤ 1 + Real.log (X : ℝ) := selberg_sum_Icc_inv_le_one_add_log X

theorem norm_selbergSqrtZetaPsi_one_mul_zero_le
    {X : ℕ} (hX : 2 ≤ X) :
    ‖selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0‖ ≤
      (X : ℝ) * (1 + Real.log (X : ℝ)) := by
  rw [norm_mul]
  calc
    ‖selbergSqrtZetaPsi X 1‖ * ‖selbergSqrtZetaPsi X 0‖ ≤
        (1 + Real.log (X : ℝ)) * (X : ℝ) :=
      mul_le_mul (norm_selbergSqrtZetaPsi_one_le hX)
        (norm_selbergSqrtZetaPsi_zero_le hX) (norm_nonneg _)
        (by positivity)
    _ = (X : ℝ) * (1 + Real.log (X : ℝ)) := mul_comm _ _

theorem normSq_selbergResidueInverseFourierKernel
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (y : ℝ) :
    Complex.normSq (selbergResidueInverseFourierKernel delta X y) =
      (1 / 4 : ℝ) * Real.exp (-y) *
        Complex.normSq
          (selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) := by
  have hz :
      ‖selbergFourierZ delta y ^ (1 / 2 : ℂ)‖ =
        Real.exp (-y / 2) := by
    convert norm_selbergFourierZ_cpow
      hdelta hdeltaPi y (1 / 2) 0 using 1 <;> norm_num
    ring
  have hexp : Real.exp (-y / 2) ^ 2 = Real.exp (-y) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold selbergResidueInverseFourierKernel
  simp only [Complex.normSq_eq_norm_sq, norm_mul, norm_div, norm_one,
    Complex.norm_natCast, Nat.cast_ofNat, Real.norm_eq_abs]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo, hz]
  calc
    (1 / 2 * Real.exp (-y / 2) * ‖selbergSqrtZetaPsi X 1‖ *
        ‖selbergSqrtZetaPsi X 0‖) ^ 2 =
      (1 / 4 : ℝ) * Real.exp (-y / 2) ^ 2 *
        (‖selbergSqrtZetaPsi X 1‖ * ‖selbergSqrtZetaPsi X 0‖) ^ 2 := by ring
    _ = _ := by rw [hexp]

end HardyTheorem
