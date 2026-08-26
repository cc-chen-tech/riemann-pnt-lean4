import HardyTheorem.SelbergRightLineAlgebra
import HardyTheorem.SelbergGaussianMellinAbsolute
import HardyTheorem.SelbergFourierMellinContour

open Complex
open scoped BigOperators

namespace HardyTheorem

/-! # Dirichlet expansion of Selberg's right Mellin line -/

/-- The fixed positive-zeta-index level after expanding both finite
mollifiers on `Re(s)=2`. -/
noncomputable def selbergRightLineLevel
    (delta : ℝ) (X : ℕ) (y : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  ∑ μ ∈ Finset.Icc 1 X, ∑ ν ∈ Finset.Icc 1 X,
    ((selbergSqrtZetaTaperedCoeff X μ : ℂ) *
      (selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
      selbergGaussianMellinLineTerm delta y μ ν (k + 1) t

private theorem selbergSqrtZetaPsi_eq_sum_neg_cpow
    (X : ℕ) (s : ℂ) :
    selbergSqrtZetaPsi X s =
      ∑ μ ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X μ : ℂ) * (μ : ℂ) ^ (-s) := by
  unfold selbergSqrtZetaPsi selbergMollifier
  apply Finset.sum_congr rfl
  intro μ _hμ
  rw [one_div, Complex.cpow_neg]

private theorem selbergSqrtZetaPsi_one_sub_eq_sum
    (X : ℕ) (s : ℂ) :
    selbergSqrtZetaPsi X (1 - s) =
      ∑ ν ∈ Finset.Icc 1 X,
        ((selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
          (ν : ℂ) ^ s := by
  unfold selbergSqrtZetaPsi selbergMollifier
  apply Finset.sum_congr rfl
  intro ν hν
  have hνpos : 0 < ν := (Finset.mem_Icc.mp hν).1
  have hν0 : (ν : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hνpos.ne'
  rw [one_div, ← Complex.cpow_neg]
  rw [show -(1 - s) = s - 1 by ring, Complex.cpow_sub s 1 hν0,
    Complex.cpow_one]
  ring

/-- One positive term of the zeta Dirichlet series expands exactly to one
arithmetic Gaussian level. -/
theorem selbergMellinWeight_mul_dirichletTerm_eq_rightLineLevel
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ)
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    selbergMellinWeight (selbergFourierZ delta y) X
        ((2 : ℂ) + I * t) *
        (1 / (n : ℂ) ^ ((2 : ℂ) + I * t)) =
      selbergRightLineLevel delta X y (n - 1) t := by
  let s : ℂ := (2 : ℂ) + I * t
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnsub : n - 1 + 1 = n := by omega
  rw [selbergMellinWeight]
  rw [selbergSqrtZetaPsi_eq_sum_neg_cpow,
    selbergSqrtZetaPsi_one_sub_eq_sum]
  unfold Gammaℝ
  rw [one_div, ← Complex.cpow_neg]
  change
    ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
      (∑ μ ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X μ : ℂ) * (μ : ℂ) ^ (-s)) *
      (∑ ν ∈ Finset.Icc 1 X,
        ((selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
          (ν : ℂ) ^ s) *
      selbergFourierZ delta y ^ s) * (n : ℂ) ^ (-s) = _
  unfold selbergRightLineLevel
  rw [hnsub]
  rw [show
    ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
      (∑ μ ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X μ : ℂ) * (μ : ℂ) ^ (-s)) *
      (∑ ν ∈ Finset.Icc 1 X,
        ((selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
          (ν : ℂ) ^ s) *
      selbergFourierZ delta y ^ s) * (n : ℂ) ^ (-s) =
      (∑ μ ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X μ : ℂ) * (μ : ℂ) ^ (-s)) *
      (∑ ν ∈ Finset.Icc 1 X,
        ((selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
          (ν : ℂ) ^ s) *
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
        selbergFourierZ delta y ^ s * (n : ℂ) ^ (-s)) by ring]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ν hν
  have hμpos : 0 < μ := (Finset.mem_Icc.mp hμ).1
  have hνpos : 0 < ν := (Finset.mem_Icc.mp hν).1
  rw [selbergGaussianMellinLineTerm]
  rw [show -(((2 : ℂ) + I * t) / 2) = -s / 2 by
    dsimp [s]
    ring]
  rw [selbergGaussianMellinPower_eq hdelta0 hdeltaPi y
    hμpos hνpos hn s]
  dsimp [s]
  ring

/-- On `Re(s)=2`, the raw contour integrand is pointwise the convergent
Dirichlet series of Gaussian arithmetic levels. -/
theorem selbergMellinRaw_rightLine_eq_tsum
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) (t : ℝ) :
    selbergMellinRawIntegrand (selbergFourierZ delta y) X
        ((2 : ℂ) + I * t) =
      ∑' k : ℕ, selbergRightLineLevel delta X y k t := by
  unfold selbergMellinRawIntegrand
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow
    (show 1 < (((2 : ℂ) + I * t).re) by norm_num)]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simpa using selbergMellinWeight_mul_dirichletTerm_eq_rightLineLevel
    hdelta0 hdeltaPi y X (Nat.succ_pos k) t

/-- The pointwise triangle majorant for one right-line level. -/
noncomputable def selbergRightLineMajorant
    (delta : ℝ) (X : ℕ) (y : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ μ ∈ Finset.Icc 1 X, ∑ ν ∈ Finset.Icc 1 X,
    ‖((selbergSqrtZetaTaperedCoeff X μ : ℂ) *
      (selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ))‖ *
      ‖selbergGaussianMellinLineTerm delta y μ ν (k + 1) t‖

/-- Every right-line level is integrable. -/
theorem integrable_selbergRightLineLevel
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X k : ℕ) :
    MeasureTheory.Integrable (selbergRightLineLevel delta X y k) := by
  unfold selbergRightLineLevel
  apply MeasureTheory.integrable_finsetSum
  intro μ hμ
  apply MeasureTheory.integrable_finsetSum
  intro ν hν
  exact (integrable_selbergGaussianMellinLineTerm hdelta0 hdeltaPi y
    (Finset.mem_Icc.mp hμ).1 (Finset.mem_Icc.mp hν).1
    (Nat.succ_pos k)).const_mul _

theorem integrable_selbergRightLineMajorant
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X k : ℕ) :
    MeasureTheory.Integrable (selbergRightLineMajorant delta X y k) := by
  unfold selbergRightLineMajorant
  apply MeasureTheory.integrable_finsetSum
  intro μ hμ
  apply MeasureTheory.integrable_finsetSum
  intro ν hν
  exact ((integrable_selbergGaussianMellinLineTerm hdelta0 hdeltaPi y
    (Finset.mem_Icc.mp hμ).1 (Finset.mem_Icc.mp hν).1
    (Nat.succ_pos k)).norm).const_mul _

theorem norm_selbergRightLineLevel_le_majorant
    (delta : ℝ) (X : ℕ) (y : ℝ) (k : ℕ) (t : ℝ) :
    ‖selbergRightLineLevel delta X y k t‖ ≤
      selbergRightLineMajorant delta X y k t := by
  unfold selbergRightLineLevel selbergRightLineMajorant
  calc
    ‖∑ μ ∈ Finset.Icc 1 X, ∑ ν ∈ Finset.Icc 1 X,
        ((selbergSqrtZetaTaperedCoeff X μ : ℂ) *
          (selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
          selbergGaussianMellinLineTerm delta y μ ν (k + 1) t‖ ≤
      ∑ μ ∈ Finset.Icc 1 X, ‖∑ ν ∈ Finset.Icc 1 X,
        ((selbergSqrtZetaTaperedCoeff X μ : ℂ) *
          (selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
          selbergGaussianMellinLineTerm delta y μ ν (k + 1) t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ μ ∈ Finset.Icc 1 X, ∑ ν ∈ Finset.Icc 1 X,
        ‖((selbergSqrtZetaTaperedCoeff X μ : ℂ) *
          (selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
          selbergGaussianMellinLineTerm delta y μ ν (k + 1) t‖ := by
      apply Finset.sum_le_sum
      intro μ _hμ
      exact norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro μ _hμ
      apply Finset.sum_congr rfl
      intro ν _hν
      rw [norm_mul]

/-- Tonelli's condition for the right-line expansion: the series of the
integrated level norms converges, by the exact `n⁻²` estimate. -/
theorem summable_integral_norm_selbergRightLineLevel
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    Summable (fun k : ℕ => ∫ t : ℝ,
      ‖selbergRightLineLevel delta X y k t‖) := by
  let B : ℕ → ℝ := fun k =>
    ∑ μ ∈ Finset.Icc 1 X, ∑ ν ∈ Finset.Icc 1 X,
      ‖((selbergSqrtZetaTaperedCoeff X μ : ℂ) *
        (selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ))‖ *
        (∫ t : ℝ, ‖selbergGaussianMellinLineTerm
          delta y μ ν (k + 1) t‖)
  have hB : Summable B := by
    dsimp [B]
    apply summable_sum
    intro μ hμ
    apply summable_sum
    intro ν hν
    exact (summable_integral_norm_selbergGaussianMellinLineTerm_add_one
      hdelta0 hdeltaPi y (Finset.mem_Icc.mp hμ).1
        (Finset.mem_Icc.mp hν).1).mul_left _
  apply Summable.of_nonneg_of_le
  · intro k
    exact MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  · intro k
    calc
      (∫ t : ℝ, ‖selbergRightLineLevel delta X y k t‖) ≤
          ∫ t : ℝ, selbergRightLineMajorant delta X y k t := by
        exact MeasureTheory.integral_mono
          (integrable_selbergRightLineLevel hdelta0 hdeltaPi y X k).norm
          (integrable_selbergRightLineMajorant hdelta0 hdeltaPi y X k)
          (norm_selbergRightLineLevel_le_majorant delta X y k)
      _ = B k := by
        unfold selbergRightLineMajorant
        rw [MeasureTheory.integral_finsetSum (Finset.Icc 1 X)]
        · apply Finset.sum_congr rfl
          intro μ hμ
          rw [MeasureTheory.integral_finsetSum (Finset.Icc 1 X)]
          · apply Finset.sum_congr rfl
            intro ν hν
            rw [MeasureTheory.integral_const_mul]
          · intro ν hν
            exact ((integrable_selbergGaussianMellinLineTerm
              hdelta0 hdeltaPi y (Finset.mem_Icc.mp hμ).1
                (Finset.mem_Icc.mp hν).1 (Nat.succ_pos k)).norm).const_mul _
        · intro μ hμ
          apply MeasureTheory.integrable_finsetSum
          intro ν hν
          exact ((integrable_selbergGaussianMellinLineTerm
            hdelta0 hdeltaPi y (Finset.mem_Icc.mp hμ).1
              (Finset.mem_Icc.mp hν).1 (Nat.succ_pos k)).norm).const_mul _
  · exact hB

/-- Absolute convergence justifies exchanging the right-line integral and
the positive zeta Dirichlet series. -/
theorem integral_selbergMellinRaw_rightLine_eq_tsum_integral
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    (∫ t : ℝ, selbergMellinRawIntegrand
      (selbergFourierZ delta y) X ((2 : ℂ) + I * t)) =
      ∑' k : ℕ, ∫ t : ℝ, selbergRightLineLevel delta X y k t := by
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
    (selbergMellinRaw_rightLine_eq_tsum hdelta0 hdeltaPi y X))]
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun k => integrable_selbergRightLineLevel hdelta0 hdeltaPi y X k)
    (summable_integral_norm_selbergRightLineLevel
      hdelta0 hdeltaPi y X)).symm

/-- Termwise complex Gaussian inversion turns one integrated right-line
level into the corresponding theta level. -/
theorem normalized_integral_selbergRightLineLevel_eq_thetaLevel
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X k : ℕ) :
    (1 / (4 * Real.pi) : ℂ) *
        (∫ t : ℝ, selbergRightLineLevel delta X y k t) =
      selbergNonconstantThetaLevel delta X y k := by
  unfold selbergRightLineLevel selbergNonconstantThetaLevel
  rw [MeasureTheory.integral_finsetSum (Finset.Icc 1 X)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro μ hμ
    rw [MeasureTheory.integral_finsetSum (Finset.Icc 1 X)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      rw [MeasureTheory.integral_const_mul]
      have hterm := integral_selbergGaussianMellin_eq_thetaTerm
        hdelta0 hdeltaPi y (Finset.mem_Icc.mp hμ).1
          (Finset.mem_Icc.mp hν).1 (Nat.succ_pos k)
      rw [show k + 1 = k.succ by omega]
      unfold selbergGaussianMellinLineTerm
      rw [← hterm]
      ring_nf
    · intro ν hν
      exact (integrable_selbergGaussianMellinLineTerm
        hdelta0 hdeltaPi y (Finset.mem_Icc.mp hμ).1
          (Finset.mem_Icc.mp hν).1 (Nat.succ_pos k)).const_mul _
  · intro μ hμ
    apply MeasureTheory.integrable_finsetSum
    intro ν hν
    exact (integrable_selbergGaussianMellinLineTerm
      hdelta0 hdeltaPi y (Finset.mem_Icc.mp hμ).1
        (Finset.mem_Icc.mp hν).1 (Nat.succ_pos k)).const_mul _

/-- Exact evaluation of Selberg's normalized right vertical integral as
the nonconstant theta kernel. -/
theorem normalized_integral_selbergMellinRaw_rightLine_eq_thetaKernel
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (y : ℝ) (X : ℕ) :
    (1 / (4 * Real.pi) : ℂ) *
        (∫ t : ℝ, selbergMellinRawIntegrand
          (selbergFourierZ delta y) X ((2 : ℂ) + I * t)) =
      selbergNonconstantThetaKernel delta X y := by
  rw [integral_selbergMellinRaw_rightLine_eq_tsum_integral
    hdelta0 hdeltaPi y X]
  rw [← tsum_mul_left]
  calc
    (∑' k : ℕ, (1 / (4 * Real.pi) : ℂ) *
        (∫ t : ℝ, selbergRightLineLevel delta X y k t)) =
        ∑' k : ℕ, selbergNonconstantThetaLevel delta X y k := by
      apply tsum_congr
      intro k
      exact normalized_integral_selbergRightLineLevel_eq_thetaLevel
        hdelta0 hdeltaPi y X k
    _ = selbergNonconstantThetaKernel delta X y :=
      (hasSum_selbergNonconstantThetaLevel hdelta0 hdeltaPi X y).tsum_eq

end HardyTheorem
