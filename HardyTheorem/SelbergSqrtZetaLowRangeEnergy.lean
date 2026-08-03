import HardyTheorem.SelbergSqrtZetaCollectedArithmetic
import HardyTheorem.SelbergMertensBound
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Low-range energy of Selberg's square-root zeta mollifier

The exact coefficient formula from
`SelbergSqrtZetaCollectedArithmetic` reduces the low-range energy estimate to
two elementary facts:

* `(Λ * Λ)(n) ≤ log(n)^2`;
* the weighted convolution `(Λ * Λ)(n) / n` is the Dirichlet convolution of
  `Λ(n) / n` with itself.

The second fact allows the truncated convolution sum to be bounded by the
square of Mertens' weighted von Mangoldt sum.
-/

/-- The von Mangoldt function with the Dirichlet-series weight `1 / n`. -/
noncomputable def weightedVonMangoldt : ArithmeticFunction ℝ :=
  ⟨fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ), by simp⟩

@[simp] theorem weightedVonMangoldt_apply (n : ℕ) :
    weightedVonMangoldt n =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
  rfl

/-- The self-convolution of the von Mangoldt function is nonnegative. -/
theorem vonMangoldt_selfConvolution_nonneg (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt *
      ArithmeticFunction.vonMangoldt) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun _ _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      ArithmeticFunction.vonMangoldt_nonneg

/-- The elementary pointwise bound `(Λ * Λ)(n) ≤ log(n)^2`. -/
theorem vonMangoldt_selfConvolution_le_log_sq
    {n : ℕ} (hn : 1 ≤ n) :
    (ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt) n ≤
      Real.log n ^ 2 := by
  rw [ArithmeticFunction.mul_apply]
  calc
    (∑ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt x.1 *
          ArithmeticFunction.vonMangoldt x.2) ≤
        ∑ x ∈ n.divisorsAntidiagonal,
          Real.log n *
            ArithmeticFunction.vonMangoldt x.2 := by
      apply Finset.sum_le_sum
      intro ij hij
      rcases Nat.mem_divisorsAntidiagonal.mp hij with
        ⟨hprod, hn0⟩
      have hprod0 : ij.1 * ij.2 ≠ 0 := by
        simpa [hprod] using hn0
      have hi0 : ij.1 ≠ 0 :=
        left_ne_zero_of_mul hprod0
      have hiDvd : ij.1 ∣ n := ⟨ij.2, hprod.symm⟩
      have hiLe : ij.1 ≤ n := Nat.le_of_dvd hn hiDvd
      have hlogLe : Real.log (ij.1 : ℝ) ≤ Real.log n :=
        Real.log_le_log
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi0)
          (by exact_mod_cast hiLe)
      exact mul_le_mul_of_nonneg_right
        (ArithmeticFunction.vonMangoldt_le_log.trans hlogLe)
        ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log n ^ 2 := by
      rw [Nat.sum_divisorsAntidiagonal'
        (fun _ j =>
          Real.log n * ArithmeticFunction.vonMangoldt j),
        ← Finset.mul_sum,
        ArithmeticFunction.vonMangoldt_sum]
      ring

/-- Dividing by `n` commutes with the von Mangoldt self-convolution. -/
theorem weightedVonMangoldt_mul_self_apply
    {n : ℕ} :
    (weightedVonMangoldt * weightedVonMangoldt) n =
      (ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt) n / (n : ℝ) := by
  rw [ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ij hij
  rcases Nat.mem_divisorsAntidiagonal.mp hij with
    ⟨hprod, hn0⟩
  have hprod0 : ij.1 * ij.2 ≠ 0 := by
    simpa [hprod] using hn0
  have hi0 : (ij.1 : ℝ) ≠ 0 := by
    exact_mod_cast left_ne_zero_of_mul hprod0
  have hj0 : (ij.2 : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hprod0
  simp only [weightedVonMangoldt_apply]
  rw [← hprod, Nat.cast_mul]
  field_simp

/-- The truncated weighted convolution sum is at most the square of the
truncated weighted von Mangoldt sum. -/
theorem sum_weightedVonMangoldt_selfConvolution_le_sq
    (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) n / (n : ℝ)) ≤
      (∑ n ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt n / (n : ℝ)) ^ 2 := by
  have hsets : Finset.Icc 1 X = Finset.Ioc 0 X := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hsets]
  calc
    (∑ n ∈ Finset.Ioc 0 X,
        (ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) n / (n : ℝ)) =
        ∑ n ∈ Finset.Ioc 0 X,
          (weightedVonMangoldt * weightedVonMangoldt) n := by
      apply Finset.sum_congr rfl
      intro n hn
      symm
      have hn1 : 1 ≤ n := by
        have := (Finset.mem_Ioc.mp hn).1
        omega
      exact weightedVonMangoldt_mul_self_apply
    _ = ∑ x ∈
          (Finset.Ioc 0 X).product (Finset.Ioc 0 X) with
            x.1 * x.2 ≤ X,
          weightedVonMangoldt x.1 * weightedVonMangoldt x.2 :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter
        weightedVonMangoldt weightedVonMangoldt X
    _ ≤ ∑ x ∈
          (Finset.Ioc 0 X).product (Finset.Ioc 0 X),
          weightedVonMangoldt x.1 * weightedVonMangoldt x.2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro x hx
      split_ifs
      · exact le_rfl
      · exact mul_nonneg
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Nat.cast_nonneg _))
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Nat.cast_nonneg _))
    _ = (∑ n ∈ Finset.Ioc 0 X,
          ArithmeticFunction.vonMangoldt n / (n : ℝ)) ^ 2 := by
      calc
        (∑ x ∈
            (Finset.Ioc 0 X).product (Finset.Ioc 0 X),
            weightedVonMangoldt x.1 *
              weightedVonMangoldt x.2) =
            ∑ i ∈ Finset.Ioc 0 X,
              ∑ j ∈ Finset.Ioc 0 X,
                weightedVonMangoldt i *
                  weightedVonMangoldt j := by
          exact Finset.sum_product _ _ _
        _ = (∑ n ∈ Finset.Ioc 0 X,
              ArithmeticFunction.vonMangoldt n / (n : ℝ)) ^ 2 := by
          simp only [weightedVonMangoldt_apply]
          rw [← Finset.sum_mul_sum]
          ring

/-- The normalized nonconstant low-range coefficient. -/
noncomputable def selbergSqrtZetaLowRangeCoeff
    (X n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.log X +
    (ArithmeticFunction.vonMangoldt *
      ArithmeticFunction.vonMangoldt) n /
        (4 * Real.log X ^ 2)

/-- The exact finite collected coefficient equals the normalized low-range
coefficient away from the constant term. -/
theorem selbergShortTaperedSqrtZeta_collected_eq_lowRangeCoeff
    {X n : ℕ} (hX : 1 < X) (hn : 1 < n) (hnX : n ≤ X) :
    (((selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta :
          ArithmeticFunction ℝ)) n) =
      selbergSqrtZetaLowRangeCoeff X n := by
  rw [selbergShortTaperedSqrtZeta_collected_apply_of_le
    hX (by omega) hnX, if_neg hn.ne']
  simp [selbergSqrtZetaLowRangeCoeff]

/-- Low-range coefficients are nonnegative. -/
theorem selbergSqrtZetaLowRangeCoeff_nonneg
    {X n : ℕ} (hX : 1 < X) :
    0 ≤ selbergSqrtZetaLowRangeCoeff X n := by
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  unfold selbergSqrtZetaLowRangeCoeff
  exact add_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog.le)
    (div_nonneg (vonMangoldt_selfConvolution_nonneg n)
      (by positivity))

/-- Every normalized low-range coefficient in the complete cutoff range is
at most `5/4`. -/
theorem selbergSqrtZetaLowRangeCoeff_le_five_fourths
    {X n : ℕ} (hX : 1 < X) (hn : 1 ≤ n) (hnX : n ≤ X) :
    selbergSqrtZetaLowRangeCoeff X n ≤ 5 / 4 := by
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlogLe : Real.log (n : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnX)
  have hvmLe :
      ArithmeticFunction.vonMangoldt n / Real.log X ≤ 1 := by
    rw [div_le_one hlogX]
    exact ArithmeticFunction.vonMangoldt_le_log.trans hlogLe
  have hconvLe :
      (ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) n /
          (4 * Real.log X ^ 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hsquares : Real.log (n : ℝ) ^ 2 ≤ Real.log X ^ 2 :=
      (sq_le_sq₀ hlogn hlogX.le).2 hlogLe
    nlinarith [vonMangoldt_selfConvolution_le_log_sq hn]
  unfold selbergSqrtZetaLowRangeCoeff
  linarith

/-- The weighted first moment of the normalized coefficients is controlled by
the explicit Mertens upper bound. -/
theorem sum_selbergSqrtZetaLowRangeCoeff_div_le
    {X : ℕ} (hX : 1 < X) :
    (∑ n ∈ Finset.Icc 1 X,
        selbergSqrtZetaLowRangeCoeff X n / (n : ℝ)) ≤
      (Real.log X + (Real.log 4 + 5)) / Real.log X +
        ((Real.log X + (Real.log 4 + 5)) / Real.log X) ^ 2 / 4 := by
  let S : ℝ :=
    ∑ n ∈ Finset.Icc 1 X,
      ArithmeticFunction.vonMangoldt n / (n : ℝ)
  let C : ℝ :=
    ∑ n ∈ Finset.Icc 1 X,
      (ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt) n / (n : ℝ)
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hSnonneg : 0 ≤ S := by
    unfold S
    exact Finset.sum_nonneg fun n _ =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Nat.cast_nonneg n)
  have hCnonneg : 0 ≤ C := by
    unfold C
    exact Finset.sum_nonneg fun n _ =>
      div_nonneg (vonMangoldt_selfConvolution_nonneg n)
        (Nat.cast_nonneg n)
  have hC : C ≤ S ^ 2 := by
    exact sum_weightedVonMangoldt_selfConvolution_le_sq X
  have hS :
      S ≤ Real.log X + (Real.log 4 + 5) := by
    exact vonMangoldt_sum_div_le_log_add (by omega)
  have hA_nonneg :
      0 ≤ Real.log X + (Real.log 4 + 5) :=
    hSnonneg.trans hS
  calc
    (∑ n ∈ Finset.Icc 1 X,
        selbergSqrtZetaLowRangeCoeff X n / (n : ℝ)) =
        S / Real.log X + C / (4 * Real.log X ^ 2) := by
      unfold S C
      calc
        (∑ n ∈ Finset.Icc 1 X,
            selbergSqrtZetaLowRangeCoeff X n / (n : ℝ)) =
            ∑ n ∈ Finset.Icc 1 X,
              ((ArithmeticFunction.vonMangoldt n / (n : ℝ)) /
                    Real.log X +
                  ((ArithmeticFunction.vonMangoldt *
                      ArithmeticFunction.vonMangoldt) n / (n : ℝ)) /
                    (4 * Real.log X ^ 2)) := by
          apply Finset.sum_congr rfl
          intro n hn
          have hn0 : (n : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
          unfold selbergSqrtZetaLowRangeCoeff
          field_simp
        _ = _ := by
          rw [Finset.sum_add_distrib,
            Finset.sum_div, Finset.sum_div]
    _ ≤ S / Real.log X + S ^ 2 / (4 * Real.log X ^ 2) := by
      gcongr
    _ ≤ (Real.log X + (Real.log 4 + 5)) / Real.log X +
        (Real.log X + (Real.log 4 + 5)) ^ 2 /
          (4 * Real.log X ^ 2) := by
      gcongr
    _ = (Real.log X + (Real.log 4 + 5)) / Real.log X +
        ((Real.log X + (Real.log 4 + 5)) / Real.log X) ^ 2 / 4 := by
      field_simp [ne_of_gt hlog]

/-- Squaring costs only a factor `5/4`, because every low-range coefficient
lies in `[0, 5/4]`. -/
theorem sum_sq_selbergSqrtZetaLowRangeCoeff_div_le_firstMoment
    {X : ℕ} (hX : 1 < X) :
    (∑ n ∈ Finset.Ioc 1 X,
        selbergSqrtZetaLowRangeCoeff X n ^ 2 / (n : ℝ)) ≤
      (5 / 4 : ℝ) *
        ∑ n ∈ Finset.Ioc 1 X,
          selbergSqrtZetaLowRangeCoeff X n / (n : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hnX : n ≤ X := (Finset.mem_Ioc.mp hn).2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq0 := selbergSqrtZetaLowRangeCoeff_nonneg
    (X := X) (n := n) hX
  have hq5 := selbergSqrtZetaLowRangeCoeff_le_five_fourths
    hX hn1 hnX
  field_simp [ne_of_gt hnpos]
  nlinarith

/-- Once `log X` dominates the fixed Mertens constant, the complete
low-range coefficient energy is bounded by the absolute constant `15/4`. -/
theorem sum_sq_selbergSqrtZetaLowRangeCoeff_div_le_fifteen_fourths
    {X : ℕ} (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    (∑ n ∈ Finset.Ioc 1 X,
        selbergSqrtZetaLowRangeCoeff X n ^ 2 / (n : ℝ)) ≤
      (15 : ℝ) / 4 := by
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hfirst :=
    sum_selbergSqrtZetaLowRangeCoeff_div_le hX
  have hset : Finset.Icc 1 X = insert 1 (Finset.Ioc 1 X) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_Ioc]
    omega
  have hq1 : selbergSqrtZetaLowRangeCoeff X 1 = 0 := by
    simp [selbergSqrtZetaLowRangeCoeff]
  rw [hset, Finset.sum_insert (by simp), hq1,
    zero_div, zero_add] at hfirst
  have hratio :
      (Real.log X + (Real.log 4 + 5)) / Real.log X ≤ 2 := by
    rw [div_le_iff₀ hlog]
    linarith
  calc
    (∑ n ∈ Finset.Ioc 1 X,
        selbergSqrtZetaLowRangeCoeff X n ^ 2 / (n : ℝ)) ≤
        (5 / 4 : ℝ) *
          ∑ n ∈ Finset.Ioc 1 X,
            selbergSqrtZetaLowRangeCoeff X n / (n : ℝ) :=
      sum_sq_selbergSqrtZetaLowRangeCoeff_div_le_firstMoment hX
    _ ≤ (5 / 4 : ℝ) *
        ((Real.log X + (Real.log 4 + 5)) / Real.log X +
          ((Real.log X + (Real.log 4 + 5)) / Real.log X) ^ 2 / 4) := by
      gcongr
    _ ≤ 15 / 4 := by
      have hratio_nonneg :
          0 ≤ (Real.log X + (Real.log 4 + 5)) / Real.log X := by
        positivity
      nlinarith

end HardyTheorem
