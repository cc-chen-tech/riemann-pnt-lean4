import PrimeNumberTheorem.DirichletPolynomialMeanSquare
import PrimeNumberTheorem.CarneiroLittmannKernelConstruction
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Complex
open scoped BigOperators ComplexConjugate Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The finite Möbius mollifier used in Carlson's zero-density argument. -/
noncomputable def mobiusMollifier (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s

/-- Coefficients of the Möbius mollifier restricted to a vertical line. -/
noncomputable def mobiusMollifierCoefficient (sigma : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) * ((n : ℂ) ^ (sigma : ℂ))⁻¹

/-- Möbius coefficients have modulus at most one, so the mollifier coefficient
on `Re s = sigma` is bounded by the expected real power. -/
theorem norm_mobiusMollifierCoefficient_le
    {n : ℕ} (hn : 0 < n) (sigma : ℝ) :
    ‖mobiusMollifierCoefficient sigma n‖ ≤ (n : ℝ) ^ (-sigma) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmuInt := ArithmeticFunction.abs_moebius_le_one (n := n)
  have hmuReal : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast hmuInt
  have hmuComplex : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_intCast] using hmuReal
  have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  unfold mobiusMollifierCoefficient
  rw [norm_mul, norm_inv, hnCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  simp only [Complex.ofReal_re]
  rw [Real.rpow_neg hnpos.le]
  have hinvnonneg : 0 ≤ ((n : ℝ) ^ sigma)⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg hnpos.le sigma)
  simpa using mul_le_mul_of_nonneg_right hmuComplex hinvnonneg

/-- Split a positive natural complex power on a vertical line into its real
decay coefficient and logarithmic oscillation. -/
theorem inv_nat_cpow_verticalLine_eq_exp
    {n : ℕ} (hn : n ≠ 0) (sigma t : ℝ) :
    1 / (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t) =
      ((n : ℂ) ^ (sigma : ℂ))⁻¹ *
        Complex.exp ((-Complex.I * (Real.log n : ℂ)) * t) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_add _ _ hnC, one_div, mul_inv_rev]
  calc
    ((n : ℂ) ^ (Complex.I * t))⁻¹ *
        ((n : ℂ) ^ (sigma : ℂ))⁻¹ =
        ((n : ℂ) ^ (sigma : ℂ))⁻¹ *
          ((n : ℂ) ^ (Complex.I * t))⁻¹ := mul_comm _ _
    _ = ((n : ℂ) ^ (sigma : ℂ))⁻¹ *
        Complex.exp ((-Complex.I * (Real.log n : ℂ)) * t) := by
      congr 1
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_neg,
        ← Complex.natCast_log]
      congr 1
      ring

/-- On a vertical line, the Möbius mollifier is a finite Dirichlet
polynomial with frequencies `-log n`. -/
theorem mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial
    (X : ℕ) (sigma t : ℝ) :
    mobiusMollifier X ((sigma : ℂ) + Complex.I * t) =
      DirichletPolynomial.finiteDirichletPolynomial (Finset.Icc 1 X)
        (mobiusMollifierCoefficient sigma) t := by
  unfold mobiusMollifier DirichletPolynomial.finiteDirichletPolynomial
    DirichletPolynomial.finiteExponentialSum
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
  have hinv := inv_nat_cpow_verticalLine_eq_exp hn0 sigma t
  rw [one_div] at hinv
  rw [div_eq_mul_inv, hinv]
  unfold mobiusMollifierCoefficient
  ring_nf
  congr 1
  push_cast
  ring_nf

/-- The finite-frequency mean-square estimate inherited by the Möbius
mollifier on every vertical line. -/
theorem mobiusMollifier_meanSquare_le
    {X : ℕ} {sigma : ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
        ‖mobiusMollifierCoefficient sigma m‖ *
          ‖mobiusMollifierCoefficient sigma n‖ *
            if m = n then b - a
            else 2 / |Real.log n - Real.log m| := by
  simp_rw [mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial]
  apply DirichletPolynomial.finiteDirichletPolynomial_meanSquare_le hab
  intro n hn
  exact (Finset.mem_Icc.mp hn).1

/-- The concrete Carneiro--Littmann Hilbert kernel gives a single weighted
diagonal bound for the Möbius mollifier mean square. -/
theorem mobiusMollifier_meanSquare_le_carneiroLittmann
    (X : ℕ) (sigma : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ‖mobiusMollifierCoefficient sigma n‖ ^ 2 := by
  let D : ℝ := ∑ n ∈ Finset.Icc 1 X,
    ((n : ℝ) + 1) * ‖mobiusMollifierCoefficient sigma n‖ ^ 2
  have hraw :
      ∫ t in a..b,
          ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
        (b - a) * ∑ n ∈ Finset.Icc 1 X,
            ‖mobiusMollifierCoefficient sigma n‖ ^ 2 +
          4 * Real.pi * D := by
    simp_rw [mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial]
    unfold DirichletPolynomial.finiteDirichletPolynomial
    simpa only [D, mul_assoc, show 2 * (2 * Real.pi) = 4 * Real.pi by ring] using
      (DirichletPolynomial.finiteExponentialSum_meanSquare_le_of_hilbert
        (S := Finset.Icc 1 X)
        (c := mobiusMollifierCoefficient sigma)
        (omega := fun n : ℕ => -Real.log n)
        (weight := fun n : ℕ => (n : ℝ) + 1)
        (C := 2 * Real.pi) hab
        (by
          intro m hm n hn hmn
          have hmpos : 0 < (m : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hm).1
          have hnpos : 0 < (n : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hn).1
          have hlog : Real.log (m : ℝ) = Real.log (n : ℝ) := by linarith
          exact Nat.cast_injective (Real.log_injOn_pos hmpos hnpos hlog))
        (by intro n hn; positivity)
        (fun d =>
          DirichletPolynomial.norm_hilbertForm_Icc_neg_log_le_carneiroLittmann
            (show 0 < (1 : ℕ) by omega) d))
  calc
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.Icc 1 X,
          ‖mobiusMollifierCoefficient sigma n‖ ^ 2 +
        4 * Real.pi * D := hraw
    _ ≤ (b - a) * D + 4 * Real.pi * D := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
        apply Finset.sum_le_sum
        intro n hn
        have hnorm : 0 ≤ ‖mobiusMollifierCoefficient sigma n‖ ^ 2 := sq_nonneg _
        have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      · exact le_rfl
    _ = ((b - a) + 4 * Real.pi) * D := by ring

/-- Replacing the Möbius coefficient by its pointwise power majorant leaves a
purely real weighted power sum for the mollifier mean square. -/
theorem mobiusMollifier_meanSquare_le_weightedPowerSum
    (X : ℕ) (sigma : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 := by
  calc
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ‖mobiusMollifierCoefficient sigma n‖ ^ 2 :=
      mobiusMollifier_meanSquare_le_carneiroLittmann X sigma hab
    _ ≤ ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro n hn
        have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
        have hcoeff := norm_mobiusMollifierCoefficient_le hnpos sigma
        have hcoeff_nonneg : 0 ≤ ‖mobiusMollifierCoefficient sigma n‖ := norm_nonneg _
        have hpower_nonneg : 0 ≤ (n : ℝ) ^ (-sigma) := Real.rpow_nonneg (by positivity) _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      · exact add_nonneg (sub_nonneg.mpr hab)
          (mul_nonneg (by norm_num) Real.pi_nonneg)

end CarlsonZeroDensity
end PrimeNumberTheorem
