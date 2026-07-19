import PrimeNumberTheorem.DirichletPolynomialMeanSquare
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

end CarlsonZeroDensity
end PrimeNumberTheorem
