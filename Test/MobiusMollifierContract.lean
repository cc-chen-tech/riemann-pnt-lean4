import PrimeNumberTheorem.MobiusMollifier

open Complex
open scoped Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (X : ℕ) (s : ℂ) :
    mobiusMollifier X s =
      ∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s :=
  rfl

example (X : ℕ) (sigma t : ℝ) :
    mobiusMollifier X ((sigma : ℂ) + Complex.I * t) =
      DirichletPolynomial.finiteDirichletPolynomial (Finset.Icc 1 X)
        (mobiusMollifierCoefficient sigma) t :=
  mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial X sigma t

example {n : ℕ} (hn : 0 < n) (sigma : ℝ) :
    ‖mobiusMollifierCoefficient sigma n‖ ≤ (n : ℝ) ^ (-sigma) :=
  norm_mobiusMollifierCoefficient_le hn sigma

example (X : ℕ) (sigma : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
        ‖mobiusMollifierCoefficient sigma m‖ *
          ‖mobiusMollifierCoefficient sigma n‖ *
            if m = n then b - a
            else 2 / |Real.log n - Real.log m| :=
  mobiusMollifier_meanSquare_le hab

example (X : ℕ) (sigma : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ‖mobiusMollifierCoefficient sigma n‖ ^ 2 :=
  mobiusMollifier_meanSquare_le_carneiroLittmann X sigma hab

example (X : ℕ) (sigma : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc 1 X,
          ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 :=
  mobiusMollifier_meanSquare_le_weightedPowerSum X sigma hab

#print axioms mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial
#print axioms norm_mobiusMollifierCoefficient_le
#print axioms mobiusMollifier_meanSquare_le
#print axioms mobiusMollifier_meanSquare_le_carneiroLittmann
#print axioms mobiusMollifier_meanSquare_le_weightedPowerSum
#print axioms inv_nat_cpow_verticalLine_eq_exp

end CarlsonZeroDensity
end PrimeNumberTheorem
