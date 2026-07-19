import PrimeNumberTheorem.MobiusMollifier

open Complex Filter Topology
open scoped Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (X : ℕ) (s : ℂ) :
    mobiusMollifier X s =
      ∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s :=
  rfl

example (X : ℕ) (s : ℂ) :
    AnalyticAt ℂ (mobiusMollifier X) s :=
  analyticAt_mobiusMollifier X s

example (X : ℕ) (hX : 1 ≤ X) :
    Tendsto (fun x : ℝ => mobiusMollifier X (x : ℂ)) atTop (𝓝 1) :=
  tendsto_mobiusMollifier_atTop X hX

example (X : ℕ) (hX : 1 ≤ X) (s : ℂ) :
    analyticOrderAt (mobiusMollifier X) s ≠ ⊤ :=
  analyticOrderAt_mobiusMollifier_ne_top X hX s

example (X : ℕ) (sigma t : ℝ) :
    mobiusMollifier X ((sigma : ℂ) + Complex.I * t) =
      DirichletPolynomial.finiteDirichletPolynomial (Finset.Icc 1 X)
        (mobiusMollifierCoefficient sigma) t :=
  mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial X sigma t

example (X : ℕ) (sigma : ℝ) :
    Continuous (fun t : ℝ =>
      mobiusMollifier X ((sigma : ℂ) + Complex.I * t)) :=
  continuous_mobiusMollifier_verticalLine X sigma

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

example {X : ℕ} (hX : 1 ≤ X) {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    (∑ n ∈ Finset.Icc 1 X,
        ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2) ≤
      2 * (1 +
        ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma)) :=
  weightedPowerSum_le_rpow_endpoint hX hsigma hsigma1

example {X : ℕ} (hX : 1 ≤ X) {sigma a b : ℝ}
    (hab : a ≤ b) (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    ∫ t in a..b,
        ‖mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        (2 * (1 +
          ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma))) :=
  mobiusMollifier_meanSquare_le_rpow_endpoint hX hab hsigma hsigma1

#print axioms analyticAt_mobiusMollifier
#print axioms tendsto_mobiusMollifier_atTop
#print axioms analyticOrderAt_mobiusMollifier_ne_top
#print axioms mobiusMollifier_verticalLine_eq_finiteDirichletPolynomial
#print axioms continuous_mobiusMollifier_verticalLine
#print axioms norm_mobiusMollifierCoefficient_le
#print axioms mobiusMollifier_meanSquare_le
#print axioms mobiusMollifier_meanSquare_le_carneiroLittmann
#print axioms mobiusMollifier_meanSquare_le_weightedPowerSum
#print axioms weightedPowerSum_le_rpow_endpoint
#print axioms mobiusMollifier_meanSquare_le_rpow_endpoint
#print axioms inv_nat_cpow_verticalLine_eq_exp

end CarlsonZeroDensity
end PrimeNumberTheorem
