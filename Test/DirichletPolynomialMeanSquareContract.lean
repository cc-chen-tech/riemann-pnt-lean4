import PrimeNumberTheorem.DirichletPolynomialMeanSquare

open Complex
open scoped Interval

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example {a b d : ℝ} (hd : d ≠ 0) :
    ‖∫ t in a..b, Complex.exp (Complex.I * (d * t))‖ ≤ 2 / |d| :=
  norm_integral_exp_I_mul_le_two_div hd

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (homega : Set.InjOn omega (S : Set ι)) :
    ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 ≤
      ∑ m ∈ S, ∑ n ∈ S,
        ‖c m‖ * ‖c n‖ *
          if m = n then b - a else 2 / |omega n - omega m| :=
  finiteExponentialSum_meanSquare_le hab homega

example (S : Finset ℕ) (c : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ n ∈ S, 0 < n) :
    ∫ t in a..b, ‖finiteDirichletPolynomial S c t‖ ^ 2 ≤
      ∑ m ∈ S, ∑ n ∈ S,
        ‖c m‖ * ‖c n‖ *
          if m = n then b - a
          else 2 / |Real.log n - Real.log m| :=
  finiteDirichletPolynomial_meanSquare_le hab hpos

#print axioms norm_integral_exp_I_mul_le_two_div
#print axioms finiteExponentialSum_meanSquare_le
#print axioms finiteDirichletPolynomial_meanSquare_le

end DirichletPolynomial
end PrimeNumberTheorem
