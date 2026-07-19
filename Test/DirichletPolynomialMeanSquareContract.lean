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

noncomputable example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) : ℂ :=
  hilbertForm S c omega

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) {a b : ℝ}
    (homega : Set.InjOn omega (S : Set ι)) :
    ((∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ) =
      (b - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) -
        Complex.I *
          (hilbertForm S (phaseTwist c omega b) omega -
            hilbertForm S (phaseTwist c omega a) omega) :=
  finiteExponentialMeanSquare_cast_eq_diagonal_add_hilbert homega

example {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    1 / |Real.log m - Real.log n| ≤ (n : ℝ) + 1 :=
  inv_abs_log_sub_log_le_nat_add_one hm hn hmn

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (weight : ι → ℝ)
    {a b C : ℝ} (hab : a ≤ b) (homega : Set.InjOn omega (S : Set ι))
    (hweight : ∀ n ∈ S, 0 ≤ weight n)
    (hHilbert : ∀ d : ι → ℂ,
      ‖hilbertForm S d omega‖ ≤
        C * ∑ n ∈ S, weight n * ‖d n‖ ^ 2) :
    ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ S, weight n * ‖c n‖ ^ 2 :=
  finiteExponentialSum_meanSquare_le_of_hilbert
    hab homega hweight hHilbert

#print axioms norm_integral_exp_I_mul_le_two_div
#print axioms finiteExponentialSum_meanSquare_le
#print axioms finiteDirichletPolynomial_meanSquare_le
#print axioms finiteExponentialMeanSquare_cast_eq_diagonal_add_hilbert
#print axioms inv_abs_log_sub_log_le_nat_add_one
#print axioms finiteExponentialSum_meanSquare_le_of_hilbert

end DirichletPolynomial
end PrimeNumberTheorem
