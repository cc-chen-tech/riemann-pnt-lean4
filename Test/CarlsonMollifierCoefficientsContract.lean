import PrimeNumberTheorem.CarlsonMollifierCoefficients

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (N n : ℕ) : ℂ := truncatedZetaArithmetic N n

example (X n : ℕ) : ℂ := truncatedMobiusArithmetic X n

example (X N n : ℕ) : ℂ := mollifiedTruncatedCoefficient X N n

noncomputable example (X N : ℕ) (s : ℂ) : ℂ := mollifiedTruncatedPolynomial X N s

example {X N n : ℕ} (hn : 0 < n) (hnX : n ≤ X) (hnN : n ≤ N) :
    mollifiedTruncatedCoefficient X N n = if n = 1 then 1 else 0 :=
  mollifiedTruncatedCoefficient_eq_one_apply hn hnX hnN

example (X N : ℕ) (s : ℂ) :
    (∑ m ∈ Finset.Icc 1 N, 1 / (m : ℂ) ^ s) *
        (∑ n ∈ Finset.Icc 1 X,
          (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s) =
      mollifiedTruncatedPolynomial X N s :=
  truncatedZeta_sum_mul_mobius_sum_eq_mollifiedTruncatedPolynomial X N s

example {X N : ℕ} (hX : 0 < X) (hN : 0 < N) (s : ℂ) :
    mollifiedTruncatedPolynomial X N s - 1 =
      ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        mollifiedTruncatedCoefficient X N n / (n : ℂ) ^ s :=
  mollifiedTruncatedPolynomial_sub_one_eq_tail hX hN s

#print axioms mollifiedTruncatedCoefficient_eq_one_apply
#print axioms truncatedZeta_sum_mul_mobius_sum_eq_mollifiedTruncatedPolynomial
#print axioms mollifiedTruncatedPolynomial_sub_one_eq_tail

end CarlsonZeroDensity
end PrimeNumberTheorem
