import PrimeNumberTheorem.CarlsonDivisorSquare

open scoped BigOperators ArithmeticFunction.sigma

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (n : ℕ) :
    fourfoldDivisorCount n =
      (ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) n :=
  rfl

example (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card :=
  card_divisorsAntidiagonal_eq_card_divisors n

example {p k : ℕ} (hp : p.Prime) :
    (p ^ k).divisors.card ^ 2 ≤ fourfoldDivisorCount (p ^ k) :=
  card_divisors_sq_le_fourfoldDivisorCount_prime_pow hp k

example {n : ℕ} (hn : n ≠ 0) :
    n.divisorsAntidiagonal.card ^ 2 ≤ fourfoldDivisorCount n :=
  card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount hn

example {L U : ℕ} (hL : 0 < L) (sigma : ℝ) :
    ∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) *
          ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 ≤
      ∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
          ((n : ℝ) ^ (-sigma)) ^ 2 :=
  weightedDivisorSquareSum_le_fourfoldDivisorCount hL sigma

#print axioms card_divisorsAntidiagonal_eq_card_divisors
#print axioms card_divisors_sq_le_fourfoldDivisorCount_prime_pow
#print axioms card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount
#print axioms weightedDivisorSquareSum_le_fourfoldDivisorCount

end CarlsonZeroDensity
end PrimeNumberTheorem
