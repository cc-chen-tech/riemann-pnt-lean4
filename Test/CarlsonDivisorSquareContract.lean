import PrimeNumberTheorem.CarlsonDivisorSquare
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators ArithmeticFunction.sigma

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (n : ℕ) :
    fourfoldDivisorCount n =
      (ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) n :=
  rfl

example (n : ℕ) :
    tripleDivisorCount n =
      (ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta) n :=
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

example {L U : ℕ} (hL : 0 < L) (sigma : ℝ) :
    ∑ n ∈ Finset.Icc L U,
        ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 ≤
      ∑ n ∈ Finset.Icc L U,
        (fourfoldDivisorCount n : ℝ) * ((n : ℝ) ^ (-sigma)) ^ 2 :=
  divisorSquareSum_le_fourfoldDivisorCount hL sigma

example (Y : ℕ) :
    ∑ n ∈ Finset.Ioc 0 Y, tripleDivisorCount n =
      ∑ n ∈ Finset.Ioc 0 Y,
        ArithmeticFunction.sigma 0 n * (Y / n) :=
  sum_Ioc_tripleDivisorCount_eq_sum_div Y

example (Y : ℕ) :
    ∑ n ∈ Finset.Ioc 0 Y, fourfoldDivisorCount n =
      ∑ n ∈ Finset.Ioc 0 Y, tripleDivisorCount n * (Y / n) :=
  sum_Ioc_fourfoldDivisorCount_eq_sum_div Y

example {c f : ℕ → ℝ} {L U : ℕ} {K : ℝ}
    (hL : 0 < L) (hLU : L ≤ U)
    (hc : ∀ n, 0 ≤ c n) (hf : ∀ n, 0 ≤ f n)
    (hfAnti : ∀ ⦃m n : ℕ⦄, L ≤ m → m ≤ n → n ≤ U → f n ≤ f m)
    (hprefix : ∀ n : ℕ, n ≤ U →
      ∑ k ∈ Finset.range (n + 1), c k ≤ K * (n + 1 : ℕ)) :
    ∑ n ∈ Finset.Icc L U, f n * c n ≤
      K * ((L : ℝ) * f L + ∑ n ∈ Finset.Icc L U, f n) :=
  sum_Icc_mul_le_prefixSlope hL hLU hc hf hfAnti hprefix

example {f : ℕ → ℝ} {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (hf : ∀ n, 0 ≤ f n)
    (hfAnti : ∀ ⦃m n : ℕ⦄, L ≤ m → m ≤ n → n ≤ U → f n ≤ f m) :
    ∑ n ∈ Finset.Icc L U, f n * (fourfoldDivisorCount n : ℝ) ≤
      (1 + Real.log U) ^ 3 *
        ((L : ℝ) * f L + ∑ n ∈ Finset.Icc L U, f n) :=
  fourfoldDivisorSum_mul_le_prefixSlope hL hLU hf hfAnti

example {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {q : ℝ}
    (hqNeg : q ≤ 0) (hq : -1 < q) :
    ∑ n ∈ Finset.Icc L U, (n : ℝ) ^ q ≤
      (L : ℝ) ^ q +
        ((U : ℝ) ^ (q + 1) - (L : ℝ) ^ (q + 1)) / (q + 1) :=
  sum_Icc_rpow_le_add_div_of_neg_one_lt hL hLU hqNeg hq

example {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {q : ℝ}
    (hq : q < -1) :
    ∑ n ∈ Finset.Icc L U, (n : ℝ) ^ q ≤
      (L : ℝ) ^ q +
        ((U : ℝ) ^ (q + 1) - (L : ℝ) ^ (q + 1)) / (q + 1) :=
  sum_Icc_rpow_le_add_div_of_lt_neg_one hL hLU hq

example {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {q : ℝ} (hq : q < -1) :
    ∑ n ∈ Finset.Icc L U,
        (fourfoldDivisorCount n : ℝ) * (n : ℝ) ^ q ≤
      (1 + Real.log U) ^ 3 *
        ((2 + 1 / (-q - 1)) * (L : ℝ) ^ (q + 1)) :=
  fourfoldDivisorRpowSum_le_lowerEndpoint hL hLU hq

example {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {q : ℝ}
    (hqNeg : q ≤ 0) (hq : -1 < q) :
    ∑ n ∈ Finset.Icc L U,
        (fourfoldDivisorCount n : ℝ) * (n : ℝ) ^ q ≤
      (1 + Real.log U) ^ 3 *
        ((2 + 1 / (q + 1)) * (U : ℝ) ^ (q + 1)) :=
  fourfoldDivisorRpowSum_le_upperEndpoint hL hLU hqNeg hq

example {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) :
    ∑ n ∈ Finset.Icc L U,
        (fourfoldDivisorCount n : ℝ) * ((n : ℝ) ^ (-sigma)) ^ 2 ≤
      (1 + Real.log U) ^ 3 *
        ((2 + 1 / (2 * sigma - 1)) * (L : ℝ) ^ (1 - 2 * sigma)) :=
  unweightedFourfoldDivisorSum_le_sharp hL hLU hsigma

example {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    ∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
          ((n : ℝ) ^ (-sigma)) ^ 2 ≤
      2 * ((1 + Real.log U) ^ 3 *
        ((2 + 1 / (2 - 2 * sigma)) * (U : ℝ) ^ (2 - 2 * sigma))) :=
  weightedFourfoldDivisorSum_le_sharp hL hLU hsigma hsigma1

example (Y : ℕ) :
    fourfoldDivisorPrefix Y =
      ∑ a ∈ Finset.Ioc 0 Y,
        ∑ b ∈ Finset.Ioc 0 (Y / a),
          ∑ c ∈ Finset.Ioc 0 ((Y / a) / b), ((Y / a) / b) / c :=
  rfl

example (Y : ℕ) :
    ∑ n ∈ Finset.Ioc 0 Y, fourfoldDivisorCount n =
      fourfoldDivisorPrefix Y :=
  sum_Ioc_fourfoldDivisorCount_eq_fourfoldDivisorPrefix Y

example (Y : ℕ) :
    (fourfoldDivisorPrefix Y : ℝ) ≤
      (Y : ℝ) * (harmonic Y : ℝ) ^ 3 :=
  fourfoldDivisorPrefix_le_mul_harmonic_cube Y

example (Y : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Y, (fourfoldDivisorCount n : ℝ)) ≤
      (Y : ℝ) * (1 + Real.log Y) ^ 3 :=
  sum_Ioc_fourfoldDivisorCount_le_mul_one_add_log_cube Y

example {L U : ℕ} (hL : 0 < L) {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    ∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
          ((n : ℝ) ^ (-sigma)) ^ 2 ≤
      2 * (L : ℝ) ^ (1 - 2 * sigma) *
        ((U : ℝ) * (1 + Real.log U) ^ 3) :=
  weightedFourfoldDivisorSum_le_prefix_bound hL hsigma

#print axioms card_divisorsAntidiagonal_eq_card_divisors
#print axioms card_divisors_sq_le_fourfoldDivisorCount_prime_pow
#print axioms card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount
#print axioms weightedDivisorSquareSum_le_fourfoldDivisorCount
#print axioms divisorSquareSum_le_fourfoldDivisorCount
#print axioms sum_Icc_mul_le_prefixSlope
#print axioms fourfoldDivisorSum_mul_le_prefixSlope
#print axioms sum_Icc_rpow_le_add_div_of_neg_one_lt
#print axioms sum_Icc_rpow_le_add_div_of_lt_neg_one
#print axioms fourfoldDivisorRpowSum_le_lowerEndpoint
#print axioms fourfoldDivisorRpowSum_le_upperEndpoint
#print axioms unweightedFourfoldDivisorSum_le_sharp
#print axioms weightedFourfoldDivisorSum_le_sharp
#print axioms sum_Ioc_tripleDivisorCount_eq_sum_div
#print axioms sum_Ioc_fourfoldDivisorCount_eq_sum_div
#print axioms sum_Ioc_fourfoldDivisorCount_eq_fourfoldDivisorPrefix
#print axioms fourfoldDivisorPrefix_le_mul_harmonic_cube
#print axioms sum_Ioc_fourfoldDivisorCount_le_mul_one_add_log_cube
#print axioms weightedFourfoldDivisorSum_le_prefix_bound

end CarlsonZeroDensity
end PrimeNumberTheorem
