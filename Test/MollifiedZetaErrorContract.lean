import PrimeNumberTheorem.MollifiedZetaError

open Complex
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (X : ℕ) (s : ℂ) :
    mollifiedZetaError X s = riemannZeta s * mobiusMollifier X s - 1 :=
  rfl

example {X : ℕ} {s : ℂ} (hs : 1 < s.re) :
    mollifiedZetaError X s =
      riemannZeta s *
        (mobiusMollifier X s -
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s) :=
  mollifiedZetaError_eq_riemannZeta_mul_mobius_tail hs

example {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    ‖mollifiedZetaError X s‖ ≤ (5 / 9 : ℝ) :=
  norm_mollifiedZetaError_le_five_ninth_of_four_le_re hX hs

#check norm_mollifiedZetaError_le_five_thirds_div_sub_one_of_four_le_re

example {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 4 ≤ s.re) :
    ‖mollifiedZetaError X s‖ < 1 :=
  norm_mollifiedZetaError_lt_one_of_four_le_re hX hs

example (X : ℕ) (x : ℝ) (s : ℂ) :
    truncatedZetaPolynomial x s * mobiusMollifier X s =
      mollifiedTruncatedPolynomial X (Nat.floor x) s :=
  truncatedZetaPolynomial_mul_mobiusMollifier X x s

noncomputable example (X N : ℕ) (sigma : ℝ) (n : ℕ) : ℂ :=
  mollifiedTailCoefficient X N sigma n

example (X N n : ℕ) (sigma : ℝ) (hn : 0 < n) :
    ‖mollifiedTailCoefficient X N sigma n‖ ≤
      (n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma) :=
  norm_mollifiedTailCoefficient_le X N sigma hn

example (X N : ℕ) (sigma : ℝ) :
    ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ((n : ℝ) + 1) * ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ((n : ℝ) + 1) *
          ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 :=
  mollifiedTailCoefficient_weightedSquareSum_le X N sigma

example (X N : ℕ) (sigma : ℝ) :
    ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        ((n : ℝ) + 1) *
          ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 :=
  mollifiedTailCoefficient_squareSum_le_weightedDivisorSquareSum X N sigma

example (X N : ℕ) (sigma t : ℝ) :
    (∑ n ∈ Finset.Icc (min X N + 1) (N * X),
        mollifiedTruncatedCoefficient X N n /
          (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)) =
      DirichletPolynomial.finiteDirichletPolynomial
        (Finset.Icc (min X N + 1) (N * X))
        (mollifiedTailCoefficient X N sigma) t :=
  mollifiedTruncatedTail_verticalLine_eq_finiteDirichletPolynomial X N sigma t

example {X N : ℕ} {sigma a b C : ℝ} (hab : a ≤ b)
    (hHilbert : ∀ d : ℕ → ℂ,
      ‖DirichletPolynomial.hilbertForm
          (Finset.Icc (min X N + 1) (N * X)) d
          (fun n : ℕ => -Real.log n)‖ ≤
        C * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * ‖d n‖ ^ 2) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 +
        2 * C * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 :=
  mollifiedTruncatedTail_meanSquare_le_of_hilbert hab hHilbert

example {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 +
        4 * Real.pi * ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * ‖mollifiedTailCoefficient X N sigma n‖ ^ 2 :=
  mollifiedTruncatedTail_meanSquare_le_carneiroLittmann hab

example {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) *
            ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 :=
  mollifiedTruncatedTail_meanSquare_le_weightedDivisorSquareSum hab

example {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
            ((n : ℝ) ^ (-sigma)) ^ 2 :=
  mollifiedTruncatedTail_meanSquare_le_fourfoldDivisorCount hab

example {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            (fourfoldDivisorCount n : ℝ) *
              ((n : ℝ) ^ (-sigma)) ^ 2 +
        4 * Real.pi *
          ∑ n ∈ Finset.Icc (min X N + 1) (N * X),
            ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
              ((n : ℝ) ^ (-sigma)) ^ 2 :=
  mollifiedTruncatedTail_meanSquare_le_separatedFourfoldDivisorSums hab

example {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsupport : min X N + 1 ≤ N * X)
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      (b - a) * ((1 + Real.log (N * X)) ^ 3 *
        ((2 + 1 / (2 * sigma - 1)) *
          ((min X N + 1 : ℕ) : ℝ) ^ (1 - 2 * sigma))) +
        8 * Real.pi * ((1 + Real.log (N * X)) ^ 3 *
          ((2 + 1 / (2 - 2 * sigma)) *
            ((N * X : ℕ) : ℝ) ^ (2 - 2 * sigma))) :=
  mollifiedTruncatedTail_meanSquare_le_sharpDivisorEndpoint
    hab hsupport hsigma hsigma1

example {X N : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsigma : 1 / 2 < sigma) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc (min X N + 1) (N * X),
          mollifiedTruncatedCoefficient X N n /
            (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      ((b - a) + 4 * Real.pi) *
        (2 * ((min X N + 1 : ℕ) : ℝ) ^ (1 - 2 * sigma) *
          (((N * X : ℕ) : ℝ) * (1 + Real.log (N * X)) ^ 3)) :=
  mollifiedTruncatedTail_meanSquare_le_prefix_bound hab hsigma

example {X : ℕ} (hX : 0 < X) (s : ℂ) (x : ℝ)
    (hfloor : 0 < Nat.floor x) :
    mollifiedZetaError X s =
        (∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
            (Nat.floor x * X),
          mollifiedTruncatedCoefficient X (Nat.floor x) n /
            (n : ℂ) ^ s) +
          carlsonZetaRemainder s x * mobiusMollifier X s :=
  mollifiedZetaError_eq_tail_add_canonicalRemainder hX s x hfloor

example {X : ℕ} (hX : 0 < X) (s : ℂ) (x : ℝ)
    (hfloor : 0 < Nat.floor x) :
    ‖mollifiedZetaError X s‖ ^ 2 ≤
        2 * ‖∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
            (Nat.floor x * X),
          mollifiedTruncatedCoefficient X (Nat.floor x) n /
            (n : ℂ) ^ s‖ ^ 2 +
          2 * ‖carlsonZetaRemainder s x * mobiusMollifier X s‖ ^ 2 :=
  norm_mollifiedZetaError_sq_le_tail_add_canonicalRemainder hX s x hfloor

example {X : ℕ} (hX : 1 ≤ X) {sigma a b x K : ℝ}
    (hab : a ≤ b) (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1)
    (hK : 0 ≤ K)
    (hR : ∀ t ∈ Set.Icc a b,
      ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x‖ ≤ K) :
    ∫ t in a..b,
        ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
          mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
      K ^ 2 * (((b - a) + 4 * Real.pi) *
        (2 * (1 +
          ((X : ℝ) ^ (2 - 2 * sigma) - 1) / (2 - 2 * sigma)))) :=
  canonicalRemainder_mul_mobius_meanSquare_le
    hX hab hsigma hsigma1 hK hR

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
        ∫ t in a..b,
            ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
              mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
          (C * x ^ (-sigma)) ^ 2 * (((b - a) + 4 * Real.pi) *
            (2 * (1 +
              ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                (2 - 2 * sigma)))) :=
  exists_canonicalRemainder_mul_mobius_meanSquare_le

example :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (kappa : ℝ) (X : ℕ) (sigma a b x : ℝ),
      0 < kappa →
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b,
        |t| ≤ x / 2 ∧ x ≤ kappa * |t|) →
        ∫ t in a..b,
            ‖carlsonZetaRemainder ((sigma : ℂ) + Complex.I * t) x *
              mobiusMollifier X ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
          ((A + kappa) * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma)))) :=
  exists_canonicalRemainder_mul_mobius_meanSquare_le_of_comparable

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
        ∫ t in a..b,
            ‖mollifiedZetaError X
              ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((C * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) :=
  exists_mollifiedZetaError_meanSquare_le_endpoint

example :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (kappa : ℝ) (X : ℕ) (sigma a b x : ℝ),
      0 < kappa →
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b,
        |t| ≤ x / 2 ∧ x ≤ kappa * |t|) →
        ∫ t in a..b,
            ‖mollifiedZetaError X
              ((sigma : ℂ) + Complex.I * t)‖ ^ 2 ≤
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((((A + kappa) * x ^ (-sigma)) ^ 2) *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) :=
  exists_mollifiedZetaError_meanSquare_le_endpoint_of_comparable

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            ‖R‖ ≤ C * x ^ (-s.re) ∧
            mollifiedZetaError X s =
              (truncatedZetaPolynomial x s * mobiusMollifier X s - 1) +
                R * mobiusMollifier X s ∧
            ‖mollifiedZetaError X s‖ ^ 2 ≤
              2 * ‖truncatedZetaPolynomial x s * mobiusMollifier X s - 1‖ ^ 2 +
                2 * ‖R * mobiusMollifier X s‖ ^ 2 :=
  exists_mollifiedZetaError_decomposition

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            ‖R‖ ≤ C * x ^ (-s.re) ∧
            mollifiedZetaError X s =
              (mollifiedTruncatedPolynomial X (Nat.floor x) s - 1) +
                R * mobiusMollifier X s ∧
            ‖mollifiedZetaError X s‖ ^ 2 ≤
              2 * ‖mollifiedTruncatedPolynomial X (Nat.floor x) s - 1‖ ^ 2 +
                2 * ‖R * mobiusMollifier X s‖ ^ 2 :=
  exists_mollifiedZetaError_coefficient_decomposition

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : ℂ) (x : ℝ),
      0 < X → (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            ‖R‖ ≤ C * x ^ (-s.re) ∧
            mollifiedZetaError X s =
                (∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
                    (Nat.floor x * X),
                  mollifiedTruncatedCoefficient X (Nat.floor x) n /
                    (n : ℂ) ^ s) + R * mobiusMollifier X s ∧
              ‖mollifiedZetaError X s‖ ^ 2 ≤
                2 * ‖∑ n ∈ Finset.Icc (min X (Nat.floor x) + 1)
                    (Nat.floor x * X),
                  mollifiedTruncatedCoefficient X (Nat.floor x) n /
                    (n : ℂ) ^ s‖ ^ 2 +
                  2 * ‖R * mobiusMollifier X s‖ ^ 2 :=
  exists_mollifiedZetaError_tail_decomposition

#print axioms exists_mollifiedZetaError_decomposition
#print axioms mollifiedZetaError_eq_riemannZeta_mul_mobius_tail
#print axioms norm_mollifiedZetaError_le_five_ninth_of_four_le_re
#print axioms norm_mollifiedZetaError_lt_one_of_four_le_re
#print axioms truncatedZetaPolynomial_mul_mobiusMollifier
#print axioms exists_mollifiedZetaError_coefficient_decomposition
#print axioms exists_mollifiedZetaError_tail_decomposition
#print axioms mollifiedTruncatedTail_verticalLine_eq_finiteDirichletPolynomial
#print axioms mollifiedTruncatedTail_meanSquare_le_of_hilbert
#print axioms mollifiedTruncatedTail_meanSquare_le_carneiroLittmann
#print axioms mollifiedTruncatedTail_meanSquare_le_weightedDivisorSquareSum
#print axioms mollifiedTruncatedTail_meanSquare_le_fourfoldDivisorCount
#print axioms mollifiedTruncatedTail_meanSquare_le_separatedFourfoldDivisorSums
#print axioms mollifiedTruncatedTail_meanSquare_le_sharpDivisorEndpoint
#print axioms mollifiedZetaError_meanSquare_le_tail_add_remainder
#print axioms exists_mollifiedZetaError_meanSquare_le_sharpEndpoint_of_comparable
#print axioms mollifiedTruncatedTail_meanSquare_le_prefix_bound
#print axioms mollifiedZetaError_eq_tail_add_canonicalRemainder
#print axioms norm_mollifiedZetaError_sq_le_tail_add_canonicalRemainder
#print axioms canonicalRemainder_mul_mobius_meanSquare_le
#print axioms exists_canonicalRemainder_mul_mobius_meanSquare_le
#print axioms exists_canonicalRemainder_mul_mobius_meanSquare_le_of_comparable
#print axioms exists_mollifiedZetaError_meanSquare_le_endpoint
#print axioms exists_mollifiedZetaError_meanSquare_le_endpoint_of_comparable
#print axioms norm_mollifiedTailCoefficient_le
#print axioms mollifiedTailCoefficient_weightedSquareSum_le
#print axioms mollifiedTailCoefficient_squareSum_le_divisorSquareSum
#print axioms mollifiedTailCoefficient_squareSum_le_weightedDivisorSquareSum

end CarlsonZeroDensity
end PrimeNumberTheorem
