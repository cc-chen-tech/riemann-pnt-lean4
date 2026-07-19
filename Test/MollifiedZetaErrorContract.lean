import PrimeNumberTheorem.MollifiedZetaError

open Complex
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (X : ℕ) (s : ℂ) :
    mollifiedZetaError X s = riemannZeta s * mobiusMollifier X s - 1 :=
  rfl

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
#print axioms truncatedZetaPolynomial_mul_mobiusMollifier
#print axioms exists_mollifiedZetaError_coefficient_decomposition
#print axioms exists_mollifiedZetaError_tail_decomposition
#print axioms mollifiedTruncatedTail_verticalLine_eq_finiteDirichletPolynomial
#print axioms mollifiedTruncatedTail_meanSquare_le_of_hilbert
#print axioms mollifiedTruncatedTail_meanSquare_le_carneiroLittmann
#print axioms norm_mollifiedTailCoefficient_le
#print axioms mollifiedTailCoefficient_weightedSquareSum_le

end CarlsonZeroDensity
end PrimeNumberTheorem
