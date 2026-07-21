import HardyTheorem.SelbergShortCollectedArithmetic
import MathlibAux.FiberwiseNormSq

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Finite square energy of the collected Selberg short coefficients

The collected coefficient at `k` is a finite sum over the admissible
factor-pair fiber `d * l = k`.  Applying finite Cauchy--Schwarz separately
at each `k` retains the cardinality of that particular multiplicative fiber.
No estimate strong enough for Selberg's positive-proportion theorem is
asserted here.
-/

/-- One summand in the factor-pair expansion of the collected critical-line
coefficient at product index `k`. -/
noncomputable def selbergShortCollectedPairTerm
    (N X k : ℕ) (p : ℕ × ℕ) : ℂ :=
  ((selbergMollifiedDirichletCoeff N X p.1 *
      selbergMoebiusCoeff X p.2 : ℝ) : ℂ) *
    (Real.sqrt (k : ℝ) : ℂ)⁻¹

/-- The collected triple coefficient is exactly the sum of its normalized
factor-pair terms. -/
theorem selbergShortDirichletCollectedCoeff_eq_pairSum
    (N X k : ℕ) :
    selbergShortDirichletCollectedCoeff N X k =
      ∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
        selbergShortCollectedPairTerm N X k p := by
  classical
  rw [selbergShortDirichletCollectedCoeff_eq_convolution]
  unfold selbergShortCollectedDirichletConvolution
  unfold selbergShortCollectedPairTerm
  push_cast
  rw [Finset.sum_mul]

/-- Fiberwise finite Cauchy--Schwarz for one collected product coefficient.
The loss is the cardinality of the actual admissible factor-pair fiber at
`k`, rather than the cardinality of the full triple support. -/
theorem normSq_selbergShortDirichletCollectedCoeff_le_pairFiber
    (N X k : ℕ) :
    Complex.normSq (selbergShortDirichletCollectedCoeff N X k) ≤
      (selbergMollifiedDirichletPairs (N * X) X k).card *
        ∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
          Complex.normSq (selbergShortCollectedPairTerm N X k p) := by
  rw [selbergShortDirichletCollectedCoeff_eq_pairSum]
  exact MathlibAux.normSq_finset_sum_le_card_mul_sum_normSq
    (selbergMollifiedDirichletPairs (N * X) X k)
    (selbergShortCollectedPairTerm N X k)

/-- A finite total square-energy bound for all collected triple coefficients.
Each product index keeps its own multiplicative-fiber cardinality and its own
fiberwise square mass. -/
theorem sum_normSq_selbergShortDirichletCollectedCoeff_le_pairFiberEnergy
    (N X : ℕ) :
    (∑ k ∈ selbergShortDirichletCollectedSupport N X,
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) ≤
      ∑ k ∈ selbergShortDirichletCollectedSupport N X,
        (selbergMollifiedDirichletPairs (N * X) X k).card *
          ∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
            Complex.normSq (selbergShortCollectedPairTerm N X k p) := by
  apply Finset.sum_le_sum
  intro k _hk
  exact normSq_selbergShortDirichletCollectedCoeff_le_pairFiber N X k

end HardyTheorem
