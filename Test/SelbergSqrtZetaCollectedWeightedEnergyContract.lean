import HardyTheorem.SelbergSqrtZetaCollectedWeightedEnergy

open Complex
open scoped BigOperators

namespace HardyTheorem

example (N X k : ℕ) :
    (selbergShortDirichletTriples N X k).card ≤ X ^ 2 :=
  card_selbergShortDirichletTriples_le_sq N X k

example {N X k : ℕ} (hX : 2 ≤ X) (hk : 1 ≤ k) :
    (k : ℝ) *
        ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ ^ 2 ≤
      (((X ^ 2 : ℕ) : ℝ)) ^ 2 :=
  mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_sq_sq hX hk

example {N X : ℕ} (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        (k : ℝ) *
          ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ ^ 2) ≤
      ((N * X * X : ℕ) : ℝ) * (((X ^ 2 : ℕ) : ℝ)) ^ 2 :=
  sum_mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_mul_sq_sq hX

example {N X : ℕ} (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        (k : ℝ) *
          ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ ^ 2) ≤
      (N : ℝ) * (X : ℝ) ^ 6 :=
  sum_mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_mul_pow_six hX

end HardyTheorem
