import WeilExtremalKernels.ArchimedeanTailTransfer

open WeilExtremalKernels

example {n : ℕ} (A H : FiniteMatrix n) (x : FiniteVector n) :
    quadraticForm (A + H) x = quadraticForm A x + quadraticForm H x :=
  quadraticForm_add A H x

example {n : ℕ} (A H : FiniteMatrix n)
    (hA : ∀ x, 0 ≤ quadraticForm A x)
    (hH : ∀ x, 0 ≤ quadraticForm H x) :
    ∀ x, 0 ≤ quadraticForm (A + H) x :=
  quadraticForm_nonneg_add_of_tail_nonneg A H hA hH

example {n : ℕ} (A H : FiniteMatrix n)
    (hA : ∀ x, x ≠ 0 → 0 < quadraticForm A x)
    (hH : ∀ x, 0 ≤ quadraticForm H x) :
    ∀ x, x ≠ 0 → 0 < quadraticForm (A + H) x :=
  quadraticForm_pos_add_of_tail_nonneg A H hA hH

example {n : ℕ} (A H : FiniteMatrix n) (x : FiniteVector n) (B : ℝ)
    (hfinite : quadraticForm A x < -B * squaredNorm x)
    (htail : quadraticForm H x ≤ B * squaredNorm x) :
    quadraticForm (A + H) x < 0 :=
  quadraticForm_neg_add_of_tail_upper A H x B hfinite htail

example {n : ℕ} (A C R : FiniteMatrix n) (x : FiniteVector n) (μ ρ : ℝ)
    (hcenter : ∀ y, μ * squaredNorm y ≤ quadraticForm C y)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) :
    (μ - ρ) * squaredNorm x ≤ quadraticForm A x :=
  quadraticForm_lower_of_interval A C R x μ ρ hcenter hR hentry hrow

example {n : ℕ} (A C R H : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ)
    (hbudget : ρ ≤ μ)
    (htail : ∀ x, 0 ≤ quadraticForm H x) :
    ∀ x, 0 ≤ quadraticForm (A + H) x :=
  quadraticForm_nonneg_of_interval_and_tail
    A C R H μ ρ hcenter hR hentry hrow hbudget htail

example {n : ℕ} (A C R H : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ)
    (hbudget : ρ < μ)
    (htail : ∀ x, 0 ≤ quadraticForm H x) :
    ∀ x, x ≠ 0 → 0 < quadraticForm (A + H) x :=
  quadraticForm_pos_of_interval_and_tail
    A C R H μ ρ hcenter hR hentry hrow hbudget htail

example {n : ℕ} (A C R H E : FiniteMatrix n) (μ ρ σ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ)
    (htail : ∀ x, 0 ≤ quadraticForm H x)
    (htransfer : ∀ x, |quadraticForm E x| ≤ σ * squaredNorm x)
    (hbudget : ρ + σ ≤ μ) :
    ∀ x, 0 ≤ quadraticForm (A + H + E) x :=
  quadraticForm_nonneg_of_interval_tail_and_transfer_error
    A C R H E μ ρ σ hcenter hR hentry hrow htail htransfer hbudget
