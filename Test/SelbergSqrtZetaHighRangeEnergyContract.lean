import HardyTheorem.SelbergSqrtZetaHighRangeEnergy

open Complex
open scoped BigOperators

namespace HardyTheorem

noncomputable example (N X k : ℕ) : ℝ :=
  selbergSqrtZetaShortCollectedTripleFiberEnergy N X k

example (N X k : ℕ) :
    (selbergShortDirichletTriples N X k).card ≤
      (selbergShortCompleteRangePairs X k).card :=
  card_selbergShortDirichletTriples_le_completeRangePairs N X k

example (N X k : ℕ) :
    Complex.normSq
        (selbergSqrtZetaShortDirichletCollectedCoeff N X k) ≤
      selbergSqrtZetaShortCollectedTripleFiberEnergy N X k :=
  normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber N X k

example {N X k : ℕ} (hX : 2 ≤ X)
    {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergShortDirichletTriples N X k) :
    Complex.normSq (selbergSqrtZetaShortDirichletTripleCoeff X p) ≤
      (k : ℝ)⁻¹ :=
  normSq_selbergSqrtZetaShortDirichletTripleCoeff_le_inv hX hp

example {N X k : ℕ} (hX : 2 ≤ X) :
    selbergSqrtZetaShortCollectedTripleFiberEnergy N X k ≤
      (selbergShortDirichletTriples N X k).card ^ 2 / (k : ℝ) :=
  selbergSqrtZetaShortCollectedTripleFiberEnergy_le_card_sq_div hX

example {N X k : ℕ} (hX : 2 ≤ X) :
    selbergSqrtZetaShortCollectedTripleFiberEnergy N X k ≤
      (selbergShortCompleteRangePairs X k).card ^ 2 / (k : ℝ) :=
  selbergSqrtZetaShortCollectedTripleFiberEnergy_le_completePair_card_sq_div hX

example {N X k : ℕ} (hk : 1 < k) (H : ℝ) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k) ≤
      (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        selbergSqrtZetaShortCollectedTripleFiberEnergy N X k :=
  normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber_mul_min_sq
    hk H

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          selbergSqrtZetaShortCollectedTripleFiberEnergy N X k :=
  sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_tripleFiberMin
    hN hX H

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortDirichletTriples N X k).card ^ 2 / (k : ℝ)) :=
  sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_cardSq
    hN hX H

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 / (k : ℝ)) :=
  sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_completePairCardSq
    hN hX H

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
            selbergSqrtZetaShortCollectedTripleFiberEnergy N X k :=
  sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_tripleFiberMinHighRange
    hN hX hlarge H

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
            ((selbergShortDirichletTriples N X k).card ^ 2 / (k : ℝ)) :=
  sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_cardSqHighRange
    hN hX hlarge H

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
            ((selbergShortCompleteRangePairs X k).card ^ 2 / (k : ℝ)) :=
  sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_completePairCardSqHighRange
    hN hX hlarge H

end HardyTheorem
