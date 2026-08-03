import HardyTheorem.SelbergSqrtZetaShortCollected

open Complex
open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

noncomputable example (X : ℕ) (p : ℕ × (ℕ × ℕ)) : ℂ :=
  selbergSqrtZetaShortDirichletTripleCoeff X p

noncomputable example (N X k : ℕ) : ℂ :=
  selbergSqrtZetaShortDirichletCollectedCoeff N X k

noncomputable example (X k : ℕ) : ℝ :=
  selbergSqrtZetaShortCompleteRangePairSum X k

example {N X k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X k =
      (selbergSqrtZetaShortCompleteRangePairSum X k : ℂ) *
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ :=
  selbergSqrtZetaShortDirichletCollectedCoeff_eq_pairSum hk hkN

example {X k : ℕ} (hk : 1 ≤ k) (hkX : k ≤ X) :
    selbergSqrtZetaShortCompleteRangePairSum X k =
      (((selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k) :=
  selbergSqrtZetaShortCompleteRangePairSum_eq_arithmetic hk hkX

example {N X k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X k =
      selbergSqrtZetaArithmeticDirichletCoeff X k :=
  selbergSqrtZetaShortDirichletCollectedCoeff_eq_arithmetic hk hkN hkX

example {N X k : ℕ} (hX : 1 < X) (hk : 1 < k)
    (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X k =
      selbergSqrtZetaLowRangeDirichletCoeff X k :=
  selbergSqrtZetaShortDirichletCollectedCoeff_eq_lowRange hX hk hkN hkX

example {N X : ℕ} (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (min N X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 :=
  sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_lowRange_le
    hX hlarge H

example {N X : ℕ} (hN : 1 ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          Complex.normSq
            (MathlibAux.slidingExponentialCoefficient H
              (selbergSqrtZetaShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency k) :=
  sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_highRange
    hN hX hlarge H

end HardyTheorem
