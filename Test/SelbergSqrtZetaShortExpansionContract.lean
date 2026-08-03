import HardyTheorem.SelbergSqrtZetaShortExpansion

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

noncomputable example (X : ℕ) (s : ℂ) : ℂ :=
  selbergSqrtZetaMollifier X s

noncomputable example (X : ℕ) : ℝ :=
  selbergSqrtZetaMollifierMajorant X

noncomputable example (N X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaShortDirichletTriplePolynomial N X t

noncomputable example (N X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaShortDirichletCollectedPolynomial N X t

noncomputable example (H : ℝ) (N X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaMollifiedShortDirichletPolynomial H N X t

example
    (X : ℕ) (t : ℝ) :
    ‖selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
      selbergSqrtZetaMollifierMajorant X :=
  norm_selbergSqrtZetaMollifier_criticalLine_le_majorant X t

example
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t) =
      ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 X,
        ∑ l ∈ Finset.Icc 1 X,
          (selbergSqrtZetaTaperedCoeff X d : ℂ) *
            (selbergSqrtZetaTaperedCoeff X l : ℂ) *
            (1 / ((m * d * l : ℕ) : ℂ) ^
              ((1 / 2 : ℂ) + I * t)) :=
  criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_tripleSum N X t

example
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t) =
      selbergSqrtZetaShortDirichletTriplePolynomial N X t :=
  criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_exponentialPolynomial N X t

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, ∀ T t : ℝ,
        T0 ≤ T → t ∈ Set.Icc T (2 * T) →
          ∃ E : ℂ,
            (riemannZeta ((1 / 2 : ℂ) + I * t) *
                selbergSqrtZetaMollifier X
                  ((1 / 2 : ℂ) + I * t)) *
              selbergSqrtZetaMollifier X
                ((1 / 2 : ℂ) + I * t) =
                selbergSqrtZetaShortDirichletTriplePolynomial
                  (firstZetaApproximationCutoff T) X t + E ∧
            ‖E‖ ≤ C / Real.sqrt T *
              selbergSqrtZetaMollifierMajorant X ^ 2 := exists_selbergSqrtZetaMollifiedZetaFirstApprox

example
    (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaShortDirichletTriplePolynomial N X t =
      selbergSqrtZetaShortDirichletCollectedPolynomial N X t :=
  selbergSqrtZetaShortDirichletTriplePolynomial_eq_collectedPolynomial N X t

example
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X 1 = 1 :=
  selbergSqrtZetaShortDirichletCollectedCoeff_one hN hX

example
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (t : ℝ) :
    selbergSqrtZetaShortDirichletCollectedPolynomial N X t - 1 =
      MathlibAux.exponentialPolynomial
        (Finset.Ioc 1 (N * X * X))
        (selbergSqrtZetaShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency t :=
  selbergSqrtZetaShortDirichletCollectedPolynomial_sub_one_eq hN hX t

example
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (H t : ℝ) :
    selbergSqrtZetaMollifiedShortDirichletPolynomial H N X t =
      MathlibAux.slidingExponentialPolynomialIntegral
        (Finset.Ioc 1 (N * X * X))
        (selbergSqrtZetaShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency H t :=
  selbergSqrtZetaMollifiedShortDirichletPolynomial_eq_slidingCollected hN hX H t

example
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) {A B H : ℝ} :
    (∫ t in A..B,
        Complex.normSq
          (selbergSqrtZetaMollifiedShortDirichletPolynomial
            H N X t)) ≤
      ∑ m ∈ Finset.Ioc 1 (N * X * X),
        ∑ n ∈ Finset.Ioc 1 (N * X * X),
          if m = n then
            (B - A) * Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency n)
          else
            2 * ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency m‖ *
                ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency n‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n| :=
  integral_normSq_selbergSqrtZetaMollifiedShortDirichletPolynomial_le_gapSum hN hX

end HardyTheorem
