import WeilExtremalKernels.ArchimedeanRankTwoTail

open WeilExtremalKernels
open scoped BigOperators

example {n : ℕ} (v x : FiniteVector n) :
    quadraticForm (rankOneGramMatrix v) x =
      (∑ i, x i * v i) ^ 2 :=
  quadraticForm_rankOneGramMatrix v x

example {n : ℕ} (p q x : FiniteVector n) :
    quadraticForm (rankTwoGramMatrix p q) x =
      (∑ i, x i * p i) ^ 2 + (∑ i, x i * q i) ^ 2 :=
  quadraticForm_rankTwoGramMatrix p q x

example {n : ℕ} (p q x : FiniteVector n) :
    0 ≤ quadraticForm (rankTwoGramMatrix p q) x :=
  quadraticForm_rankTwoGramMatrix_nonneg p q x

example {n : ℕ} (p q x : FiniteVector n) :
    quadraticForm (rankTwoGramMatrix p q) x ≤
      ((∑ i, (p i) ^ 2) + ∑ i, (q i) ^ 2) * squaredNorm x :=
  quadraticForm_rankTwoGramMatrix_le p q x

example {n : ℕ} (coordinate : FiniteVector n) {rho radius T : ℝ}
    (hrho : 0 < rho) (hT : rho * radius < T)
    (hcoordinate : ∀ i, |coordinate i| ≤ radius) :
    (∑ i, (cauchyTailPlusVector rho T coordinate i) ^ 2) +
        ∑ i, (cauchyTailMinusVector rho T coordinate i) ^ 2 ≤
      2 * n * (rho / (T - rho * radius)) ^ 2 :=
  sum_sq_cauchyTailVectors_le coordinate hrho hT hcoordinate

example (N : ℕ) (i : Fin (2 * N + 1)) :
    |centeredIndexCoordinate N i| ≤ N :=
  abs_centeredIndexCoordinate_le N i

example (N : ℕ) {rho T : ℝ} (hrho : 0 < rho) (hT : rho * N < T) :
    (∑ i, (paperCauchyPlusVector N rho T i) ^ 2) +
        ∑ i, (paperCauchyMinusVector N rho T i) ^ 2 ≤
      2 * ((2 * N + 1 : ℕ) : ℝ) * (rho / (T - rho * N)) ^ 2 :=
  sum_sq_paperCauchyVectors_le N hrho hT

example (N : ℕ) {weight rho T : ℝ} (hweight : 0 ≤ weight)
    (x : FiniteVector (2 * N + 1)) :
    0 ≤ quadraticForm
      (paperArchimedeanRankTwoDensity N weight rho T) x :=
  quadraticForm_paperArchimedeanRankTwoDensity_nonneg N hweight x

example (N : ℕ) {weight rho T : ℝ}
    (hweight : 0 ≤ weight) (hrho : 0 < rho) (hT : rho * N < T)
    (x : FiniteVector (2 * N + 1)) :
    quadraticForm (paperArchimedeanRankTwoDensity N weight rho T) x ≤
      (weight *
        (2 * ((2 * N + 1 : ℕ) : ℝ) * (rho / (T - rho * N)) ^ 2)) *
        squaredNorm x :=
  quadraticForm_paperArchimedeanRankTwoDensity_le
    N hweight hrho hT x
