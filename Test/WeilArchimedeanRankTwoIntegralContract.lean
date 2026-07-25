import WeilExtremalKernels.ArchimedeanRankTwoIntegral

open MeasureTheory WeilExtremalKernels
open scoped Interval

example {n : ℕ} (F : ℝ → FiniteMatrix n) (x : FiniteVector n) {a b : ℝ}
    (hF : ∀ i j, IntervalIntegrable (fun r => F r i j) volume a b) :
    quadraticForm (intervalIntegratedMatrix F a b) x =
      ∫ r in a..b, quadraticForm (F r) x :=
  quadraticForm_intervalIntegratedMatrix F x hF

example {n : ℕ} (F : ℝ → FiniteMatrix n) (x : FiniteVector n) {a b : ℝ}
    (hab : a ≤ b)
    (hF : ∀ i j, IntervalIntegrable (fun r => F r i j) volume a b)
    (hpos : ∀ r ∈ Set.Icc a b, 0 ≤ quadraticForm (F r) x) :
    0 ≤ quadraticForm (intervalIntegratedMatrix F a b) x :=
  quadraticForm_intervalIntegratedMatrix_nonneg F x hab hF hpos

example (N : ℕ) {weight : ℝ → ℝ} {rho a b : ℝ}
    (hab : a ≤ b) (hweight : ContinuousOn weight (Set.Icc a b))
    (hweightNonneg : ∀ r ∈ Set.Icc a b, 0 ≤ weight r)
    (hrho : 0 < rho) (ha : rho * N < a)
    (x : FiniteVector (2 * N + 1)) :
    0 ≤ quadraticForm
      (paperArchimedeanRankTwoIncrement N weight rho a b) x :=
  quadraticForm_paperArchimedeanRankTwoIncrement_nonneg
    N hab hweight hweightNonneg hrho ha x

example (N : ℕ) {weight : ℝ → ℝ} {rho a b : ℝ}
    (hab : a ≤ b) (hweight : ContinuousOn weight (Set.Icc a b))
    (hweightNonneg : ∀ r ∈ Set.Icc a b, 0 ≤ weight r)
    (hrho : 0 < rho) (ha : rho * N < a)
    (x : FiniteVector (2 * N + 1)) :
    quadraticForm
        (paperArchimedeanRankTwoIncrement N weight rho a b) x ≤
      (∫ r in a..b,
        paperArchimedeanRankTwoPointwiseBudget N weight rho r) *
          squaredNorm x :=
  quadraticForm_paperArchimedeanRankTwoIncrement_le
    N hab hweight hweightNonneg hrho ha x
