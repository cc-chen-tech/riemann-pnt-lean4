import WeilExtremalKernels.ArchimedeanRankTwoTail

/-!
# Integrated rank-two archimedean increments

This module integrates finite real matrices entrywise and proves that their
quadratic forms commute with finite-interval integration.  It then applies
that infrastructure to the paper's Cauchy rank-two density.

For a continuous nonnegative weight on `[a,b]`, with `rho * N < a`, the
integrated rank-two increment is positive semidefinite.  Its quadratic form is
bounded by the integral of the explicit pointwise vector-norm budget.

The paper's analytic weight

`pi⁻² * h₊(r) * sin²(L*r/2) / rho`

has not yet been inserted.  Consequently this module does not prove
positivity of `h₊`, the improper tail limit, the explicit constant `B_T`, the
basis transfer, or the infinite-dimensional Weil criterion.
-/

namespace WeilExtremalKernels

open MeasureTheory
open scoped BigOperators Interval

/-- Entrywise interval integration of a finite real matrix family. -/
noncomputable def intervalIntegratedMatrix {n : ℕ}
    (F : ℝ → FiniteMatrix n) (a b : ℝ) : FiniteMatrix n :=
  fun i j => ∫ r in a..b, F r i j

theorem intervalIntegrable_quadraticForm {n : ℕ}
    (F : ℝ → FiniteMatrix n) (x : FiniteVector n) {a b : ℝ}
    (hF : ∀ i j, IntervalIntegrable (fun r => F r i j) volume a b) :
    IntervalIntegrable (fun r => quadraticForm (F r) x) volume a b := by
  unfold quadraticForm
  have hsOuter :=
    IntervalIntegrable.sum Finset.univ fun i _ => by
      have hsInner :=
        IntervalIntegrable.sum Finset.univ fun j _ =>
          ((hF i j).const_mul (x i)).mul_const (x j)
      convert hsInner using 1
  convert hsOuter using 1
  ext r
  simp

/-- A finite quadratic form commutes with entrywise interval integration. -/
theorem quadraticForm_intervalIntegratedMatrix {n : ℕ}
    (F : ℝ → FiniteMatrix n) (x : FiniteVector n) {a b : ℝ}
    (hF : ∀ i j, IntervalIntegrable (fun r => F r i j) volume a b) :
    quadraticForm (intervalIntegratedMatrix F a b) x =
      ∫ r in a..b, quadraticForm (F r) x := by
  unfold quadraticForm intervalIntegratedMatrix
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul]
    · intro j _
      exact ((hF i j).const_mul (x i)).mul_const (x j)
  · intro i _
    have hs :=
      IntervalIntegrable.sum Finset.univ fun j _ =>
        ((hF i j).const_mul (x i)).mul_const (x j)
    convert hs using 1
    ext r
    simp

theorem quadraticForm_intervalIntegratedMatrix_nonneg {n : ℕ}
    (F : ℝ → FiniteMatrix n) (x : FiniteVector n) {a b : ℝ}
    (hab : a ≤ b)
    (hF : ∀ i j, IntervalIntegrable (fun r => F r i j) volume a b)
    (hpos : ∀ r ∈ Set.Icc a b, 0 ≤ quadraticForm (F r) x) :
    0 ≤ quadraticForm (intervalIntegratedMatrix F a b) x := by
  rw [quadraticForm_intervalIntegratedMatrix F x hF]
  exact intervalIntegral.integral_nonneg hab hpos

theorem continuousOn_cauchyTailPlusVector
    {n : ℕ} (coordinate : FiniteVector n) {rho radius a b : ℝ}
    (hrho : 0 < rho) (ha : rho * radius < a)
    (hcoordinate : ∀ i, |coordinate i| ≤ radius) (i : Fin n) :
    ContinuousOn (fun r =>
      cauchyTailPlusVector rho r coordinate i) (Set.Icc a b) := by
  apply ((continuousOn_id.div_const rho).sub continuousOn_const).inv₀
  intro r hr
  have hpair := cauchyTail_denominator_lower coordinate
    (rho := rho) (radius := radius) (T := r) hrho hcoordinate i
  have hlower := hpair.1
  have hbase : 0 < (r - rho * radius) / rho :=
    div_pos (sub_pos.mpr (ha.trans_le hr.1)) hrho
  simpa only [id_eq] using ne_of_gt (hbase.trans_le hlower)

theorem continuousOn_cauchyTailMinusVector
    {n : ℕ} (coordinate : FiniteVector n) {rho radius a b : ℝ}
    (hrho : 0 < rho) (ha : rho * radius < a)
    (hcoordinate : ∀ i, |coordinate i| ≤ radius) (i : Fin n) :
    ContinuousOn (fun r =>
      cauchyTailMinusVector rho r coordinate i) (Set.Icc a b) := by
  apply ((continuousOn_id.div_const rho).add continuousOn_const).inv₀
  intro r hr
  have hpair := cauchyTail_denominator_lower coordinate
    (rho := rho) (radius := radius) (T := r) hrho hcoordinate i
  have hlower := hpair.2
  have hbase : 0 < (r - rho * radius) / rho :=
    div_pos (sub_pos.mpr (ha.trans_le hr.1)) hrho
  simpa only [id_eq, Pi.add_apply] using ne_of_gt (hbase.trans_le hlower)

theorem continuousOn_paperArchimedeanRankTwoDensity_entry
    (N : ℕ) {weight : ℝ → ℝ} {rho a b : ℝ}
    (hweight : ContinuousOn weight (Set.Icc a b))
    (hrho : 0 < rho) (ha : rho * N < a)
    (i j : Fin (2 * N + 1)) :
    ContinuousOn (fun r =>
      paperArchimedeanRankTwoDensity N (weight r) rho r i j)
        (Set.Icc a b) := by
  have hpi := continuousOn_cauchyTailPlusVector
    (a := a) (b := b) (centeredIndexCoordinate N) hrho ha
      (abs_centeredIndexCoordinate_le N) i
  have hpj := continuousOn_cauchyTailPlusVector
    (a := a) (b := b) (centeredIndexCoordinate N) hrho ha
      (abs_centeredIndexCoordinate_le N) j
  have hqi := continuousOn_cauchyTailMinusVector
    (a := a) (b := b) (centeredIndexCoordinate N) hrho ha
      (abs_centeredIndexCoordinate_le N) i
  have hqj := continuousOn_cauchyTailMinusVector
    (a := a) (b := b) (centeredIndexCoordinate N) hrho ha
      (abs_centeredIndexCoordinate_le N) j
  unfold paperArchimedeanRankTwoDensity weightedRankTwoGramMatrix
    rankTwoGramMatrix rankOneGramMatrix paperCauchyPlusVector
    paperCauchyMinusVector
  exact hweight.mul ((hpi.mul hpj).add (hqi.mul hqj))

/-- The finite-interval matrix increment generated by the rank-two density. -/
noncomputable def paperArchimedeanRankTwoIncrement
    (N : ℕ) (weight : ℝ → ℝ) (rho a b : ℝ) :
    FiniteMatrix (2 * N + 1) :=
  intervalIntegratedMatrix
    (fun r => paperArchimedeanRankTwoDensity N (weight r) rho r) a b

/-- Pointwise scalar budget whose integral controls the increment operator. -/
noncomputable def paperArchimedeanRankTwoPointwiseBudget
    (N : ℕ) (weight : ℝ → ℝ) (rho r : ℝ) : ℝ :=
  weight r *
    (2 * ((2 * N + 1 : ℕ) : ℝ) * (rho / (r - rho * N)) ^ 2)

theorem continuousOn_paperArchimedeanRankTwoPointwiseBudget
    (N : ℕ) {weight : ℝ → ℝ} {rho a b : ℝ}
    (hweight : ContinuousOn weight (Set.Icc a b))
    (ha : rho * N < a) :
    ContinuousOn
      (paperArchimedeanRankTwoPointwiseBudget N weight rho)
      (Set.Icc a b) := by
  unfold paperArchimedeanRankTwoPointwiseBudget
  apply hweight.mul
  have hden :
      ContinuousOn (fun r : ℝ => r - rho * N) (Set.Icc a b) :=
    continuousOn_id.sub continuousOn_const
  have hdenNe : ∀ r ∈ Set.Icc a b, r - rho * N ≠ 0 := by
    intro r hr
    exact sub_ne_zero.mpr (ha.trans_le hr.1).ne'
  have hratio :
      ContinuousOn (fun r : ℝ => rho / (r - rho * N)) (Set.Icc a b) :=
    continuousOn_const.div₀ hden hdenNe
  exact continuousOn_const.mul (hratio.pow 2)

/-- A continuous nonnegative rank-two density integrates to a positive
semidefinite finite matrix. -/
theorem quadraticForm_paperArchimedeanRankTwoIncrement_nonneg
    (N : ℕ) {weight : ℝ → ℝ} {rho a b : ℝ}
    (hab : a ≤ b) (hweight : ContinuousOn weight (Set.Icc a b))
    (hweightNonneg : ∀ r ∈ Set.Icc a b, 0 ≤ weight r)
    (hrho : 0 < rho) (ha : rho * N < a)
    (x : FiniteVector (2 * N + 1)) :
    0 ≤ quadraticForm
      (paperArchimedeanRankTwoIncrement N weight rho a b) x := by
  apply quadraticForm_intervalIntegratedMatrix_nonneg
      (fun r => paperArchimedeanRankTwoDensity N (weight r) rho r) x hab
  · intro i j
    exact (continuousOn_paperArchimedeanRankTwoDensity_entry
      N hweight hrho ha i j).intervalIntegrable_of_Icc hab
  · intro r hr
    exact quadraticForm_paperArchimedeanRankTwoDensity_nonneg
      N (hweightNonneg r hr) x

/-- The integrated quadratic form is controlled by the integral of the
pointwise Cauchy-vector budget. -/
theorem quadraticForm_paperArchimedeanRankTwoIncrement_le
    (N : ℕ) {weight : ℝ → ℝ} {rho a b : ℝ}
    (hab : a ≤ b) (hweight : ContinuousOn weight (Set.Icc a b))
    (hweightNonneg : ∀ r ∈ Set.Icc a b, 0 ≤ weight r)
    (hrho : 0 < rho) (ha : rho * N < a)
    (x : FiniteVector (2 * N + 1)) :
    quadraticForm
        (paperArchimedeanRankTwoIncrement N weight rho a b) x ≤
      (∫ r in a..b,
        paperArchimedeanRankTwoPointwiseBudget N weight rho r) *
          squaredNorm x := by
  let F : ℝ → FiniteMatrix (2 * N + 1) :=
    fun r => paperArchimedeanRankTwoDensity N (weight r) rho r
  have hF : ∀ i j, IntervalIntegrable (fun r => F r i j) volume a b := by
    intro i j
    exact (continuousOn_paperArchimedeanRankTwoDensity_entry
      N hweight hrho ha i j).intervalIntegrable_of_Icc hab
  rw [paperArchimedeanRankTwoIncrement,
    quadraticForm_intervalIntegratedMatrix F x hF]
  calc
    (∫ r in a..b, quadraticForm (F r) x) ≤
        ∫ r in a..b,
          paperArchimedeanRankTwoPointwiseBudget N weight rho r *
            squaredNorm x := by
      apply intervalIntegral.integral_mono_on hab
        (intervalIntegrable_quadraticForm F x hF)
        ((continuousOn_paperArchimedeanRankTwoPointwiseBudget
          N hweight ha).mul continuousOn_const
          |>.intervalIntegrable_of_Icc hab)
      intro r hr
      exact quadraticForm_paperArchimedeanRankTwoDensity_le N
        (hweightNonneg r hr) hrho (ha.trans_le hr.1) x
    _ = (∫ r in a..b,
          paperArchimedeanRankTwoPointwiseBudget N weight rho r) *
            squaredNorm x := by
      rw [intervalIntegral.integral_mul_const]

end WeilExtremalKernels
