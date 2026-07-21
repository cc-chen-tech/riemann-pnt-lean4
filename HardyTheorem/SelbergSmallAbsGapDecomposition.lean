import HardyTheorem.SelbergSmallAbsGapBound
import HardyTheorem.SelbergShortHighRangeEnergy
import MathlibAux.SlidingExponentialCoefficientBound

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Diagonal/off-diagonal decomposition of the Selberg short gap sum

The finite frequency-gap sum `selbergShortDirichletGapSum` splits into a
diagonal part, which is the interval length times the transformed coefficient
energy, and an off-diagonal frequency-spacing part.  The sliding coefficient
envelope `min |H| (2 / |lambda|)` turns the off-diagonal part into the
classical Selberg bilinear form

```
H^2 * sum_{m, n} 2 |c_m| |c_n| / |log m - log n| .
```

Together with the proved low-range/hybrid energy bounds this isolates the two
remaining analytic inputs needed for the `T / 24` small-absolute-mass bound:

* the high-range fiber energy
  `sum_k (min |H| (2 / log k))^2 * selbergShortCollectedPairFiberEnergy N X k`,
* the off-diagonal bilinear form above.
-/

/-- The gap sum splits into the proved diagonal energy expression and the
classical off-diagonal Selberg bilinear form with coefficient envelope `H^2`. -/
theorem selbergShortDirichletGapSum_le_diagonal_add_offDiagonal
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) {A B H : ℝ} (hAB : A ≤ B) :
    selbergShortDirichletGapSum N X A B H ≤
      (B - A) * (4 * H ^ 2 * (1 + Real.log (min N X : ℝ)) +
          ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
            (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
              selbergShortCollectedPairFiberEnergy N X k) +
        H ^ 2 * ∑ m ∈ Finset.Ioc 1 (N * X * X),
          ∑ n ∈ Finset.Ioc 1 (N * X * X),
            2 * ‖selbergShortDirichletCollectedCoeff N X m‖ *
              ‖selbergShortDirichletCollectedCoeff N X n‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n| := by
  classical
  have hoff : ∀ m n : ℕ,
      2 * ‖MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency m‖ *
          ‖MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency n‖ /
        |selbergShortDirichletCollectedFrequency m -
          selbergShortDirichletCollectedFrequency n| ≤
        H ^ 2 * (2 * ‖selbergShortDirichletCollectedCoeff N X m‖ *
            ‖selbergShortDirichletCollectedCoeff N X n‖ /
          |selbergShortDirichletCollectedFrequency m -
            selbergShortDirichletCollectedFrequency n|) := by
    intro m n
    by_cases hz : |selbergShortDirichletCollectedFrequency m -
        selbergShortDirichletCollectedFrequency n| = 0
    · rw [hz]
      simp
    · have hpos : 0 < |selbergShortDirichletCollectedFrequency m -
          selbergShortDirichletCollectedFrequency n| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
      have h1 := MathlibAux.norm_slidingExponentialCoefficient_le_abs_length H
        (selbergShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency m
      have h2 := MathlibAux.norm_slidingExponentialCoefficient_le_abs_length H
        (selbergShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency n
      have hnum :
          2 * (‖MathlibAux.slidingExponentialCoefficient H
                (selbergShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency m‖ *
              ‖MathlibAux.slidingExponentialCoefficient H
                (selbergShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency n‖) ≤
            2 * ((‖selbergShortDirichletCollectedCoeff N X m‖ * |H|) *
              (‖selbergShortDirichletCollectedCoeff N X n‖ * |H|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (abs_nonneg _)))
          (by norm_num)
      calc
        2 * ‖MathlibAux.slidingExponentialCoefficient H
              (selbergShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency m‖ *
            ‖MathlibAux.slidingExponentialCoefficient H
              (selbergShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency n‖ /
          |selbergShortDirichletCollectedFrequency m -
            selbergShortDirichletCollectedFrequency n|
          = (2 * (‖MathlibAux.slidingExponentialCoefficient H
                (selbergShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency m‖ *
              ‖MathlibAux.slidingExponentialCoefficient H
                (selbergShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency n‖)) /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n| := by ring
        _ ≤ (2 * ((‖selbergShortDirichletCollectedCoeff N X m‖ * |H|) *
              (‖selbergShortDirichletCollectedCoeff N X n‖ * |H|))) /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n| := by
          rw [div_le_iff₀ hpos, div_mul_cancel₀ _ hz]
          exact hnum
        _ = H ^ 2 * (2 * ‖selbergShortDirichletCollectedCoeff N X m‖ *
              ‖selbergShortDirichletCollectedCoeff N X n‖ /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n|) := by
          have hH2 :
              (2 : ℝ) * ((‖selbergShortDirichletCollectedCoeff N X m‖ * |H|) *
                  (‖selbergShortDirichletCollectedCoeff N X n‖ * |H|)) =
                H ^ 2 * (2 * ‖selbergShortDirichletCollectedCoeff N X m‖ *
                  ‖selbergShortDirichletCollectedCoeff N X n‖) := by
            rw [show (H : ℝ) ^ 2 = |H| ^ 2 by rw [sq_abs]]
            ring
          rw [← mul_div_assoc, hH2]
  have hinner : ∀ m ∈ Finset.Ioc 1 (N * X * X),
      (∑ n ∈ Finset.Ioc 1 (N * X * X),
          if m = n then
            (B - A) * Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency n)
          else
            2 * ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency m‖ *
                ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency n‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n|) =
        (B - A) * Complex.normSq
            (MathlibAux.slidingExponentialCoefficient H
              (selbergShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency m) +
          ∑ n ∈ Finset.Ioc 1 (N * X * X),
            2 * ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency m‖ *
                ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency n‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n| := by
    intro m hm
    have hpt : ∀ n ∈ Finset.Ioc 1 (N * X * X),
        (if m = n then
            (B - A) * Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency n)
          else
            2 * ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency m‖ *
                ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency n‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n|) =
          (if m = n then
              (B - A) * Complex.normSq
                (MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency n)
            else 0) +
            2 * ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency m‖ *
                ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency n‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n| := by
      intro n _hn
      by_cases h : m = n
      · subst h
        have hz : 2 * ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency m‖ *
                ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency m‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency m| = 0 := by
          rw [sub_self, abs_zero, div_zero]
        rw [if_pos rfl, if_pos rfl, hz, add_zero]
      · rw [if_neg h, if_neg h, zero_add]
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq,
      if_pos hm]
  have hsplit :
      selbergShortDirichletGapSum N X A B H =
        (B - A) * (∑ k ∈ Finset.Ioc 1 (N * X * X),
            Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency k)) +
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ∑ n ∈ Finset.Ioc 1 (N * X * X),
              2 * ‖MathlibAux.slidingExponentialCoefficient H
                    (selbergShortDirichletCollectedCoeff N X)
                    selbergShortDirichletCollectedFrequency m‖ *
                  ‖MathlibAux.slidingExponentialCoefficient H
                    (selbergShortDirichletCollectedCoeff N X)
                    selbergShortDirichletCollectedFrequency n‖ /
                |selbergShortDirichletCollectedFrequency m -
                  selbergShortDirichletCollectedFrequency n| := by
    unfold selbergShortDirichletGapSum
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.mul_sum]
  rw [hsplit]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (sum_normSq_sliding_selbergShortDirichletCollectedCoeff_le_lowRange_add_pairFiberMinHighRange
        hN hX H)
      (sub_nonneg.mpr hAB)
  · calc
      ∑ m ∈ Finset.Ioc 1 (N * X * X),
          ∑ n ∈ Finset.Ioc 1 (N * X * X),
            2 * ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency m‖ *
                ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency n‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n|
        ≤ ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ∑ n ∈ Finset.Ioc 1 (N * X * X),
              H ^ 2 * (2 * ‖selbergShortDirichletCollectedCoeff N X m‖ *
                  ‖selbergShortDirichletCollectedCoeff N X n‖ /
                |selbergShortDirichletCollectedFrequency m -
                  selbergShortDirichletCollectedFrequency n|) := by
          apply Finset.sum_le_sum
          intro m _hm
          apply Finset.sum_le_sum
          intro n _hn
          exact hoff m n
      _ = H ^ 2 * ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ∑ n ∈ Finset.Ioc 1 (N * X * X),
              2 * ‖selbergShortDirichletCollectedCoeff N X m‖ *
                ‖selbergShortDirichletCollectedCoeff N X n‖ /
                |selbergShortDirichletCollectedFrequency m -
                  selbergShortDirichletCollectedFrequency n| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _hm
          rw [Finset.mul_sum]

end HardyTheorem
