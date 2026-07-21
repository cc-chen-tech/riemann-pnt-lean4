import HardyTheorem.SelbergShortLowRangeEnergy
import HardyTheorem.SelbergShortCollectedEnergy

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# High-range energy of the Selberg short coefficients

For every nonconstant collected mode, the sliding interval contributes the
oscillatory factor `2 / log k`.  Combining this with the fiberwise finite
Cauchy--Schwarz estimate retains the arithmetic square mass inside each
multiplicative fiber.  Thus the unresolved high range is reduced to a
logarithmically weighted fiber energy, without replacing the fiber by a
global divisor-count majorant.
-/

/-- The square mass retained by finite Cauchy--Schwarz in the product fiber
at `k`. -/
noncomputable def selbergShortCollectedPairFiberEnergy
    (N X k : ℕ) : ℝ :=
  (selbergMollifiedDirichletPairs (N * X) X k).card *
    ∑ p ∈ selbergMollifiedDirichletPairs (N * X) X k,
      Complex.normSq (selbergShortCollectedPairTerm N X k p)

/-- The strongest available pointwise envelope combines the trivial interval
length and oscillatory reciprocal-frequency bounds before applying the
fiberwise energy estimate. -/
theorem normSq_sliding_selbergShortDirichletCollectedCoeff_le_pairFiber_mul_min_sq
    {N X k : ℕ} (hk : 1 < k) (H : ℝ) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H
          (selbergShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k) ≤
      (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        selbergShortCollectedPairFiberEnergy N X k := by
  have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkReal
  have hfreq : selbergShortDirichletCollectedFrequency k ≠ 0 := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log]
    exact neg_ne_zero.mpr hlog.ne'
  have hfreqAbs :
      |selbergShortDirichletCollectedFrequency k| = Real.log (k : ℝ) := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log, abs_neg,
      abs_of_pos hlog]
  have hslide := MathlibAux.norm_slidingExponentialCoefficient_le_min
    (selbergShortDirichletCollectedCoeff N X)
    selbergShortDirichletCollectedFrequency k hfreq (H := H)
  rw [hfreqAbs] at hslide
  have hcoeff :
      Complex.normSq (selbergShortDirichletCollectedCoeff N X k) ≤
        selbergShortCollectedPairFiberEnergy N X k := by
    exact normSq_selbergShortDirichletCollectedCoeff_le_pairFiber N X k
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖MathlibAux.slidingExponentialCoefficient H
          (selbergShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k‖ ^ 2 ≤
        (‖selbergShortDirichletCollectedCoeff N X k‖ *
          min |H| (2 / Real.log (k : ℝ))) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hslide
    _ = (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k) := by
      rw [Complex.normSq_eq_norm_sq]
      ring
    _ ≤ (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        selbergShortCollectedPairFiberEnergy N X k :=
      mul_le_mul_of_nonneg_left hcoeff (sq_nonneg _)

/-- The oscillatory interval transform turns the square energy of one
nonconstant collected coefficient into its fiber energy with weight
`4 / log(k)^2`. -/
theorem normSq_sliding_selbergShortDirichletCollectedCoeff_le_pairFiber_div_log
    {N X k : ℕ} (hk : 1 < k) (H : ℝ) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H
          (selbergShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k) ≤
      (4 / Real.log (k : ℝ) ^ 2) *
        selbergShortCollectedPairFiberEnergy N X k := by
  have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkReal
  have hfreq : selbergShortDirichletCollectedFrequency k ≠ 0 := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log]
    exact neg_ne_zero.mpr hlog.ne'
  have hfreqAbs :
      |selbergShortDirichletCollectedFrequency k| = Real.log (k : ℝ) := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log, abs_neg,
      abs_of_pos hlog]
  have hslide :=
    MathlibAux.norm_slidingExponentialCoefficient_le_two_div_abs
      (selbergShortDirichletCollectedCoeff N X)
      selbergShortDirichletCollectedFrequency k hfreq (H := H)
  rw [hfreqAbs] at hslide
  have hcoeff :
      Complex.normSq (selbergShortDirichletCollectedCoeff N X k) ≤
        selbergShortCollectedPairFiberEnergy N X k := by
    exact normSq_selbergShortDirichletCollectedCoeff_le_pairFiber N X k
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖MathlibAux.slidingExponentialCoefficient H
          (selbergShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k‖ ^ 2 ≤
        (‖selbergShortDirichletCollectedCoeff N X k‖ *
          (2 / Real.log (k : ℝ))) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hslide
    _ = (4 / Real.log (k : ℝ) ^ 2) *
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k) := by
      rw [Complex.normSq_eq_norm_sq, div_eq_mul_inv]
      ring
    _ ≤ (4 / Real.log (k : ℝ) ^ 2) *
        selbergShortCollectedPairFiberEnergy N X k :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)

/-- The transformed high-range energy is bounded by the corresponding
logarithmically weighted multiplicative-fiber energy. -/
theorem sum_normSq_sliding_selbergShortDirichletCollectedCoeff_highRange_le_pairFiber_div_log
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (4 / Real.log (k : ℝ) ^ 2) *
          selbergShortCollectedPairFiberEnergy N X k := by
  apply Finset.sum_le_sum
  intro k hk
  have hone_min : 1 ≤ min N X :=
    Nat.le_min.mpr ⟨hN, by omega⟩
  exact
    normSq_sliding_selbergShortDirichletCollectedCoeff_le_pairFiber_div_log
      (hone_min.trans_lt (Finset.mem_Ioc.mp hk).1) H

/-- Summing the strongest pointwise envelope preserves the minimum of the
length and oscillatory bounds throughout the high range. -/
theorem sum_normSq_sliding_selbergShortDirichletCollectedCoeff_highRange_le_pairFiber_mul_min_sq
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          selbergShortCollectedPairFiberEnergy N X k := by
  apply Finset.sum_le_sum
  intro k hk
  have hone_min : 1 ≤ min N X :=
    Nat.le_min.mpr ⟨hN, by omega⟩
  exact
    normSq_sliding_selbergShortDirichletCollectedCoeff_le_pairFiber_mul_min_sq
      (hone_min.trans_lt (Finset.mem_Ioc.mp hk).1) H

/-- The complete transformed energy is the proved logarithmic low range plus
one explicit logarithmically weighted high-range fiber sum. -/
theorem sum_normSq_sliding_selbergShortDirichletCollectedCoeff_le_lowRange_add_pairFiberHighRange
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      4 * H ^ 2 * (1 + Real.log (min N X : ℝ)) +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          (4 / Real.log (k : ℝ) ^ 2) *
            selbergShortCollectedPairFiberEnergy N X k := by
  exact
    (sum_normSq_sliding_selbergShortDirichletCollectedCoeff_le_lowRange_add_highRange
      hN hX H).trans
      (add_le_add (le_refl _)
        (sum_normSq_sliding_selbergShortDirichletCollectedCoeff_highRange_le_pairFiber_div_log
          hN hX H))

/-- The strongest complete-range reduction uses the harmonic low-range bound
and the minimum interval-transform envelope on the unresolved high range. -/
theorem sum_normSq_sliding_selbergShortDirichletCollectedCoeff_le_lowRange_add_pairFiberMinHighRange
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      4 * H ^ 2 * (1 + Real.log (min N X : ℝ)) +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
            selbergShortCollectedPairFiberEnergy N X k := by
  exact
    (sum_normSq_sliding_selbergShortDirichletCollectedCoeff_le_lowRange_add_highRange
      hN hX H).trans
      (add_le_add (le_refl _)
        (sum_normSq_sliding_selbergShortDirichletCollectedCoeff_highRange_le_pairFiber_mul_min_sq
          hN hX H))

end HardyTheorem
