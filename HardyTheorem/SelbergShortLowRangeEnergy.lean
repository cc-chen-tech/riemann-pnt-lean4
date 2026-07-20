import HardyTheorem.SelbergShortLowRangeArithmetic
import MathlibAux.SlidingExponentialCoefficientBound
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Low-range energy of the Selberg short coefficients

On the complete divisor range the pointwise `2 / sqrt k` coefficient bound,
combined with the trivial length bound for a sliding interval, gives a fully
explicit harmonic estimate for the transformed coefficient energy.  This
isolates the genuinely difficult contribution to the truncated high range.
-/

/-- A complete-range sliding coefficient has square energy at most
`4 * H^2 / k`. -/
theorem normSq_sliding_selbergShortDirichletCollectedCoeff_le
    {N X k : ℕ} (hX : 2 ≤ X) (hk : 1 < k)
    (hkN : k ≤ N) (hkX : k ≤ X) (H : ℝ) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H
          (selbergShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k) ≤
      4 * H ^ 2 / (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsqrtpos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkpos
  have hcoeff := norm_selbergShortDirichletCollectedCoeff_le_two_div_sqrt
    hX hk hkN hkX
  have hslide := MathlibAux.norm_slidingExponentialCoefficient_le_abs_length
    H (selbergShortDirichletCollectedCoeff N X)
      selbergShortDirichletCollectedFrequency k
  have hnorm :
      ‖MathlibAux.slidingExponentialCoefficient H
          (selbergShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k‖ ≤
        2 / Real.sqrt (k : ℝ) * |H| :=
    hslide.trans (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg H))
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖MathlibAux.slidingExponentialCoefficient H
          (selbergShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k‖ ^ 2 ≤
        (2 / Real.sqrt (k : ℝ) * |H|) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
    _ = 4 * H ^ 2 / (k : ℝ) := by
      rw [mul_pow, div_pow, sq_abs, Real.sq_sqrt hkpos.le]
      ring

/-- The transformed coefficient energy on `2 <= k <= min N X` is bounded by
four times `H^2` times the corresponding harmonic sum. -/
theorem sum_normSq_sliding_selbergShortDirichletCollectedCoeff_lowRange_le_harmonic
    {N X : ℕ} (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (min N X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      4 * H ^ 2 * (harmonic (min N X) : ℝ) := by
  calc
    (∑ k ∈ Finset.Ioc 1 (min N X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
        ∑ k ∈ Finset.Ioc 1 (min N X), 4 * H ^ 2 / (k : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact normSq_sliding_selbergShortDirichletCollectedCoeff_le hX
        (Finset.mem_Ioc.mp hk).1
        ((Finset.mem_Ioc.mp hk).2.trans (min_le_left N X))
        ((Finset.mem_Ioc.mp hk).2.trans (min_le_right N X)) H
    _ = 4 * H ^ 2 * ∑ k ∈ Finset.Ioc 1 (min N X), (k : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [div_eq_mul_inv]
    _ ≤ 4 * H ^ 2 * ∑ k ∈ Finset.Icc 1 (min N X), (k : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Ioc_subset_Icc_self
        · intro k _hk _hnot
          positivity
      · positivity
    _ = 4 * H ^ 2 * (harmonic (min N X) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- A convenient logarithmic version of the low-range transformed energy
bound. -/
theorem sum_normSq_sliding_selbergShortDirichletCollectedCoeff_lowRange_le_log
    {N X : ℕ} (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (min N X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      4 * H ^ 2 * (1 + Real.log (min N X : ℝ)) := by
  exact
    (sum_normSq_sliding_selbergShortDirichletCollectedCoeff_lowRange_le_harmonic
      hX H).trans
      (mul_le_mul_of_nonneg_left
        (by simpa only [Nat.cast_min] using harmonic_le_one_add_log (min N X))
        (by positivity))

/-- The full transformed energy splits into a logarithmically controlled
complete-divisor range and one remaining truncated high range.  This is the
precise energy term that a sharp Selberg mean-square argument must still
control. -/
theorem sum_normSq_sliding_selbergShortDirichletCollectedCoeff_le_lowRange_add_highRange
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      4 * H ^ 2 * (1 + Real.log (min N X : ℝ)) +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          Complex.normSq
            (MathlibAux.slidingExponentialCoefficient H
              (selbergShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency k) := by
  have hXone : 1 ≤ X := by omega
  have hone_min : 1 ≤ min N X := Nat.le_min.mpr ⟨hN, hXone⟩
  have hmin_support : min N X ≤ N * X * X := by
    calc
      min N X ≤ N := min_le_left N X
      _ = N * 1 * 1 := by simp
      _ ≤ N * X * X := Nat.mul_le_mul (Nat.mul_le_mul_left N hXone) hXone
  have hsplit :
      Finset.Ioc 1 (min N X) ∪ Finset.Ioc (min N X) (N * X * X) =
        Finset.Ioc 1 (N * X * X) :=
    Finset.Ioc_union_Ioc_eq_Ioc hone_min hmin_support
  have hdisjoint :
      Disjoint (Finset.Ioc 1 (min N X))
        (Finset.Ioc (min N X) (N * X * X)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  rw [← hsplit, Finset.sum_union hdisjoint]
  exact add_le_add
    (sum_normSq_sliding_selbergShortDirichletCollectedCoeff_lowRange_le_log hX H)
    (le_refl _)

end HardyTheorem
