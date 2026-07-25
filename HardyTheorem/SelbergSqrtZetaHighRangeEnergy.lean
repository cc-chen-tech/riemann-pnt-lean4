import HardyTheorem.SelbergSqrtZetaShortCollected
import MathlibAux.FiberwiseNormSq
import MathlibAux.SlidingExponentialCoefficientBound

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# High-range energy of the square-root-zeta short coefficients

The unresolved collected coefficient at product `k` is kept as its actual
finite triple fiber.  Finite Cauchy--Schwarz and the oscillatory interval
transform reduce the high range to a logarithmically weighted arithmetic
fiber energy.
-/

/-- The finite square mass retained inside the actual triple-product fiber
at `k`. -/
noncomputable def selbergSqrtZetaShortCollectedTripleFiberEnergy
    (N X k : ℕ) : ℝ :=
  (selbergShortDirichletTriples N X k).card *
    ∑ p ∈ selbergShortDirichletTriples N X k,
      Complex.normSq (selbergSqrtZetaShortDirichletTripleCoeff X p)

/-- Fiberwise finite Cauchy--Schwarz for one collected square-root-zeta
coefficient. -/
theorem normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber
    (N X k : ℕ) :
    Complex.normSq
        (selbergSqrtZetaShortDirichletCollectedCoeff N X k) ≤
      selbergSqrtZetaShortCollectedTripleFiberEnergy N X k := by
  unfold selbergSqrtZetaShortDirichletCollectedCoeff
  unfold selbergSqrtZetaShortCollectedTripleFiberEnergy
  exact MathlibAux.normSq_finset_sum_le_card_mul_sum_normSq
    (selbergShortDirichletTriples N X k)
    (selbergSqrtZetaShortDirichletTripleCoeff X)

/-- The strongest pointwise interval-transform envelope for a nonconstant
collected mode. -/
theorem normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber_mul_min_sq
    {N X k : ℕ} (hk : 1 < k) (H : ℝ) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k) ≤
      (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        selbergSqrtZetaShortCollectedTripleFiberEnergy N X k := by
  have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkReal
  have hfreq : selbergShortDirichletCollectedFrequency k ≠ 0 := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log]
    exact neg_ne_zero.mpr hlog.ne'
  have hfreqAbs :
      |selbergShortDirichletCollectedFrequency k| =
        Real.log (k : ℝ) := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log, abs_neg,
      abs_of_pos hlog]
  have hslide := MathlibAux.norm_slidingExponentialCoefficient_le_min
    (selbergSqrtZetaShortDirichletCollectedCoeff N X)
    selbergShortDirichletCollectedFrequency k hfreq (H := H)
  rw [hfreqAbs] at hslide
  have hcoeff :=
    normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber
      N X k
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖MathlibAux.slidingExponentialCoefficient H
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k‖ ^ 2 ≤
        (‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ *
          min |H| (2 / Real.log (k : ℝ))) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hslide
    _ = (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
      rw [Complex.normSq_eq_norm_sq]
      ring
    _ ≤ (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        selbergSqrtZetaShortCollectedTripleFiberEnergy N X k :=
      mul_le_mul_of_nonneg_left hcoeff (sq_nonneg _)

/-- The transformed high-range energy is bounded by the corresponding
minimum-envelope triple-fiber sum. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_tripleFiberMin
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          selbergSqrtZetaShortCollectedTripleFiberEnergy N X k := by
  apply Finset.sum_le_sum
  intro k hk
  have honeMin : 1 ≤ min N X :=
    Nat.le_min.mpr ⟨hN, by omega⟩
  exact
    normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber_mul_min_sq
      (honeMin.trans_lt (Finset.mem_Ioc.mp hk).1) H

/-- The full transformed energy is the proved constant low range plus one
explicit minimum-envelope triple-fiber high-range sum. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_tripleFiberMinHighRange
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
            selbergSqrtZetaShortCollectedTripleFiberEnergy N X k := by
  exact
    (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_highRange
      hN (by omega) hlarge H).trans
      (add_le_add (le_refl _)
        (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_tripleFiberMin
          hN hX H))

end HardyTheorem
