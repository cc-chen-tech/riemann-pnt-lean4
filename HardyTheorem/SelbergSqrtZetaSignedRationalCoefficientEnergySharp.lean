import HardyTheorem.SelbergSqrtZetaSignedDenominatorCollected

/-!
# Exact arithmetic energy of the rationally collected signed Selberg model

The generic fiberwise Cauchy--Schwarz estimate loses the cardinality of every
raw triple fiber.  Here the two denominator variables are collected first.
The remaining coefficient is real, and its full square energy is rewritten
exactly as a multiplicative correlation of denominator--numerator pairs.

The equality condition is the integer relation `l * k' = l' * k`; no fiber
cardinality or absolute value is introduced.  Thus the unresolved estimate is
isolated as a genuine off-diagonal arithmetic correlation rather than hidden
inside a coarse collision count.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The real coefficient attached to one collected denominator--numerator
pair `(k,l)`. -/
noncomputable def selbergSqrtZetaSignedRationalPairCoeff
    (N X : ℕ) (p : ℕ × ℕ) : ℝ :=
  (selbergSqrtZetaSignedDenominatorCollectedCoeff N X p.1).re *
    (selbergSqrtZetaSignedNumeratorCoeff X p.2).re

private theorem selbergSqrtZetaSignedDenominatorCollectedCoeff_im
    (N X k : ℕ) :
    (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k).im = 0 := by
  classical
  unfold selbergSqrtZetaSignedDenominatorCollectedCoeff
    selbergSqrtZetaSignedDenominatorCoeff
  simp

private theorem selbergSqrtZetaSignedNumeratorCoeff_im
    (X l : ℕ) :
    (selbergSqrtZetaSignedNumeratorCoeff X l).im = 0 := by
  unfold selbergSqrtZetaSignedNumeratorCoeff
  simp

private theorem
    selbergSqrtZetaSignedDenominatorCollected_mul_numerator_eq_ofReal
    (N X : ℕ) (p : ℕ × ℕ) :
    selbergSqrtZetaSignedDenominatorCollectedCoeff N X p.1 *
        selbergSqrtZetaSignedNumeratorCoeff X p.2 =
      (selbergSqrtZetaSignedRationalPairCoeff N X p : ℂ) := by
  apply Complex.ext
  · simp [selbergSqrtZetaSignedRationalPairCoeff,
      selbergSqrtZetaSignedDenominatorCollectedCoeff_im,
      selbergSqrtZetaSignedNumeratorCoeff_im]
  · simp [selbergSqrtZetaSignedDenominatorCollectedCoeff_im,
      selbergSqrtZetaSignedNumeratorCoeff_im]

/-- The real part of a rationally collected coefficient is the exact real
sum over the already-collected denominator--numerator fiber. -/
theorem selbergSqrtZetaSignedRationalCoeff_re_eq_pairSum
    (N X : ℕ) (q : ℚ) :
    (selbergSqrtZetaSignedRationalCoeff N X q).re =
      ∑ p ∈ selbergSqrtZetaSignedDenominatorNumeratorFiber N X q,
        selbergSqrtZetaSignedRationalPairCoeff N X p := by
  rw [selbergSqrtZetaSignedRationalCoeff_eq_denominatorCollected]
  simp_rw [
    selbergSqrtZetaSignedDenominatorCollected_mul_numerator_eq_ofReal]
  simp

private theorem selbergSqrtZetaSignedRationalCoeff_im
    (N X : ℕ) (q : ℚ) :
    (selbergSqrtZetaSignedRationalCoeff N X q).im = 0 := by
  rw [selbergSqrtZetaSignedRationalCoeff_eq_denominatorCollected]
  simp_rw [
    selbergSqrtZetaSignedDenominatorCollected_mul_numerator_eq_ofReal]
  simp

private theorem normSq_selbergSqrtZetaSignedRationalCoeff_eq_sq_pairSum
    (N X : ℕ) (q : ℚ) :
    Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) =
      (∑ p ∈ selbergSqrtZetaSignedDenominatorNumeratorFiber N X q,
        selbergSqrtZetaSignedRationalPairCoeff N X p) ^ 2 := by
  rw [Complex.normSq_apply,
    selbergSqrtZetaSignedRationalCoeff_re_eq_pairSum,
    selbergSqrtZetaSignedRationalCoeff_im]
  ring

private theorem
    selbergSqrtZetaSignedDenominatorNumeratorKey_mem_rationalSupport
    {N X : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X) :
    selbergSqrtZetaSignedDenominatorNumeratorKey p ∈
      selbergSqrtZetaSignedRationalSupport N X := by
  rcases Finset.mem_product.mp hp with ⟨hk, hl⟩
  rcases Finset.mem_image.mp hk with ⟨md, hmd, hmdk⟩
  rcases Finset.mem_product.mp hmd with ⟨hm, hd⟩
  apply Finset.mem_image.mpr
  refine ⟨(md.1, md.2, p.2), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨hm, Finset.mem_product.mpr ⟨hd, hl⟩⟩
  · unfold selbergSqrtZetaSignedDenominatorKey at hmdk
    simpa only [selbergSqrtZetaSignedDenominatorNumeratorKey,
      selbergSqrtZetaSignedRationalKey] using
      congrArg (fun k : ℕ => (p.2 : ℚ) / (k : ℚ)) hmdk

private theorem
    selbergSqrtZetaSignedDenominatorNumeratorKey_eq_iff_crossProduct
    {N X : ℕ} {p r : ℕ × ℕ}
    (hp : p ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X) :
    selbergSqrtZetaSignedDenominatorNumeratorKey p =
        selbergSqrtZetaSignedDenominatorNumeratorKey r ↔
      p.2 * r.1 = r.2 * p.1 := by
  have hp1 : 0 < p.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hp).1
  have hr1 : 0 < r.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hr).1
  unfold selbergSqrtZetaSignedDenominatorNumeratorKey
  rw [div_eq_div_iff]
  · norm_cast
  · exact_mod_cast hp1.ne'
  · exact_mod_cast hr1.ne'

/-- The exact rational coefficient energy is the multiplicative correlation
of the denominator--numerator coefficients.  Equal rational keys have become
the integer equation `l * k' = l' * k`; unlike the previous bound, this
identity has no fiber-cardinality loss. -/
theorem sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_crossProduct
    (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) =
      ∑ p ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X,
        ∑ r ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X,
          if p.2 * r.1 = r.2 * p.1 then
            selbergSqrtZetaSignedRationalPairCoeff N X p *
              selbergSqrtZetaSignedRationalPairCoeff N X r
          else 0 := by
  classical
  let S := selbergSqrtZetaSignedDenominatorNumeratorSupport N X
  let Q := selbergSqrtZetaSignedRationalSupport N X
  let key := selbergSqrtZetaSignedDenominatorNumeratorKey
  let coeff := selbergSqrtZetaSignedRationalPairCoeff N X
  have hmaps : ∀ p ∈ S, key p ∈ Q := by
    intro p hp
    exact
      selbergSqrtZetaSignedDenominatorNumeratorKey_mem_rationalSupport hp
  calc
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) =
        ∑ q ∈ Q,
          (∑ p ∈ S.filter (fun p => key p = q), coeff p) ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      simpa only [S, Q, key, coeff,
        selbergSqrtZetaSignedDenominatorNumeratorFiber] using
        normSq_selbergSqrtZetaSignedRationalCoeff_eq_sq_pairSum N X q
    _ = ∑ q ∈ Q,
        ∑ p ∈ S.filter (fun p => key p = q),
          ∑ r ∈ S.filter (fun r => key r = q),
            coeff p * coeff r := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    _ = ∑ q ∈ Q,
        ∑ p ∈ S.filter (fun p => key p = q),
          ∑ r ∈ S.filter (fun r => key r = key p),
            coeff p * coeff r := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      have hpkey : key p = q := (Finset.mem_filter.mp hp).2
      rw [hpkey]
    _ = ∑ p ∈ S,
        ∑ r ∈ S.filter (fun r => key r = key p),
          coeff p * coeff r := by
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun p => ∑ r ∈ S.filter (fun r => key r = key p),
          coeff p * coeff r)
    _ = ∑ p ∈ S, ∑ r ∈ S,
        if key r = key p then coeff p * coeff r else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_filter]
    _ = ∑ p ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X,
        ∑ r ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X,
          if p.2 * r.1 = r.2 * p.1 then
            selbergSqrtZetaSignedRationalPairCoeff N X p *
              selbergSqrtZetaSignedRationalPairCoeff N X r
          else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro r hr
      have hiff :
          key r = key p ↔ p.2 * r.1 = r.2 * p.1 := by
        simpa only [key, eq_comm] using
          (selbergSqrtZetaSignedDenominatorNumeratorKey_eq_iff_crossProduct
            hr hp)
      by_cases hcross : p.2 * r.1 = r.2 * p.1
      · have hkey : key r = key p := hiff.mpr hcross
        simp only [hkey, hcross, if_true, coeff]
      · have hkey : key r ≠ key p := fun h => hcross (hiff.mp h)
        simp only [hkey, hcross, if_false]

/-- The genuine diagonal part of the multiplicative correlation factors
exactly into the denominator energy and numerator energy.  Hence only the
nontrivial solutions of `l * k' = l' * k` remain to be estimated. -/
theorem sum_normSq_selbergSqrtZetaSignedRationalPairCoeff_eq_product
    (N X : ℕ) :
    (∑ p ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X,
        (selbergSqrtZetaSignedRationalPairCoeff N X p) ^ 2) =
      (∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k)) *
        ∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
          Complex.normSq (selbergSqrtZetaSignedNumeratorCoeff X l) := by
  classical
  calc
    (∑ p ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X,
        (selbergSqrtZetaSignedRationalPairCoeff N X p) ^ 2) =
        ∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
          ∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
            (selbergSqrtZetaSignedRationalPairCoeff N X (k, l)) ^ 2 := by
      unfold selbergSqrtZetaSignedDenominatorNumeratorSupport
      exact Finset.sum_product _ _ _
    _ = ∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
          ∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
            (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k).re ^ 2 *
              (selbergSqrtZetaSignedNumeratorCoeff X l).re ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      simp only [selbergSqrtZetaSignedRationalPairCoeff]
      ring
    _ = ∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
        (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k).re ^ 2 *
          ∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
            (selbergSqrtZetaSignedNumeratorCoeff X l).re ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    _ = (∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
        (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k).re ^ 2) *
          ∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
            (selbergSqrtZetaSignedNumeratorCoeff X l).re ^ 2 := by
      rw [Finset.sum_mul]
    _ = (∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k)) *
        ∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
          Complex.normSq (selbergSqrtZetaSignedNumeratorCoeff X l) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [Complex.normSq_apply,
          selbergSqrtZetaSignedDenominatorCollectedCoeff_im]
        ring
      · apply Finset.sum_congr rfl
        intro l hl
        rw [Complex.normSq_apply,
          selbergSqrtZetaSignedNumeratorCoeff_im]
        ring

/-- The nontrivial multiplicative correlations left after removing the
genuine pairwise diagonal.  This is the only part of the exact coefficient
energy which is not a product of two one-variable square energies. -/
noncomputable def
    selbergSqrtZetaSignedRationalCoefficientOffDiagonal
    (N X : ℕ) : ℝ :=
  ∑ p ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X,
    ∑ r ∈
        (selbergSqrtZetaSignedDenominatorNumeratorSupport N X).erase p,
      if p.2 * r.1 = r.2 * p.1 then
        selbergSqrtZetaSignedRationalPairCoeff N X p *
          selbergSqrtZetaSignedRationalPairCoeff N X r
      else 0

/-- Sharp structural decomposition of the rational coefficient energy:
the diagonal is the product of two one-variable energies, and every remaining
term is an explicit nontrivial solution of `l * k' = l' * k`.  This removes
the raw triple-fiber cardinality loss completely. -/
theorem
    sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_product_add_offDiagonal
    (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) =
      (∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k)) *
        (∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
          Complex.normSq (selbergSqrtZetaSignedNumeratorCoeff X l)) +
        selbergSqrtZetaSignedRationalCoefficientOffDiagonal N X := by
  classical
  let S := selbergSqrtZetaSignedDenominatorNumeratorSupport N X
  let coeff := selbergSqrtZetaSignedRationalPairCoeff N X
  rw [sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_crossProduct]
  calc
    (∑ p ∈ S, ∑ r ∈ S,
        if p.2 * r.1 = r.2 * p.1 then coeff p * coeff r else 0) =
        (∑ p ∈ S, (coeff p) ^ 2) +
          ∑ p ∈ S, ∑ r ∈ S.erase p,
            if p.2 * r.1 = r.2 * p.1 then
              coeff p * coeff r
            else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      let f : ℕ × ℕ → ℝ := fun r =>
        if p.2 * r.1 = r.2 * p.1 then coeff p * coeff r else 0
      calc
        (∑ r ∈ S, f r) =
            (∑ r ∈ S.erase p, f r) + f p :=
          (Finset.sum_erase_add S f hp).symm
        _ = (coeff p) ^ 2 + ∑ r ∈ S.erase p, f r := by
          rw [add_comm]
          simp only [f, coeff, if_pos rfl]
          ring
    _ = (∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k)) *
        (∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
          Complex.normSq (selbergSqrtZetaSignedNumeratorCoeff X l)) +
        selbergSqrtZetaSignedRationalCoefficientOffDiagonal N X := by
      rw [sum_normSq_selbergSqrtZetaSignedRationalPairCoeff_eq_product]
      rfl

/-- A cardinality-free upper bound: proving the desired Selberg-scale energy
now reduces exactly to bounding the explicit off-diagonal correlation. -/
theorem
    sum_normSq_selbergSqrtZetaSignedRationalCoeff_le_product_add_abs_offDiagonal
    (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) ≤
      (∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k)) *
        (∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
          Complex.normSq (selbergSqrtZetaSignedNumeratorCoeff X l)) +
        |selbergSqrtZetaSignedRationalCoefficientOffDiagonal N X| := by
  rw [
    sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_product_add_offDiagonal]
  exact add_le_add (le_refl _)
    (le_abs_self
      (selbergSqrtZetaSignedRationalCoefficientOffDiagonal N X))

end HardyTheorem
