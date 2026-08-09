import HardyTheorem.SelbergSqrtZetaRestrictedPairMoment

open scoped BigOperators

namespace HardyTheorem

/-!
# Explicit bounds for the restricted pair moment

The totient-square remainder from
`SelbergSqrtZetaRestrictedPairMoment` is first returned exactly to the
underlying pair box.  Its reciprocal-lcm form is then bounded by an explicit
polynomial-harmonic expression.
-/

/-- The divisor-restricted product-multiplicity sum is exactly the reciprocal
product sum over pairs in the original box. -/
theorem
    sum_productMultiplicity_mul_inv_filter_eq_sum_completeRangePair_inv_filter
    (X d : ℕ) :
    (∑ r ∈ (Finset.Icc 1 (X * X)).filter (fun r => d ∣ r),
        (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
          (r : ℝ)⁻¹) =
      ∑ p ∈ selbergShortCompleteRangePairSupport X,
        if d ∣ selbergShortCompleteRangePairProduct p then
          (selbergShortCompleteRangePairProduct p : ℝ)⁻¹
        else 0 := by
  simpa only [Finset.sum_filter, mul_ite, mul_inv_rev, one_mul, mul_zero] using
    (sum_completeRangePair_kernel_eq_productMultiplicity X
      (fun r => if d ∣ r then (r : ℝ)⁻¹ else 0)).symm

/-- The total unsigned product multiplicity is the cardinality `X^2` of the
pair box. -/
theorem sum_selbergShortRestrictedPairProductMultiplicity_eq_sq (X : ℕ) :
    (∑ r ∈ Finset.Icc 1 (X * X),
        (selbergShortRestrictedPairProductMultiplicity X r : ℝ)) =
      (X : ℝ) ^ 2 := by
  calc
    (∑ r ∈ Finset.Icc 1 (X * X),
        (selbergShortRestrictedPairProductMultiplicity X r : ℝ)) =
        ∑ r ∈ Finset.Icc 1 (X * X),
          (selbergShortRestrictedPairProductMultiplicity X r : ℝ) * 1 := by
      simp
    _ = ∑ _p ∈ selbergShortCompleteRangePairSupport X, (1 : ℝ) :=
      (sum_completeRangePair_kernel_eq_productMultiplicity X
        (fun _ => 1)).symm
    _ = (X : ℝ) ^ 2 := by
      simp [selbergShortCompleteRangePairSupport, Nat.card_Icc, pow_two]

/-- The reciprocal-product mass of the pair box factors as the square of one
harmonic sum. -/
theorem sum_selbergShortRestrictedPairProductMultiplicity_mul_inv_eq_harmonic_sq
    (X : ℕ) :
    (∑ r ∈ Finset.Icc 1 (X * X),
        (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
          (r : ℝ)⁻¹) =
      (harmonic X : ℝ) ^ 2 := by
  rw [← sum_completeRangePair_kernel_eq_productMultiplicity X
    (fun r => (r : ℝ)⁻¹)]
  have hharm :
      (∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹) = (harmonic X : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
  calc
    (∑ p ∈ selbergShortCompleteRangePairSupport X,
        (selbergShortCompleteRangePairProduct p : ℝ)⁻¹) =
        ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
          ((a * b : ℕ) : ℝ)⁻¹ := by
      exact Finset.sum_product (Finset.Icc 1 X) (Finset.Icc 1 X)
        (fun p : ℕ × ℕ => ((p.1 * p.2 : ℕ) : ℝ)⁻¹)
    _ = (∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [Nat.cast_mul, mul_inv_rev]
      ring
    _ = (harmonic X : ℝ) ^ 2 := by rw [hharm]

/-- The finite totient-square remainder is bounded by `X^2 H_X^2`.

The proof returns to the reciprocal-lcm quadratic form.  Since `r ∣ lcm r s`,
one reciprocal-lcm factor is at most `1 / r`; the two remaining multiplicity
sums are exactly the mass and reciprocal mass of the original pair box. -/
theorem totientSquares_selbergShortRestrictedPairProductMultiplicity_le
    (X : ℕ) :
    (∑ d ∈ Finset.Icc 1 (X * X), (Nat.totient d : ℝ) *
        (∑ r ∈ (Finset.Icc 1 (X * X)).filter (fun r => d ∣ r),
          (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
            (r : ℝ)⁻¹) ^ 2) ≤
      (X : ℝ) ^ 2 * (harmonic X : ℝ) ^ 2 := by
  rw [← MathlibAux.sum_reciprocal_lcm_quadratic_eq_totient_squares
    (fun r => (selbergShortRestrictedPairProductMultiplicity X r : ℝ))
    (X * X)]
  calc
    (∑ r ∈ Finset.Icc 1 (X * X), ∑ s ∈ Finset.Icc 1 (X * X),
        (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
          (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
            (Nat.lcm r s : ℝ)⁻¹) ≤
        ∑ r ∈ Finset.Icc 1 (X * X), ∑ s ∈ Finset.Icc 1 (X * X),
          (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
            (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
              (r : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      have hrPos : 0 < r := (Finset.mem_Icc.mp hr).1
      have hsPos : 0 < s := (Finset.mem_Icc.mp hs).1
      have hlcmPos : 0 < Nat.lcm r s := Nat.lcm_pos hrPos hsPos
      have hrLeLcm : (r : ℝ) ≤ (Nat.lcm r s : ℝ) := by
        exact_mod_cast
          Nat.le_of_dvd hlcmPos (Nat.dvd_lcm_left r s)
      have hinv :
          (Nat.lcm r s : ℝ)⁻¹ ≤ (r : ℝ)⁻¹ := by
        exact (inv_le_inv₀ (by exact_mod_cast hlcmPos)
          (by exact_mod_cast hrPos)).2 hrLeLcm
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ =
        (∑ r ∈ Finset.Icc 1 (X * X),
          (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
            (r : ℝ)⁻¹) *
        (∑ s ∈ Finset.Icc 1 (X * X),
          (selbergShortRestrictedPairProductMultiplicity X s : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      ring
    _ = (X : ℝ) ^ 2 * (harmonic X : ℝ) ^ 2 := by
      rw [
        sum_selbergShortRestrictedPairProductMultiplicity_mul_inv_eq_harmonic_sq,
        sum_selbergShortRestrictedPairProductMultiplicity_eq_sq]
      ring

/-- The minimum-envelope high-range pair sum has an explicit
polynomial-harmonic bound. -/
theorem
    weighted_highRange_selbergShortCompleteRangePairs_le_harmonicPolynomial
    {L U : ℕ} (hL : 1 ≤ L) (X : ℕ) (H : ℝ) :
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
      H ^ 2 * (harmonic U : ℝ) *
        ((X : ℝ) ^ 2 * (harmonic X : ℝ) ^ 2) := by
  calc
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
        H ^ 2 * (harmonic U : ℝ) *
          ∑ d ∈ Finset.Icc 1 (X * X), (Nat.totient d : ℝ) *
            (∑ r ∈ (Finset.Icc 1 (X * X)).filter (fun r => d ∣ r),
              (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
                (r : ℝ)⁻¹) ^ 2 :=
      weighted_highRange_selbergShortCompleteRangePairs_le_totientSquares
        hL X H
    _ ≤ H ^ 2 * (harmonic U : ℝ) *
        ((X : ℝ) ^ 2 * (harmonic X : ℝ) ^ 2) := by
      have hU_nonneg : 0 ≤ (harmonic U : ℝ) := by
        simpa using harmonic_natCast_mono (Nat.zero_le U)
      exact mul_le_mul_of_nonneg_left
        (totientSquares_selbergShortRestrictedPairProductMultiplicity_le X)
        (mul_nonneg (sq_nonneg H) hU_nonneg)

/-- Replacing both harmonic factors by elementary logarithmic majorants gives
a bound involving only `H`, `U`, and `X`. -/
theorem weighted_highRange_selbergShortCompleteRangePairs_le_logPolynomial
    {L U : ℕ} (hL : 1 ≤ L) (X : ℕ) (H : ℝ) :
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
      H ^ 2 * (1 + Real.log U) *
        ((X : ℝ) ^ 2 * (1 + Real.log X) ^ 2) := by
  have hU := harmonic_le_one_add_log U
  have hX := harmonic_le_one_add_log X
  have hU_nonneg : 0 ≤ (harmonic U : ℝ) := by
    simpa using harmonic_natCast_mono (Nat.zero_le U)
  have hX_nonneg : 0 ≤ (harmonic X : ℝ) := by
    simpa using harmonic_natCast_mono (Nat.zero_le X)
  have hlogU : 0 ≤ 1 + Real.log U := hU_nonneg.trans hU
  have hlogX : 0 ≤ 1 + Real.log X :=
    hX_nonneg.trans hX
  have hXsq :
      (harmonic X : ℝ) ^ 2 ≤ (1 + Real.log X) ^ 2 :=
    (sq_le_sq₀ hX_nonneg hlogX).2 hX
  calc
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
        H ^ 2 * (harmonic U : ℝ) *
          ((X : ℝ) ^ 2 * (harmonic X : ℝ) ^ 2) :=
      weighted_highRange_selbergShortCompleteRangePairs_le_harmonicPolynomial
        hL X H
    _ ≤ H ^ 2 * (1 + Real.log U) *
        ((X : ℝ) ^ 2 * (harmonic X : ℝ) ^ 2) := by
      gcongr
    _ ≤ H ^ 2 * (1 + Real.log U) *
        ((X : ℝ) ^ 2 * (1 + Real.log X) ^ 2) := by
      gcongr

/-- The retained triple-fiber high-range energy satisfies the same explicit
logarithmic-polynomial bound. -/
theorem weighted_highRange_selbergSqrtZetaShortCollectedTripleFiberEnergy_le_logPolynomial
    {N L U : ℕ} (hL : 1 ≤ L) {X : ℕ} (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          selbergSqrtZetaShortCollectedTripleFiberEnergy N X k) ≤
      H ^ 2 * (1 + Real.log U) *
        ((X : ℝ) ^ 2 * (1 + Real.log X) ^ 2) := by
  calc
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          selbergSqrtZetaShortCollectedTripleFiberEnergy N X k) ≤
        ∑ k ∈ Finset.Ioc L U,
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
            ((selbergShortCompleteRangePairs X k).card ^ 2 /
              (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact mul_le_mul_of_nonneg_left
        (selbergSqrtZetaShortCollectedTripleFiberEnergy_le_completePair_card_sq_div
          hX)
        (sq_nonneg _)
    _ ≤ H ^ 2 * (1 + Real.log U) *
        ((X : ℝ) ^ 2 * (1 + Real.log X) ^ 2) :=
      weighted_highRange_selbergShortCompleteRangePairs_le_logPolynomial
        hL X H

/-- The actual transformed high range is now bounded without a remaining
finite arithmetic sum. -/
theorem
    sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_logPolynomial
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      H ^ 2 * (1 + Real.log ((N * X * X : ℕ) : ℝ)) *
        ((X : ℝ) ^ 2 * (1 + Real.log X) ^ 2) := by
  have hmin : 1 ≤ min N X := Nat.le_min.mpr ⟨hN, by omega⟩
  exact
    (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_tripleFiberMin
      hN hX H).trans
      (weighted_highRange_selbergSqrtZetaShortCollectedTripleFiberEnergy_le_logPolynomial
        (N := N) (L := min N X) (U := N * X * X) hmin hX H)

/-- Combining the proved low range with the explicit high-range estimate
removes the last finite pair-moment expression from the full energy bound. -/
theorem
    sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_logPolynomialHighRange
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        H ^ 2 * (1 + Real.log ((N * X * X : ℕ) : ℝ)) *
          ((X : ℝ) ^ 2 * (1 + Real.log X) ^ 2) := by
  have hmin : 1 ≤ min N X := Nat.le_min.mpr ⟨hN, by omega⟩
  exact
    (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_tripleFiberMinHighRange
      hN hX hlarge H).trans
      (add_le_add (le_refl _)
        (weighted_highRange_selbergSqrtZetaShortCollectedTripleFiberEnergy_le_logPolynomial
          (N := N) (L := min N X) (U := N * X * X) hmin hX H))

end HardyTheorem
