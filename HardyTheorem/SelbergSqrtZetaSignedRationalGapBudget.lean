import HardyTheorem.SelbergSqrtZetaSignedOrdinaryShiftBudget
import HardyTheorem.SelbergSqrtZetaSignedRationalRealCollected

/-!
# Rational indexing of the signed Selberg gap budget

The off-diagonal term in the signed-model second moment is initially indexed
by real logarithmic frequencies.  This file reindexes that finite sum by the
underlying positive rational keys.  The change of index is exact: no absolute
value, cardinality, or minimum-separation estimate is introduced.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-- Every rational key in the collected signed support is positive. -/
theorem selbergSqrtZetaSignedRational_pos_of_mem
    {N X : ℕ} {q : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X) :
    0 < q := by
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  exact selbergSqrtZetaSignedRationalKey_pos_of_mem hp

/-- On the positive rational support, a frequency difference is the
logarithm of the corresponding rational ratio. -/
theorem selbergSqrtZetaSignedRationalFrequency_sub_eq_log_div
    {N X : ℕ} {q r : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedRationalSupport N X) :
    selbergSqrtZetaSignedRationalFrequency q -
        selbergSqrtZetaSignedRationalFrequency r =
      Real.log ((q : ℝ) / (r : ℝ)) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast
      (selbergSqrtZetaSignedRational_pos_of_mem hq).ne'
  have hr0 : (r : ℝ) ≠ 0 := by
    exact_mod_cast
      (selbergSqrtZetaSignedRational_pos_of_mem hr).ne'
  exact (Real.log_div hq0 hr0).symm

/-- The exact reciprocal-log-gap budget of the rationally collected signed
square-root-zeta coefficients. -/
noncomputable def selbergSqrtZetaSignedRationalGapBudget
    (N X : ℕ) (delta : ℝ) : ℝ :=
  ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
    ∑ r ∈ selbergSqrtZetaSignedRationalSupport N X,
      if q = r then 0
      else
        ‖selbergSqrtZetaSignedRationalCoeff N X q‖ *
          ‖selbergSqrtZetaSignedRationalCoeff N X r‖ *
          ((2 + delta / 2) /
            |Real.log ((q : ℝ) / (r : ℝ))|)

/-- The real-frequency reciprocal-gap sum is exactly the corresponding
rational-key sum. -/
theorem sum_collectedFrequencyGap_eq_rationalGapBudget
    (N X : ℕ) (delta : ℝ) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
      ∑ nu ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        if omega = nu then 0
        else
          ‖selbergSqrtZetaSignedCollectedCoeff N X omega‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff N X nu‖ *
            ((2 + delta / 2) / |omega - nu|)) =
      selbergSqrtZetaSignedRationalGapBudget N X delta := by
  classical
  let Q : Finset ℚ := selbergSqrtZetaSignedRationalSupport N X
  let frequency : ℚ → ℝ := selbergSqrtZetaSignedRationalFrequency
  have hinj : Set.InjOn frequency (Q : Set ℚ) := by
    simpa only [Q, frequency] using
      selbergSqrtZetaSignedRationalFrequency_injOn N X
  rw [← image_rationalFrequency_rationalSupport N X]
  change
    (∑ omega ∈ Q.image frequency,
      ∑ nu ∈ Q.image frequency,
        if omega = nu then 0
        else
          ‖selbergSqrtZetaSignedCollectedCoeff N X omega‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff N X nu‖ *
            ((2 + delta / 2) / |omega - nu|)) = _
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro r hr
  rw [selbergSqrtZetaSignedCollectedCoeff_rationalFrequency hq,
    selbergSqrtZetaSignedCollectedCoeff_rationalFrequency hr]
  by_cases hqr : q = r
  · subst r
    simp
  · have hfrequency :
        frequency q ≠ frequency r := by
      intro h
      exact hqr (hinj hq hr h)
    simp only [hfrequency, hqr, if_false]
    rw [selbergSqrtZetaSignedRationalFrequency_sub_eq_log_div hq hr]

/-- The ordinary signed-model correlation bound with both its diagonal energy
and its off-diagonal reciprocal-gap term indexed by rational keys. -/
theorem
    norm_integral_integral_integral_selbergSqrtZetaSignedOrdinaryCorrelation_le_rational_gap
    (kappa T : ℝ) (X : ℕ) {delta : ℝ}
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))‖ ≤
      delta ^ 2 *
          selbergSqrtZetaSignedRationalGapBudget
            (firstZetaApproximationCutoff T) X delta +
        delta ^ 2 * (T - delta) *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport
              (firstZetaApproximationCutoff T) X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff
                (firstZetaApproximationCutoff T) X q) := by
  simpa only [
    sum_collectedFrequencyGap_eq_rationalGapBudget] using
    norm_integral_integral_integral_selbergSqrtZetaSignedOrdinaryCorrelation_le_rational_energy
      kappa T X hT hdelta hroom

end HardyTheorem
