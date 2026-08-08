import HardyTheorem.SelbergSqrtZetaSignedCollectedL1

/-!
# Raw-energy compression for the signed square-root-zeta model

The frequency-fiber budget can be bounded without estimating every fiber
separately. Each fiber has cardinality at most the full raw support, the
fibers partition that support, and the number of distinct frequencies is at
most the support cardinality. This compresses the pseudo-correlation
coefficient budget to support-cardinality squared times the raw coefficient
energy.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The raw signed triple support has exactly `N * X * X` elements. -/
theorem card_selbergSqrtZetaSignedPhaseSupport (N X : ℕ) :
    (selbergSqrtZetaSignedPhaseSupport N X).card = N * X * X := by
  simp [selbergSqrtZetaSignedPhaseSupport, Nat.card_Icc, Nat.mul_assoc]

/-- Collecting equal frequencies cannot increase support cardinality. -/
theorem card_selbergSqrtZetaSignedCollectedFrequencySupport_le
    (N X : ℕ) :
    (selbergSqrtZetaSignedCollectedFrequencySupport N X).card ≤
      (selbergSqrtZetaSignedPhaseSupport N X).card := by
  exact Finset.card_image_le

/-- Summing the raw square energy over all frequency fibers recovers the
total raw square energy exactly. -/
theorem sum_sum_normSq_selbergSqrtZetaSignedPhaseCoeff_fibers
    (N X : ℕ) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        ∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
          Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p)) =
      ∑ p ∈ selbergSqrtZetaSignedPhaseSupport N X,
        Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) := by
  classical
  let S := selbergSqrtZetaSignedPhaseSupport N X
  let K := selbergSqrtZetaSignedCollectedFrequencySupport N X
  let f : ℕ × (ℕ × ℕ) → ℝ := fun p =>
    Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p)
  have hmaps : ∀ p ∈ S, selbergSqrtZetaSignedPhaseFrequency p ∈ K := by
    intro p hp
    exact Finset.mem_image_of_mem _ hp
  simpa only [S, K, f, selbergSqrtZetaSignedCollectedFrequencySupport,
    MathlibAux.collectedFrequencySupport] using
    (Finset.sum_fiberwise_of_maps_to hmaps f)

/-- The exact frequency-fiber multiplicity energy is bounded by full-support
cardinality times the total raw coefficient energy. -/
theorem
    sum_selbergSqrtZetaSignedFrequencyFiberCard_mul_energy_le_raw
    (N X : ℕ) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        (((selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
        ∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
          Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p)) ≤
      ((selbergSqrtZetaSignedPhaseSupport N X).card : ℝ) *
        ∑ p ∈ selbergSqrtZetaSignedPhaseSupport N X,
          Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) := by
  let S := selbergSqrtZetaSignedPhaseSupport N X
  let K := selbergSqrtZetaSignedCollectedFrequencySupport N X
  let E : ℝ → ℝ := fun omega =>
    ∑ p ∈ S.filter
      (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
      Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p)
  have hterm : ∀ omega ∈ K,
      (((S.filter
        (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
          E omega) ≤ (S.card : ℝ) * E omega := by
    intro omega homega
    apply mul_le_mul_of_nonneg_right
    · have hcard :
          (S.filter
            (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card ≤
              S.card :=
          Finset.card_filter_le _ _
      exact_mod_cast hcard
    · exact Finset.sum_nonneg fun p hp => Complex.normSq_nonneg _
  calc
    (∑ omega ∈ K,
        (((S.filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
          E omega)) ≤
        ∑ omega ∈ K, (S.card : ℝ) * E omega :=
      Finset.sum_le_sum fun omega homega => hterm omega homega
    _ = (S.card : ℝ) * ∑ omega ∈ K, E omega := by
      rw [Finset.mul_sum]
    _ = (S.card : ℝ) *
        ∑ p ∈ S, Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) := by
      rw [sum_sum_normSq_selbergSqrtZetaSignedPhaseCoeff_fibers N X]

/-- A nonnegative pseudo-correlation coefficient double sum is controlled by
the square of the raw support cardinality times raw coefficient energy. -/
theorem
    sum_sum_mul_norm_selbergSqrtZetaSignedCollectedCoeff_le_raw_energy
    (N X : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        ∑ nu ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          C * (‖selbergSqrtZetaSignedCollectedCoeff N X omega‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff N X nu‖)) ≤
      C * ((selbergSqrtZetaSignedPhaseSupport N X).card : ℝ) *
        (((selbergSqrtZetaSignedPhaseSupport N X).card : ℝ) *
          ∑ p ∈ selbergSqrtZetaSignedPhaseSupport N X,
            Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p)) := by
  have hK :
      ((selbergSqrtZetaSignedCollectedFrequencySupport N X).card : ℝ) ≤
        ((selbergSqrtZetaSignedPhaseSupport N X).card : ℝ) := by
    exact_mod_cast
      card_selbergSqrtZetaSignedCollectedFrequencySupport_le N X
  have hF :=
    sum_selbergSqrtZetaSignedFrequencyFiberCard_mul_energy_le_raw N X
  have hFnonneg : 0 ≤
      ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        (((selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
        ∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
          Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) :=
    Finset.sum_nonneg fun omega homega =>
      mul_nonneg (Nat.cast_nonneg _)
        (Finset.sum_nonneg fun p hp => Complex.normSq_nonneg _)
  have hScard : 0 ≤
      ((selbergSqrtZetaSignedPhaseSupport N X).card : ℝ) :=
    Nat.cast_nonneg _
  calc
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        ∑ nu ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          C * (‖selbergSqrtZetaSignedCollectedCoeff N X omega‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff N X nu‖)) ≤
        C *
          ((selbergSqrtZetaSignedCollectedFrequencySupport N X).card : ℝ) *
          ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
            (((selbergSqrtZetaSignedPhaseSupport N X).filter
              (fun p =>
                selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
            ∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
              (fun p =>
                selbergSqrtZetaSignedPhaseFrequency p = omega),
              Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) :=
      sum_sum_mul_norm_selbergSqrtZetaSignedCollectedCoeff_le_fiber_budget
        N X hC
    _ ≤ C *
          ((selbergSqrtZetaSignedPhaseSupport N X).card : ℝ) *
          (((selbergSqrtZetaSignedPhaseSupport N X).card : ℝ) *
            ∑ p ∈ selbergSqrtZetaSignedPhaseSupport N X,
              Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p)) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hK hF hFnonneg hScard) hC

end HardyTheorem
