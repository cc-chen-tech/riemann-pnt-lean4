import HardyTheorem.SelbergSqrtZetaSignedRationalReducedPairEnergy

/-!
# Reduced-pair form of the rational coefficient energy

The diagonal coefficient energy in the signed rational short-model budget is
indexed by rational keys.  Reindexing those keys by their canonical positive
coprime numerator-denominator pairs shows that it is governed by the same
complete-ray and boundary terms as the local-frequency-separation energy.

This is a structural reduction only.  It introduces no arithmetic estimate on
either ray term.
-/

open scoped BigOperators

namespace HardyTheorem

private theorem inv_sqrt_sq_eq_inv
    {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ ^ 2 = x⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hx]

/-- Exact reduced-pair expression for the diagonal rational coefficient
energy.  Each coefficient is the complete signed ray contribution plus its
boundary defect, with the sharp harmonic normalization `1 / (a*b)`. -/
theorem sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_reducedPairEnergy
    (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) =
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
            selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2 := by
  rw [
    sum_selbergSqrtZetaSignedRationalSupport_eq_reducedPairSupport
      N X (fun q =>
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q))]
  apply Finset.sum_congr rfl
  intro p hp
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
  rw [selbergSqrtZetaSignedReducedPairKey,
    selbergSqrtZetaSignedRationalCoeff_reduced_eq_coprimeRayScaleSum
      N X p.1 p.2 hpFacts.2.2.1 hpFacts.2.1,
    ← Complex.ofReal_sum,
    selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_bilinearScaleSum,
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_eq_complete_add_boundary
      N X p.1 p.2 hpFacts.2.1,
    Complex.normSq_ofReal]
  push_cast
  rw [← pow_two
    ((Real.sqrt ((p.1 : ℝ) * (p.2 : ℝ)))⁻¹ *
      (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
        selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2))]
  rw [mul_pow,
    inv_sqrt_sq_eq_inv (by positivity : (0 : ℝ) ≤ (p.1 : ℝ) * p.2)]

/-- The diagonal rational coefficient energy is controlled by the same split
complete-plus-boundary reduced-pair budget used for local frequency
separation.  The extra geometric weight is at least one, so no separate
diagonal arithmetic object is required. -/
theorem
    sum_normSq_selbergSqrtZetaSignedRationalCoeff_le_reducedPairComplete_add_boundary
    (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) ≤
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) +
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2))) := by
  rw [
    sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_reducedPairEnergy]
  apply Finset.sum_le_sum
  intro p hp
  let w : ℝ := ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ)
  let invab : ℝ := (((p.1 * p.2 : ℕ) : ℝ)⁻¹)
  let complete :=
    selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2
  let boundary :=
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2
  have hw : 1 ≤ w := by
    dsimp only [w]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hinv : 0 ≤ invab := by
    dsimp only [invab]
    positivity
  have hcomplete : 0 ≤ invab * complete ^ 2 :=
    mul_nonneg hinv (sq_nonneg _)
  have hboundary : 0 ≤ invab * boundary ^ 2 :=
    mul_nonneg hinv (sq_nonneg _)
  have hsplit :
      (complete + boundary) ^ 2 ≤
        2 * complete ^ 2 + 2 * boundary ^ 2 := by
    nlinarith [sq_nonneg (complete - boundary)]
  have hcompleteWeight :
      invab * complete ^ 2 ≤ w * (invab * complete ^ 2) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hw hcomplete
  have hboundaryWeight :
      invab * boundary ^ 2 ≤ w * (invab * boundary ^ 2) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hw hboundary
  calc
    invab * (complete + boundary) ^ 2 ≤
        invab * (2 * complete ^ 2 + 2 * boundary ^ 2) :=
      mul_le_mul_of_nonneg_left hsplit hinv
    _ = 2 * (invab * complete ^ 2) +
        2 * (invab * boundary ^ 2) := by ring
    _ ≤ 2 * (w * (invab * complete ^ 2)) +
        2 * (w * (invab * boundary ^ 2)) := by
      gcongr
    _ = 2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) +
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2)) := by
      rfl

end HardyTheorem
