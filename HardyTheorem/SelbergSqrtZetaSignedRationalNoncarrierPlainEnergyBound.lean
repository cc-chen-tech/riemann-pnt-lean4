import HardyTheorem.SelbergSqrtZetaSignedRationalCoefficientReducedPairEnergy
import HardyTheorem.SelbergSqrtZetaSignedRationalNoncarrierEnergy
import HardyTheorem.SelbergSqrtZetaSignedReducedPairCompleteCancellation
import HardyTheorem.SelbergSqrtZetaSignedReducedRayBoundaryTaperEnergy

/-!
# Plain coefficient energy after deleting the rational carrier

The unweighted squared-coefficient energy on the rational noncarrier support
is exactly the full energy with the ratio-one coefficient removed. Reindexing
by positive coprime pairs then deletes precisely `(1, 1)` and preserves the
sharp `1 / (a * b)` weight.

The final estimate applies the existing complete-ray cancellation bound and
the pointwise boundary-taper estimate. It leaves the signed high-product tail
and an explicit erased-pair boundary budget; it makes no second-moment claim.
-/

open scoped BigOperators

namespace HardyTheorem

private theorem inv_sqrt_sq_eq_inv_noncarrierPlain
    {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ ^ 2 = x⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hx]

/-- The plain noncarrier energy plus the deleted carrier energy is exactly the
full rational coefficient energy. -/
theorem
    sum_normSq_selbergSqrtZetaSignedRationalNoncarrierCoeff_add_carrier_eq_full
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) +
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X 1) =
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) := by
  classical
  unfold selbergSqrtZetaSignedRationalNoncarrierSupport
  exact Finset.sum_erase_add _ _
    (one_mem_selbergSqrtZetaSignedRationalSupport hN hX)

/-- Subtractive form of the exact carrier deletion identity. -/
theorem
    sum_normSq_selbergSqrtZetaSignedRationalNoncarrierCoeff_eq_full_sub_carrier
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) =
      (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) -
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X 1) := by
  linarith only
    [sum_normSq_selbergSqrtZetaSignedRationalNoncarrierCoeff_add_carrier_eq_full
      hN hX]

/-- Exact erased reduced-pair expression for the plain noncarrier energy.
Each surviving coefficient retains the complete-plus-boundary cancellation
inside one square. -/
theorem
    sum_normSq_selbergSqrtZetaSignedRationalNoncarrierCoeff_eq_reducedPairCompleteBoundary_erase_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) =
      ∑ p ∈
          (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
            selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2 := by
  rw [sum_normSq_noncarrier_eq_reducedPairSupport_erase_one hN hX]
  apply Finset.sum_congr rfl
  intro p hp
  have hpFull :
      p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X :=
    Finset.mem_of_mem_erase hp
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hpFull
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
    inv_sqrt_sq_eq_inv_noncarrierPlain
      (by positivity : (0 : ℝ) ≤ (p.1 : ℝ) * p.2)]

/-- Splitting complete and boundary pieces costs a factor two, while the
plain energy keeps its sharp unweighted `1 / (a * b)` arithmetic weight. -/
theorem
    sum_normSq_selbergSqrtZetaSignedRationalNoncarrierCoeff_le_reducedPairComplete_add_boundary_erase_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) ≤
      ∑ p ∈
          (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        (2 * ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2) ^ 2) +
        2 * ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2)) := by
  rw [
    sum_normSq_selbergSqrtZetaSignedRationalNoncarrierCoeff_eq_reducedPairCompleteBoundary_erase_one
      hN hX]
  apply Finset.sum_le_sum
  intro p hp
  let invab : ℝ := (((p.1 * p.2 : ℕ) : ℝ)⁻¹)
  let complete :=
    selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2
  let boundary :=
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2
  have hinv : 0 ≤ invab := by
    dsimp only [invab]
    positivity
  have hsplit :
      (complete + boundary) ^ 2 ≤
        2 * complete ^ 2 + 2 * boundary ^ 2 := by
    nlinarith [sq_nonneg (complete - boundary)]
  calc
    (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
            selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2 =
        invab * (complete + boundary) ^ 2 := by rfl
    _ ≤ invab * (2 * complete ^ 2 + 2 * boundary ^ 2) :=
      mul_le_mul_of_nonneg_left hsplit hinv
    _ = 2 * ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2) ^ 2) +
        2 * ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2) := by
      dsimp only [invab, complete, boundary]
      ring

/-- Explicit boundary-taper budget on positive coprime pairs other than the
carrier pair. -/
noncomputable def
    selbergSqrtZetaSignedRationalNoncarrierBoundaryTaperBudget
    (N X : ℕ) : ℝ :=
  ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
    (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
      ((∑ d ∈ Finset.Ioc
          (min N X / p.2)
          (min (X / p.1) (N * X / p.2)),
          (d : ℝ)⁻¹) ^ 2 *
        (harmonic X : ℝ) *
        (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2))

private theorem
    sum_noncarrierCompletePlain_le_completeEnergy
    (N X : ℕ) :
    (∑ p ∈
        (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2) ^ 2) ≤
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2) := by
  calc
    (∑ p ∈
        (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2) ^ 2) ≤
      ∑ p ∈
          (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hweight :
          1 ≤ ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
      exact
        (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hweight
              (mul_nonneg (by positivity) (sq_nonneg _)))
    _ ≤ _ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (by
          intro p hpFull hpErase
          positivity)

private theorem
    sum_noncarrierBoundaryPlain_le_boundaryTaperBudget
    {N X : ℕ} (hX : 2 ≤ X) :
    (∑ p ∈
        (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2) ≤
      selbergSqrtZetaSignedRationalNoncarrierBoundaryTaperBudget N X := by
  unfold selbergSqrtZetaSignedRationalNoncarrierBoundaryTaperBudget
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left
    (selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_four_mul_harmonicTail_sq_mul_harmonic_mul_sq_div_log_sq
      hX)
    (by positivity)

/-- The strongest compiled plain noncarrier bound supplied here. The complete
part uses the current `19/4` low-product estimate and retains the signed
high-product energy. The boundary part is an explicit erased-pair harmonic
tail budget with `1 / log(X)^2` taper decay. -/
theorem
    sum_normSq_selbergSqrtZetaSignedRationalNoncarrierCoeff_le_completeHigh_add_boundaryTaper
    {N X : ℕ} (hN : 1 ≤ N) (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) ≤
      2 * (((X : ℝ) ^ 2 + 1) *
        ((19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X)) +
      2 * selbergSqrtZetaSignedRationalNoncarrierBoundaryTaperBudget N X := by
  have hsplit :=
    sum_normSq_selbergSqrtZetaSignedRationalNoncarrierCoeff_le_reducedPairComplete_add_boundary_erase_one
      hN (by omega : 1 ≤ X)
  have hcomplete := sum_noncarrierCompletePlain_le_completeEnergy N X
  have hcompleteArithmetic :=
    sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_le_nineteen_fourths_add_high
      hNX hX hlarge
  have hboundary :=
    sum_noncarrierBoundaryPlain_le_boundaryTaperBudget
      (N := N) (X := X) (by omega : 2 ≤ X)
  rw [Finset.sum_add_distrib] at hsplit
  simp only [← Finset.mul_sum] at hsplit
  nlinarith

end HardyTheorem
