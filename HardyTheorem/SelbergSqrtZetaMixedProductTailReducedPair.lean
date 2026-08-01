import HardyTheorem.SelbergSqrtZetaRectangularParseval
import HardyTheorem.SelbergSqrtZetaSignedRationalCoefficientReducedPairEnergy
import HardyTheorem.SelbergSqrtZetaSignedReducedPairCompleteCancellation
import HardyTheorem.SelbergSqrtZetaSignedReducedRayBoundaryTaperEnergy

/-!
# Reduced-pair control of the filtered product tail

The exact filtered Parseval identity separates the low integer-product block
from the full signed rational coefficient energy.  Combining that subtraction
with the existing reduced-pair complete/boundary estimate retains the low block
instead of enlarging the filtered tail back to the full rational energy.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The mixed-product tail is bounded by the reduced-pair complete/boundary
budget after subtracting the exact low integer-product block.  This does not
remove the rational carrier: ratio-one terms can still occur above the product
cutoff. -/
theorem
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_le_reducedPairComplete_add_boundary_sub_lowProduct
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N ≤
      (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) +
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2)))) -
        ∑ k ∈ Finset.Icc 1 N,
          Complex.normSq
            (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
  rw [
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_eq_signedRationalEnergy_sub_lowProduct
      hN hX]
  exact sub_le_sub_right
    (sum_normSq_selbergSqrtZetaSignedRationalCoeff_le_reducedPairComplete_add_boundary
      N X) _

/-- After the complete reduced-ray contribution is evaluated by multiplicative
Parseval, the filtered tail is reduced to the high complete-product energy,
the boundary defect, and the exact low-product subtraction.  In particular,
the complete contribution no longer carries a loss depending on `N`. -/
theorem
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_le_completeProductHigh_add_boundary_sub_lowProduct
    {N X : ℕ} (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N ≤
      2 * (((X : ℝ) ^ 2 + 1) *
        ((19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X)) +
      2 *
        (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
          ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
            ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2) ^ 2)) -
      ∑ k ∈ Finset.Icc 1 N,
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
  have hN : 1 ≤ N := (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hXone : 1 ≤ X := hX.le
  have htail :=
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_le_reducedPairComplete_add_boundary_sub_lowProduct
      hN hXone
  have hcomplete :=
    sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_le_nineteen_fourths_add_high
      hNX hX hlarge
  have hsplit :
      (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) +
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2)))) =
        2 *
          (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
            ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayCompleteTerm
                  N X p.1 p.2) ^ 2)) +
        2 *
          (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
            ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayBoundaryTerm
                  N X p.1 p.2) ^ 2)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit] at htail
  exact htail.trans
    (sub_le_sub_right
      (add_le_add
        (mul_le_mul_of_nonneg_left hcomplete (by norm_num)) le_rfl) _)

/-- Explicit full-support boundary budget retaining the reciprocal ray weight,
the exact containing harmonic tail, and the logarithmic taper saving. -/
noncomputable def selbergSqrtZetaSignedRationalBoundaryTaperBudget
    (N X : ℕ) : ℝ :=
  ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
    (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
      ((∑ d ∈ Finset.Ioc
          (min N X / p.2)
          (min (X / p.1) (N * X / p.2)),
          (d : ℝ)⁻¹) ^ 2 *
        (harmonic X : ℝ) *
        (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2))

/-- The unweighted boundary square sum is controlled by the explicit taper
budget.  Unlike the local-separation budget, this introduces no geometric
factor `X * min (a*N) b + 1`. -/
theorem sum_selbergSqrtZetaSignedRationalBoundaryPlain_le_boundaryTaperBudget
    {N X : ℕ} (hX : 2 ≤ X) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayBoundaryTerm
          N X p.1 p.2) ^ 2) ≤
      selbergSqrtZetaSignedRationalBoundaryTaperBudget N X := by
  unfold selbergSqrtZetaSignedRationalBoundaryTaperBudget
  apply Finset.sum_le_sum
  intro p _hp
  exact mul_le_mul_of_nonneg_left
    (selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_four_mul_harmonicTail_sq_mul_harmonic_mul_sq_div_log_sq
      hX)
    (by positivity)

private theorem
    sum_selbergSqrtZetaSignedRationalCompletePlain_le_nineteen_fourths_add_high
    {N X : ℕ} (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayCompleteTerm
          N X p.1 p.2) ^ 2) ≤
      (19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X := by
  exact
    sum_selbergSqrtZetaSignedReducedPairCompletePlainEnergy_le_nineteen_fourths_add_high
      hNX hX hlarge

/-- Strong filtered-tail endpoint: the complete part has no `N` loss, the
boundary keeps its `1 / log(X)^2` taper saving, and the exact low-product
energy is still subtracted.  The remaining arithmetic tasks are precisely the
high complete-product energy and this explicit boundary budget. -/
theorem
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_le_completeProductHigh_add_boundaryTaper_sub_lowProduct
    {N X : ℕ} (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N ≤
      2 * ((19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X) +
      2 * selbergSqrtZetaSignedRationalBoundaryTaperBudget N X -
      ∑ k ∈ Finset.Icc 1 N,
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
  have hN : 1 ≤ N := hX.le.trans hNX
  have hXone : 1 ≤ X := hX.le
  rw [
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_eq_signedRationalEnergy_sub_lowProduct
      hN hXone,
    sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_reducedPairEnergy]
  apply sub_le_sub_right
  calc
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
          selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2) ≤
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (2 * ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm
            N X p.1 p.2) ^ 2) +
        2 * ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayBoundaryTerm
            N X p.1 p.2) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p _hp
        have hinv : 0 ≤ (((p.1 * p.2 : ℕ) : ℝ)⁻¹) := by positivity
        have hsplit :
            (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
              selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2 ≤
            2 * (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2 +
            2 * (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2 := by
          nlinarith [sq_nonneg
            (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 -
              selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2)]
        calc
          (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
                selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2 ≤
              (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (2 * (selbergSqrtZetaSignedReducedRayCompleteTerm
                    N X p.1 p.2) ^ 2 +
                  2 * (selbergSqrtZetaSignedReducedRayBoundaryTerm
                    N X p.1 p.2) ^ 2) :=
            mul_le_mul_of_nonneg_left hsplit hinv
          _ = _ := by ring
    _ = 2 *
          (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
            (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayCompleteTerm
                N X p.1 p.2) ^ 2) +
        2 *
          (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
            (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left
        (sum_selbergSqrtZetaSignedRationalCompletePlain_le_nineteen_fourths_add_high
          hNX hX hlarge)
        (by norm_num))
      (mul_le_mul_of_nonneg_left
        (sum_selbergSqrtZetaSignedRationalBoundaryPlain_le_boundaryTaperBudget
          (by omega : 2 ≤ X))
        (by norm_num))

end HardyTheorem
