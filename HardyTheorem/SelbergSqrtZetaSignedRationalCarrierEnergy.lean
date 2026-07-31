import HardyTheorem.SelbergSqrtZetaSignedRationalCarrierDecomposition
import HardyTheorem.SelbergSqrtZetaSignedReducedPairCompleteCancellation
import HardyTheorem.SelbergSqrtZetaSignedReducedRayBoundaryTaperEnergy

/-!
# Energy control for the distinguished rational carrier

When the zeta cutoff contains the taper box, the `(1,1)` reduced ray has no
boundary scales.  Consequently the exact rational carrier coefficient is the
complete ratio coefficient.  This isolates the remaining arithmetic input as
the signed high-product energy, without reintroducing the vacuous split-energy
bound.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The `(1,1)` reduced ray has no boundary defect once the zeta cutoff
contains the taper box. -/
theorem selbergSqrtZetaSignedReducedRayBoundaryTerm_one_one_eq_zero
    {N X : ℕ} (hX : 2 ≤ X) (hNX : X ≤ N) :
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X 1 1 = 0 := by
  have hN : 1 ≤ N := by omega
  have hXleNX : X ≤ N * X := by
    calc
      X = 1 * X := by simp
      _ ≤ N * X := Nat.mul_le_mul_right X hN
  have hbound :=
    selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_four_mul_harmonicTail_sq_mul_harmonic_mul_sq_div_log_sq
      (N := N) (X := X) (a := 1) (b := 1) hX
  simp [Nat.min_eq_right hNX, Nat.min_eq_left hXleNX] at hbound
  nlinarith [sq_nonneg
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X 1 1)]

/-- With no boundary defect, the exact rational carrier is precisely the
complete ratio coefficient at ratio one. -/
theorem selbergSqrtZetaSignedRationalCoeff_one_eq_completeRatioCoeff
    {N X : ℕ} (hX : 2 ≤ X) (hNX : X ≤ N) :
    selbergSqrtZetaSignedRationalCoeff N X 1 =
      (selbergSqrtZetaCompleteRatioCoeff X 1 : ℂ) := by
  rw [selbergSqrtZetaSignedRationalCoeff_one_eq_complete_add_boundary]
  rw [selbergSqrtZetaSignedReducedRayBoundaryTerm_one_one_eq_zero hX hNX]
  simp only [add_zero]
  have hcomplete :=
    selbergSqrtZetaCompleteRatioCoeff_reduced_eq_completeTerm
      (N := N) (X := X) (a := 1) (b := 1)
      hNX (by omega) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcomplete
  rw [hcomplete]

/-- The carrier square is controlled by the proved low-product constant plus
the explicit signed high-product tail.  No split-energy smallness assumption
is used. -/
theorem
    normSq_selbergSqrtZetaSignedRationalCoeff_one_le_nineteen_fourths_add_high
    {N X : ℕ} (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X 1) ≤
      (19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X := by
  have hXtwo : 2 ≤ X := by omega
  have hone : (1 : ℚ) ∈ selbergSqrtZetaCompleteRatioSupport X := by
    unfold selbergSqrtZetaCompleteRatioSupport
      selbergSqrtZetaCompletePairSupport
      selbergSqrtZetaCompleteIndexSupport
    apply Finset.mem_image.mpr
    refine ⟨(1, 1), ?_, ?_⟩
    · simp [hX.le]
    · simp [selbergSqrtZetaCompleteRatioKey]
  have hsingle :
      selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 ≤
        ∑ q ∈ selbergSqrtZetaCompleteRatioSupport X,
          selbergSqrtZetaCompleteRatioCoeff X q ^ 2 := by
    exact Finset.single_le_sum (fun q _hq => sq_nonneg _) hone
  calc
    Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X 1) =
        selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 := by
      rw [selbergSqrtZetaSignedRationalCoeff_one_eq_completeRatioCoeff
        hXtwo hNX]
      simp [Complex.normSq]
      ring
    _ ≤ ∑ q ∈ selbergSqrtZetaCompleteRatioSupport X,
          selbergSqrtZetaCompleteRatioCoeff X q ^ 2 := hsingle
    _ = ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
          selbergSqrtZetaCompleteProductCoeff X n ^ 2 :=
      sum_sq_selbergSqrtZetaCompleteRatioCoeff_eq_productCoeff X
    _ ≤ (19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X :=
      sum_sq_selbergSqrtZetaCompleteProductCoeff_le_nineteen_fourths_add_high
        hX hlarge

end HardyTheorem
