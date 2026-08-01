import HardyTheorem.SelbergSqrtZetaExcessiveReducedPairEndpoint
import HardyTheorem.SelbergSqrtZetaSignedReducedPairCompleteCancellation

/-!
# Lower bound for the reduced-pair split energy

The complete ratio model contains the unit product coefficient.  The
multiplicative Parseval identity therefore forces its square energy to be at
least one.  Once the complete taper box embeds in the actual signed support,
the factor two in the split-energy definition gives an unconditional lower
bound of two.
-/

open scoped BigOperators

namespace HardyTheorem

private theorem completeRatioSupport_subset_signedRationalSupport
    {N X : ℕ} (hN : 1 ≤ N) :
    selbergSqrtZetaCompleteRatioSupport X ⊆
      selbergSqrtZetaSignedRationalSupport N X := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
  apply Finset.mem_image.mpr
  refine ⟨(1, (p.2, p.1)), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hN⟩,
        Finset.mem_product.mpr ⟨hp2, hp1⟩⟩
  · simp [selbergSqrtZetaSignedRationalKey,
      selbergSqrtZetaCompleteRatioKey]

private theorem one_le_sum_sq_completeProductCoeff
    {X : ℕ} (hX : 1 ≤ X) :
    1 ≤ ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
      selbergSqrtZetaCompleteProductCoeff X n ^ 2 := by
  have honeMem : 1 ∈ selbergSqrtZetaCompleteProductSupport X := by
    apply Finset.mem_image.mpr
    refine ⟨(1, 1), ?_, by simp [selbergSqrtZetaCompleteProductKey]⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hX⟩,
        Finset.mem_Icc.mpr ⟨by omega, hX⟩⟩
  have honeCoeff : selbergSqrtZetaCompleteProductCoeff X 1 = 1 := by
    rw [selbergSqrtZetaCompleteProductCoeff_eq_collected_div_sqrt
      (by omega) hX]
    simp
  calc
    1 = selbergSqrtZetaCompleteProductCoeff X 1 ^ 2 := by
      rw [honeCoeff]
      norm_num
    _ ≤ ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
        selbergSqrtZetaCompleteProductCoeff X n ^ 2 := by
      exact Finset.single_le_sum (fun n _hn => sq_nonneg _) honeMem

private theorem inv_mul_completeTerm_sq_eq_ratioCoeff_sq_lower
    {N X a b : ℕ} (hNX : X ≤ N) (hX : 0 < X)
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    (((a * b : ℕ) : ℝ)⁻¹ *
        selbergSqrtZetaSignedReducedRayCompleteTerm N X a b ^ 2) =
      selbergSqrtZetaCompleteRatioCoeff X ((a : ℚ) / (b : ℚ)) ^ 2 := by
  rw [selbergSqrtZetaCompleteRatioCoeff_reduced_eq_completeTerm
    hNX hX ha hb hab]
  rw [mul_pow, inv_pow, Real.sq_sqrt]
  · simp only [Nat.cast_mul]
  · positivity

private theorem one_le_sum_sq_completeRatioCoeff_over_reducedSupport
    {N X : ℕ} (hX : 1 ≤ X) (hNX : X ≤ N) :
    1 ≤ ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
      selbergSqrtZetaCompleteRatioCoeff X
        (selbergSqrtZetaSignedReducedPairKey p) ^ 2 := by
  have hN : 1 ≤ N := hX.trans hNX
  have hsubset := completeRatioSupport_subset_signedRationalSupport
    (N := N) (X := X) hN
  calc
    1 ≤ ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
        selbergSqrtZetaCompleteProductCoeff X n ^ 2 :=
      one_le_sum_sq_completeProductCoeff hX
    _ = ∑ q ∈ selbergSqrtZetaCompleteRatioSupport X,
        selbergSqrtZetaCompleteRatioCoeff X q ^ 2 :=
      (sum_sq_selbergSqrtZetaCompleteRatioCoeff_eq_productCoeff X).symm
    _ ≤ ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        selbergSqrtZetaCompleteRatioCoeff X q ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro q _hq _hnot
        positivity)
    _ = ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        selbergSqrtZetaCompleteRatioCoeff X
          (selbergSqrtZetaSignedReducedPairKey p) ^ 2 :=
      sum_selbergSqrtZetaSignedRationalSupport_eq_reducedPairSupport
        N X (fun q => selbergSqrtZetaCompleteRatioCoeff X q ^ 2)

/-- The complete diagonal contribution prevents the current split energy
from satisfying any upper budget below two. -/
theorem two_le_selbergSqrtZetaSignedReducedPairSplitEnergy
    {N X : ℕ} (hX : 1 ≤ X) (hNX : X ≤ N) :
    2 ≤ selbergSqrtZetaSignedReducedPairSplitEnergy N X := by
  have hratio :
      1 ≤ ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        selbergSqrtZetaCompleteRatioCoeff X
          (selbergSqrtZetaSignedReducedPairKey p) ^ 2 :=
    one_le_sum_sq_completeRatioCoeff_over_reducedSupport hX hNX
  have hpointwise :
      ∀ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        2 * selbergSqrtZetaCompleteRatioCoeff X
            (selbergSqrtZetaSignedReducedPairKey p) ^ 2 ≤
          (2 *
              (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
                ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                  selbergSqrtZetaSignedReducedRayCompleteTerm
                    N X p.1 p.2 ^ 2)) +
            2 *
              (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
                ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                  selbergSqrtZetaSignedReducedRayBoundaryTerm
                    N X p.1 p.2 ^ 2))) := by
    intro p hp
    have hpFacts :=
      selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
    have hcomplete :
        (((p.1 * p.2 : ℕ) : ℝ)⁻¹ *
            selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2 ^ 2) =
          selbergSqrtZetaCompleteRatioCoeff X
            (selbergSqrtZetaSignedReducedPairKey p) ^ 2 := by
      simpa only [selbergSqrtZetaSignedReducedPairKey] using
        inv_mul_completeTerm_sq_eq_ratioCoeff_sq_lower
          hNX (by omega) hpFacts.1 hpFacts.2.1 hpFacts.2.2.1
    have hweight :
        (1 : ℝ) ≤ ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    rw [← hcomplete]
    have hmainNonneg :
        0 ≤ (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 ^ 2 := by
      positivity
    have hboundaryNonneg :
        0 ≤ 2 *
          (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
            ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2 ^ 2)) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_right hweight hmainNonneg]
  unfold selbergSqrtZetaSignedReducedPairSplitEnergy
  calc
    2 ≤ 2 *
        (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
          selbergSqrtZetaCompleteRatioCoeff X
            (selbergSqrtZetaSignedReducedPairKey p) ^ 2) := by
      linarith
    _ = ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        2 * selbergSqrtZetaCompleteRatioCoeff X
          (selbergSqrtZetaSignedReducedPairKey p) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (2 *
            (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                selbergSqrtZetaSignedReducedRayCompleteTerm
                  N X p.1 p.2 ^ 2)) +
          2 *
            (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                selbergSqrtZetaSignedReducedRayBoundaryTerm
                  N X p.1 p.2 ^ 2))) :=
      Finset.sum_le_sum hpointwise

/-- In the nonempty complete-taper range, the numerical split-energy
hypothesis used by the old excessive-window endpoint is impossible. -/
theorem not_selbergSqrtZetaSignedReducedPairSplitEnergy_le_one_div_768
    {N X : ℕ} (hX : 1 ≤ X) (hNX : X ≤ N) :
    ¬ selbergSqrtZetaSignedReducedPairSplitEnergy N X ≤ 1 / 768 := by
  intro hsmall
  have hlower :=
    two_le_selbergSqrtZetaSignedReducedPairSplitEnergy hX hNX
  norm_num at hsmall
  linarith

end HardyTheorem
