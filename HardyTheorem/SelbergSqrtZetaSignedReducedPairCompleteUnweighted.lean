import HardyTheorem.SelbergSqrtZetaSignedReducedPairCompleteCancellation
import HardyTheorem.SelbergSqrtZetaSignedRationalNoncarrierEnergy

/-!
# Unweighted Parseval after deleting the rational carrier

The local-separation energy carries a geometric weight of size up to `X^2+1`.
That weight is irrelevant for the plain coefficient energy.  This file keeps
the reduced-pair complete contribution unweighted, deletes `(1, 1)` before
Parseval, and identifies the result exactly with the product-side energy minus
the single ratio-one coefficient.
-/

open scoped BigOperators

namespace HardyTheorem

/-- Every ratio represented by the complete `X`-box occurs in the signed
rational support as soon as the zeta cutoff contains that box. -/
theorem selbergSqrtZetaCompleteRatioSupport_subset_signedRationalSupport
    {N X : ℕ} (hNX : X ≤ N) (hX : 0 < X) :
    selbergSqrtZetaCompleteRatioSupport X ⊆
      selbergSqrtZetaSignedRationalSupport N X := by
  classical
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  have hpBox := Finset.mem_product.mp hp
  have hpNum := Finset.mem_Icc.mp hpBox.1
  have hpDen := Finset.mem_Icc.mp hpBox.2
  apply Finset.mem_image.mpr
  refine ⟨(p.2, (1, p.1)), ?_, ?_⟩
  · change
      (p.2, (1, p.1)) ∈
        (Finset.Icc 1 N).product
          ((Finset.Icc 1 X).product (Finset.Icc 1 X))
    have hm : p.2 ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨hpDen.1, hpDen.2.trans hNX⟩
    have hd : 1 ∈ Finset.Icc 1 X :=
      Finset.mem_Icc.mpr ⟨le_rfl, hX⟩
    exact Finset.mem_product.mpr
      ⟨hm, Finset.mem_product.mpr ⟨hd, hpBox.1⟩⟩
  · simp [selbergSqrtZetaSignedRationalKey,
      selbergSqrtZetaCompleteRatioKey]

private theorem selbergSqrtZetaCompleteRatioCoeff_eq_zero_of_not_mem
    {X : ℕ} {q : ℚ}
    (hq : q ∉ selbergSqrtZetaCompleteRatioSupport X) :
    selbergSqrtZetaCompleteRatioCoeff X q = 0 := by
  classical
  unfold selbergSqrtZetaCompleteRatioCoeff
    selbergSqrtZetaCompleteRatioFiber
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  exact False.elim (hq (Finset.mem_image.mpr ⟨p, hp'.1, hp'.2⟩))

private theorem inv_mul_completeTerm_sq_eq_ratioCoeff_sq_unweighted
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

private theorem sum_completeRatioCoeff_sq_noncarrier_eq_erase_complete
    {N X : ℕ} (hNX : X ≤ N) (hX : 0 < X) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        selbergSqrtZetaCompleteRatioCoeff X q ^ 2) =
      ∑ q ∈ (selbergSqrtZetaCompleteRatioSupport X).erase 1,
        selbergSqrtZetaCompleteRatioCoeff X q ^ 2 := by
  classical
  have hsubset :
      (selbergSqrtZetaCompleteRatioSupport X).erase 1 ⊆
        selbergSqrtZetaSignedRationalNoncarrierSupport N X := by
    intro q hq
    have hq' := Finset.mem_erase.mp hq
    unfold selbergSqrtZetaSignedRationalNoncarrierSupport
    exact Finset.mem_erase.mpr
      ⟨hq'.1,
        selbergSqrtZetaCompleteRatioSupport_subset_signedRationalSupport
          hNX hX hq'.2⟩
  symm
  exact Finset.sum_subset hsubset (by
    intro q hqSigned hqNotCompleteErase
    have hqNe : q ≠ 1 := by
      exact (Finset.mem_erase.mp hqSigned).1
    have hqNotComplete : q ∉ selbergSqrtZetaCompleteRatioSupport X := by
      intro hqComplete
      exact hqNotCompleteErase (Finset.mem_erase.mpr ⟨hqNe, hqComplete⟩)
    rw [selbergSqrtZetaCompleteRatioCoeff_eq_zero_of_not_mem hqNotComplete]
    simp)

/-- Exact unweighted carrier-deleted Parseval identity.  The reduced-pair
complete contribution is collected with its sharp `1/(a*b)` normalization;
after deleting `(1,1)`, adding back the ratio-one square gives exactly the
one-dimensional product energy.  No local-separation factor occurs. -/
theorem
    sum_selbergSqrtZetaSignedReducedPairCompleteUnweighted_erase_one_add_carrier_eq_productEnergy
    {N X : ℕ} (hNX : X ≤ N) (hX : 0 < X) :
    (∑ p ∈
        (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 ^ 2) +
        selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 =
      ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
        selbergSqrtZetaCompleteProductCoeff X n ^ 2 := by
  classical
  have hN : 1 ≤ N := by omega
  have hX1 : 1 ≤ X := by omega
  have hreindex :=
    sum_selbergSqrtZetaSignedRationalNoncarrierSupport_eq_reducedPairSupport_erase_one
      hN hX1 (fun q => selbergSqrtZetaCompleteRatioCoeff X q ^ 2)
  have hone : (1 : ℚ) ∈ selbergSqrtZetaCompleteRatioSupport X := by
    apply Finset.mem_image.mpr
    refine ⟨(1, 1), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hX⟩,
          Finset.mem_Icc.mpr ⟨by omega, hX⟩⟩
    · simp [selbergSqrtZetaCompleteRatioKey]
  calc
    (∑ p ∈
        (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 ^ 2) +
        selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 =
        (∑ p ∈
          (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
          selbergSqrtZetaCompleteRatioCoeff X
            (selbergSqrtZetaSignedReducedPairKey p) ^ 2) +
          selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      have hpFull :
          p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X :=
        Finset.mem_of_mem_erase hp
      have hpFacts :=
        selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hpFull
      simpa only [selbergSqrtZetaSignedReducedPairKey] using
        inv_mul_completeTerm_sq_eq_ratioCoeff_sq_unweighted
          hNX hX hpFacts.1 hpFacts.2.1 hpFacts.2.2.1
    _ = (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
          selbergSqrtZetaCompleteRatioCoeff X q ^ 2) +
        selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 := by
      rw [hreindex]
    _ = (∑ q ∈ (selbergSqrtZetaCompleteRatioSupport X).erase 1,
          selbergSqrtZetaCompleteRatioCoeff X q ^ 2) +
        selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 := by
      rw [sum_completeRatioCoeff_sq_noncarrier_eq_erase_complete hNX hX]
    _ = ∑ q ∈ selbergSqrtZetaCompleteRatioSupport X,
          selbergSqrtZetaCompleteRatioCoeff X q ^ 2 :=
      Finset.sum_erase_add _ _ hone
    _ = ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
          selbergSqrtZetaCompleteProductCoeff X n ^ 2 :=
      sum_sq_selbergSqrtZetaCompleteRatioCoeff_eq_productCoeff X

/-- Subtractive form of the exact unweighted carrier-deleted Parseval
identity. -/
theorem
    sum_selbergSqrtZetaSignedReducedPairCompleteUnweighted_erase_one_eq_productEnergy_sub_carrier
    {N X : ℕ} (hNX : X ≤ N) (hX : 0 < X) :
    (∑ p ∈
        (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 ^ 2) =
      (∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
        selbergSqrtZetaCompleteProductCoeff X n ^ 2) -
        selbergSqrtZetaCompleteRatioCoeff X 1 ^ 2 := by
  linarith only
    [sum_selbergSqrtZetaSignedReducedPairCompleteUnweighted_erase_one_add_carrier_eq_productEnergy
      hNX hX]

/-- Sharp factor-free upper bound obtained by dropping only the nonnegative
deleted carrier square from the exact identity. -/
theorem
    sum_selbergSqrtZetaSignedReducedPairCompleteUnweighted_erase_one_le_productEnergy
    {N X : ℕ} (hNX : X ≤ N) (hX : 0 < X) :
    (∑ p ∈
        (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 ^ 2) ≤
      ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
        selbergSqrtZetaCompleteProductCoeff X n ^ 2 := by
  nlinarith only
    [sum_selbergSqrtZetaSignedReducedPairCompleteUnweighted_erase_one_add_carrier_eq_productEnergy
      hNX hX,
    sq_nonneg (selbergSqrtZetaCompleteRatioCoeff X 1)]

end HardyTheorem
