import HardyTheorem.SelbergSqrtZetaSignedCoprimeRayLogExpansion

/-!
# One-coefficient reindexing on a reduced coprime ray

This file identifies a single rationally collected coefficient at the reduced
ratio `a / b` with the finite sum over the positive scales on the coprime ray
`(a, b)`.  It is the coefficient-level counterpart of the existing
off-diagonal energy reindexing.
-/

open scoped BigOperators

namespace HardyTheorem

private theorem selbergSqrtZetaSignedDenominatorCollectedCoeff_im_eq_zero
    (N X k : ℕ) :
    (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k).im = 0 := by
  classical
  unfold selbergSqrtZetaSignedDenominatorCollectedCoeff
    selbergSqrtZetaSignedDenominatorCoeff
  simp

private theorem selbergSqrtZetaSignedNumeratorCoeff_im_eq_zero
    (X l : ℕ) :
    (selbergSqrtZetaSignedNumeratorCoeff X l).im = 0 := by
  unfold selbergSqrtZetaSignedNumeratorCoeff
  simp

/-- At a reduced ratio `a / b`, the rationally collected coefficient is
exactly the finite sum of the pair coefficients over the positive scales on
the coprime ray `(a,b)`. -/
theorem
    selbergSqrtZetaSignedRationalCoeff_reduced_eq_coprimeRayScaleSum
    (N X a b : ℕ) (hab : Nat.Coprime a b) (hb : 0 < b) :
    selbergSqrtZetaSignedRationalCoeff N X ((a : ℚ) / (b : ℚ)) =
      ∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
        (selbergSqrtZetaSignedRationalPairCoeff N X
          (b * d, a * d) : ℂ) := by
  classical
  rw [selbergSqrtZetaSignedRationalCoeff_eq_denominatorCollected]
  symm
  refine Finset.sum_bij (fun d _hd => (b * d, a * d)) ?_ ?_ ?_ ?_
  · intro d hd
    rcases Finset.mem_filter.mp hd with ⟨_hdRange, hdPos, hpair⟩
    apply Finset.mem_filter.mpr
    refine ⟨hpair, ?_⟩
    unfold selbergSqrtZetaSignedDenominatorNumeratorKey
    apply (div_eq_div_iff ?_ ?_).2
    · push_cast
      ring
    · exact_mod_cast (Nat.mul_pos hb hdPos).ne'
    · exact_mod_cast hb.ne'
  · intro d hd e he hde
    have hfst : b * d = b * e := congrArg Prod.fst hde
    exact Nat.eq_of_mul_eq_mul_left hb hfst
  · rintro ⟨k, l⟩ hp
    have hp' := Finset.mem_filter.mp hp
    have hpSupport := hp'.1
    have hpKey := hp'.2
    have hk : 0 < k :=
      selbergSqrtZetaSignedDenominator_pos_of_mem
        (Finset.mem_product.mp hpSupport).1
    have hcrossQ : (l : ℚ) * (b : ℚ) = (a : ℚ) * (k : ℚ) := by
      exact
        (div_eq_div_iff (by exact_mod_cast hk.ne')
          (by exact_mod_cast hb.ne')).mp hpKey
    have hcross : l * b = a * k := by
      exact_mod_cast hcrossQ
    have hbDvd : b ∣ k := by
      apply hab.symm.dvd_of_dvd_mul_left
      rw [← hcross]
      exact dvd_mul_left b l
    let d := k / b
    have hkFactor : k = b * d := by
      exact (Nat.mul_div_cancel' hbDvd).symm
    have hlFactor : l = a * d := by
      apply Nat.eq_of_mul_eq_mul_right hb
      simpa only [hkFactor, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hcross
    have hdPos : 0 < d := by
      have hdNe : d ≠ 0 := by
        intro hd
        rw [hd, mul_zero] at hkFactor
        omega
      exact Nat.pos_of_ne_zero hdNe
    have hkBound :
        k ≤ N * X :=
      (selbergSqrtZetaSignedDenominator_bounds_of_mem
        (Finset.mem_product.mp hpSupport).1).2
    have hdLeMul : d ≤ b * d := by
      have h :=
        Nat.mul_le_mul_right d (Nat.succ_le_iff.mpr hb)
      norm_num at h ⊢
      exact h
    have hdBound : d ≤ N * X := by
      calc
        d ≤ b * d := hdLeMul
        _ = k := hkFactor.symm
        _ ≤ N * X := hkBound
    refine ⟨d, Finset.mem_filter.mpr ⟨
      Finset.mem_range.mpr (Nat.lt_succ_of_le hdBound), hdPos, ?_⟩, ?_⟩
    · simpa only [← hkFactor, ← hlFactor] using hpSupport
    · simp only [hkFactor, hlFactor]
  · intro d hd
    apply Complex.ext
    · simp only [Complex.ofReal_re, Complex.mul_re,
        selbergSqrtZetaSignedDenominatorCollectedCoeff_im_eq_zero,
        selbergSqrtZetaSignedNumeratorCoeff_im_eq_zero, mul_zero, sub_zero,
        selbergSqrtZetaSignedRationalPairCoeff]
    · simp only [Complex.ofReal_im, Complex.mul_im,
        selbergSqrtZetaSignedDenominatorCollectedCoeff_im_eq_zero,
        selbergSqrtZetaSignedNumeratorCoeff_im_eq_zero, zero_mul, mul_zero,
        add_zero]

end HardyTheorem
