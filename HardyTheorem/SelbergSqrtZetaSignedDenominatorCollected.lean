import HardyTheorem.SelbergSqrtZetaSignedRationalCollected

/-!
# Denominator collection of the signed square-root-zeta coefficients

The signed rational key of a triple `(m,d,l)` is `l / (m*d)`.  This module
first collects the two denominator variables at `k = m*d`, keeps the numerator
variable separate, and then recovers the existing rational coefficient by a
finite convolution over the pairs `(k,l)` satisfying `l/k = q`.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The finite support of the two denominator variables `(m,d)`. -/
noncomputable def selbergSqrtZetaSignedDenominatorRawSupport
    (N X : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N).product (Finset.Icc 1 X)

/-- The positive denominator key `k = m*d`. -/
def selbergSqrtZetaSignedDenominatorKey (p : ℕ × ℕ) : ℕ :=
  p.1 * p.2

/-- The finite support of denominator keys `k = m*d`. -/
noncomputable def selbergSqrtZetaSignedDenominatorSupport
    (N X : ℕ) : Finset ℕ :=
  (selbergSqrtZetaSignedDenominatorRawSupport N X).image
    selbergSqrtZetaSignedDenominatorKey

/-- The raw denominator pairs `(m,d)` whose product is `k`. -/
noncomputable def selbergSqrtZetaSignedDenominatorFiber
    (N X k : ℕ) : Finset (ℕ × ℕ) :=
  (selbergSqrtZetaSignedDenominatorRawSupport N X).filter
    (fun p => selbergSqrtZetaSignedDenominatorKey p = k)

/-- The coefficient contributed by one denominator pair `(m,d)`. -/
noncomputable def selbergSqrtZetaSignedDenominatorCoeff
    (X : ℕ) (p : ℕ × ℕ) : ℂ :=
  (selbergSqrtZetaTaperedCoeff X p.2 : ℂ) *
    ((Real.sqrt p.1 : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt p.2 : ℝ) : ℂ)⁻¹

/-- The coefficient collected at the positive denominator `k = m*d`. -/
noncomputable def selbergSqrtZetaSignedDenominatorCollectedCoeff
    (N X k : ℕ) : ℂ :=
  ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
    selbergSqrtZetaSignedDenominatorCoeff X p

/-- The finite support of the numerator variable `l`. -/
noncomputable def selbergSqrtZetaSignedNumeratorSupport
    (X : ℕ) : Finset ℕ :=
  Finset.Icc 1 X

/-- The coefficient contributed by the numerator variable `l`. -/
noncomputable def selbergSqrtZetaSignedNumeratorCoeff
    (X l : ℕ) : ℂ :=
  (selbergSqrtZetaTaperedCoeff X l : ℂ) *
    ((Real.sqrt l : ℝ) : ℂ)⁻¹

/-- The normalized rational key `l/k` of a denominator-numerator pair. -/
noncomputable def selbergSqrtZetaSignedDenominatorNumeratorKey
    (p : ℕ × ℕ) : ℚ :=
  (p.2 : ℚ) / (p.1 : ℚ)

/-- The finite denominator-numerator support `(k,l)`. -/
noncomputable def selbergSqrtZetaSignedDenominatorNumeratorSupport
    (N X : ℕ) : Finset (ℕ × ℕ) :=
  (selbergSqrtZetaSignedDenominatorSupport N X).product
    (selbergSqrtZetaSignedNumeratorSupport X)

/-- The finite `(k,l)` fiber satisfying `l/k = q`. -/
noncomputable def selbergSqrtZetaSignedDenominatorNumeratorFiber
    (N X : ℕ) (q : ℚ) : Finset (ℕ × ℕ) :=
  (selbergSqrtZetaSignedDenominatorNumeratorSupport N X).filter
    (fun p => selbergSqrtZetaSignedDenominatorNumeratorKey p = q)

/-- Every denominator key in the collected support is strictly positive. -/
theorem selbergSqrtZetaSignedDenominator_pos_of_mem
    {N X k : ℕ}
    (hk : k ∈ selbergSqrtZetaSignedDenominatorSupport N X) :
    0 < k := by
  rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
  have hp' := Finset.mem_product.mp hp
  exact Nat.mul_pos
    (Finset.mem_Icc.mp hp'.1).1
    (Finset.mem_Icc.mp hp'.2).1

/-- The signed triple coefficient factors exactly into its denominator and
numerator coefficients. -/
theorem selbergSqrtZetaSignedPhaseCoeff_eq_denominator_mul_numerator
    (X m d l : ℕ) :
    selbergSqrtZetaSignedPhaseCoeff X (m, d, l) =
      selbergSqrtZetaSignedDenominatorCoeff X (m, d) *
        selbergSqrtZetaSignedNumeratorCoeff X l := by
  unfold selbergSqrtZetaSignedPhaseCoeff
    selbergSqrtZetaSignedDenominatorCoeff
    selbergSqrtZetaSignedNumeratorCoeff
  ring

/-- For a supported numerator `l`, collecting the triples with fixed
denominator-numerator pair `(k,l)` gives the product of the collected
denominator coefficient and the numerator coefficient. -/
theorem sum_selbergSqrtZetaSignedPhaseCoeff_fixed_denominatorNumerator
    (N X k l : ℕ)
    (hl : l ∈ selbergSqrtZetaSignedNumeratorSupport X) :
    (∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
        (fun p => (selbergSqrtZetaSignedDenominatorKey (p.1, p.2.1), p.2.2) =
          (k, l)),
        selbergSqrtZetaSignedPhaseCoeff X p) =
      selbergSqrtZetaSignedDenominatorCollectedCoeff N X k *
        selbergSqrtZetaSignedNumeratorCoeff X l := by
  classical
  let A := Finset.Icc 1 N
  let B := Finset.Icc 1 X
  have hlB : l ∈ B := by
    simpa only [B, selbergSqrtZetaSignedNumeratorSupport] using hl
  calc
    (∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
        (fun p =>
          (selbergSqrtZetaSignedDenominatorKey (p.1, p.2.1), p.2.2) =
            (k, l)),
        selbergSqrtZetaSignedPhaseCoeff X p) =
        ∑ m ∈ A, ∑ dl ∈ B.product B,
          if
            (selbergSqrtZetaSignedDenominatorKey (m, dl.1), dl.2) =
              (k, l)
          then selbergSqrtZetaSignedPhaseCoeff X (m, dl)
          else 0 := by
      unfold selbergSqrtZetaSignedPhaseSupport
      rw [Finset.sum_filter]
      exact Finset.sum_product A (B.product B) _
    _ = ∑ m ∈ A, ∑ d ∈ B, ∑ l' ∈ B,
          if
            (selbergSqrtZetaSignedDenominatorKey (m, d), l') = (k, l)
          then selbergSqrtZetaSignedPhaseCoeff X (m, d, l')
          else 0 := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact Finset.sum_product B B _
    _ = ∑ m ∈ A, ∑ d ∈ B,
          if selbergSqrtZetaSignedDenominatorKey (m, d) = k
          then selbergSqrtZetaSignedPhaseCoeff X (m, d, l)
          else 0 := by
      apply Finset.sum_congr rfl
      intro m _hm
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hmd : selbergSqrtZetaSignedDenominatorKey (m, d) = k
      · simp only [hmd, true_and, if_true, Prod.mk.injEq]
        rw [Finset.sum_eq_single l]
        · simp
        · intro l' _hl' hne
          simp [hne]
        · exact fun hnot => (hnot hlB).elim
      · simp [hmd]
    _ = ∑ m ∈ A, ∑ d ∈ B,
          if selbergSqrtZetaSignedDenominatorKey (m, d) = k
          then
            selbergSqrtZetaSignedDenominatorCoeff X (m, d) *
              selbergSqrtZetaSignedNumeratorCoeff X l
          else 0 := by
      apply Finset.sum_congr rfl
      intro m _hm
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hmd : selbergSqrtZetaSignedDenominatorKey (m, d) = k
      · simp only [hmd, if_true]
        exact
          selbergSqrtZetaSignedPhaseCoeff_eq_denominator_mul_numerator
            X m d l
      · simp [hmd]
    _ = ∑ md ∈ A.product B,
          if selbergSqrtZetaSignedDenominatorKey md = k
          then
            selbergSqrtZetaSignedDenominatorCoeff X md *
              selbergSqrtZetaSignedNumeratorCoeff X l
          else 0 := by
      exact
        (Finset.sum_product A B
          (fun md : ℕ × ℕ =>
            if selbergSqrtZetaSignedDenominatorKey md = k
            then
              selbergSqrtZetaSignedDenominatorCoeff X md *
                selbergSqrtZetaSignedNumeratorCoeff X l
            else (0 : ℂ))).symm
    _ = selbergSqrtZetaSignedDenominatorCollectedCoeff N X k *
          selbergSqrtZetaSignedNumeratorCoeff X l := by
      unfold selbergSqrtZetaSignedDenominatorCollectedCoeff
        selbergSqrtZetaSignedDenominatorFiber
        selbergSqrtZetaSignedDenominatorRawSupport
      rw [Finset.sum_mul, Finset.sum_filter]

/-- The existing signed rational coefficient is exactly the finite convolution
of the collected denominator coefficient with the numerator coefficient over
the pairs `(k,l)` satisfying `l/k = q`. -/
theorem selbergSqrtZetaSignedRationalCoeff_eq_denominatorCollected
    (N X : ℕ) (q : ℚ) :
    selbergSqrtZetaSignedRationalCoeff N X q =
      ∑ p ∈ selbergSqrtZetaSignedDenominatorNumeratorFiber N X q,
        selbergSqrtZetaSignedDenominatorCollectedCoeff N X p.1 *
          selbergSqrtZetaSignedNumeratorCoeff X p.2 := by
  classical
  let P := selbergSqrtZetaSignedRationalFiber N X q
  let K := selbergSqrtZetaSignedDenominatorNumeratorFiber N X q
  let g : ℕ × (ℕ × ℕ) → ℕ × ℕ := fun p =>
    (selbergSqrtZetaSignedDenominatorKey (p.1, p.2.1), p.2.2)
  let f : ℕ × (ℕ × ℕ) → ℂ := selbergSqrtZetaSignedPhaseCoeff X
  have hmaps : ∀ p ∈ P, g p ∈ K := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpSupport := hp'.1
    have hpKey := hp'.2
    have hm :
        p.1 ∈ Finset.Icc 1 N :=
      (Finset.mem_product.mp hpSupport).1
    have hdl :
        p.2 ∈ (Finset.Icc 1 X).product (Finset.Icc 1 X) :=
      (Finset.mem_product.mp hpSupport).2
    have hd : p.2.1 ∈ Finset.Icc 1 X :=
      (Finset.mem_product.mp hdl).1
    have hl : p.2.2 ∈ Finset.Icc 1 X :=
      (Finset.mem_product.mp hdl).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_image.mpr
        exact ⟨(p.1, p.2.1),
          Finset.mem_product.mpr ⟨hm, hd⟩, rfl⟩
      · exact hl
    · simpa only [g, selbergSqrtZetaSignedDenominatorNumeratorKey,
        selbergSqrtZetaSignedDenominatorKey,
        selbergSqrtZetaSignedRationalKey] using hpKey
  have hfiber :
      (∑ p ∈ P, f p) =
        ∑ kl ∈ K, ∑ p ∈ P.filter (fun p => g p = kl), f p := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  unfold selbergSqrtZetaSignedRationalCoeff
  calc
    (∑ p ∈ selbergSqrtZetaSignedRationalFiber N X q,
        selbergSqrtZetaSignedPhaseCoeff X p) =
        ∑ p ∈ P, f p := by rfl
    _ = ∑ kl ∈ K, ∑ p ∈ P.filter (fun p => g p = kl), f p := hfiber
    _ = ∑ kl ∈ K,
        selbergSqrtZetaSignedDenominatorCollectedCoeff N X kl.1 *
          selbergSqrtZetaSignedNumeratorCoeff X kl.2 := by
      apply Finset.sum_congr rfl
      intro kl hkl
      have hkl' := Finset.mem_filter.mp hkl
      have hklSupport := hkl'.1
      have hklKey := hkl'.2
      have hl :
          kl.2 ∈ selbergSqrtZetaSignedNumeratorSupport X :=
        (Finset.mem_product.mp hklSupport).2
      have hfilter :
          P.filter (fun p => g p = kl) =
            (selbergSqrtZetaSignedPhaseSupport N X).filter
              (fun p =>
                (selbergSqrtZetaSignedDenominatorKey (p.1, p.2.1), p.2.2) =
                  kl) := by
        ext p
        change
          (p ∈ (selbergSqrtZetaSignedRationalFiber N X q).filter
              (fun p =>
                (selbergSqrtZetaSignedDenominatorKey (p.1, p.2.1), p.2.2) =
                  kl)) ↔
            p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
              (fun p =>
                (selbergSqrtZetaSignedDenominatorKey (p.1, p.2.1), p.2.2) =
                  kl)
        simp only [Finset.mem_filter,
          selbergSqrtZetaSignedRationalFiber]
        constructor
        · intro hp
          exact ⟨hp.1.1, hp.2⟩
        · intro hp
          rcases hp with ⟨hpSupport, rfl⟩
          refine ⟨⟨hpSupport, ?_⟩, rfl⟩
          simpa only [selbergSqrtZetaSignedRationalKey,
            selbergSqrtZetaSignedDenominatorNumeratorKey,
            selbergSqrtZetaSignedDenominatorKey] using hklKey
      rw [hfilter]
      exact
        sum_selbergSqrtZetaSignedPhaseCoeff_fixed_denominatorNumerator
          N X kl.1 kl.2 hl
    _ = ∑ p ∈ selbergSqrtZetaSignedDenominatorNumeratorFiber N X q,
        selbergSqrtZetaSignedDenominatorCollectedCoeff N X p.1 *
          selbergSqrtZetaSignedNumeratorCoeff X p.2 := by rfl

end HardyTheorem
