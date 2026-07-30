import HardyTheorem.SelbergSqrtZetaSignedRationalCoprimeRayReindex

/-!
# Exact signed Selberg coefficients on one coprime ray

The coprime-ray reindexing reduces the rational coefficient off-diagonal to
pairs `(b*d, a*d)` and `(b*e, a*e)`.  This file opens the actual pair
coefficient at one scale.  The denominator variables remain collected in one
finite real sum, while the numerator contributes its signed tapered
coefficient divided by the square root of the scaled numerator.

This is the form needed by a subsequent one-dimensional scale estimate: the
sign of the numerator factor is exactly the sign of the taper, and the
off-diagonal scale correlation is a square minus its diagonal.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The real denominator coefficient after collecting all factorizations
`m*r = k` in the actual finite support. -/
noncomputable def selbergSqrtZetaSignedDenominatorCollectedRealCoeff
    (N X k : ℕ) : ℝ :=
  ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
    selbergSqrtZetaTaperedCoeff X p.2 *
      (Real.sqrt p.1)⁻¹ * (Real.sqrt p.2)⁻¹

/-- The real numerator factor at `l`: the signed taper divided by `sqrt l`. -/
noncomputable def selbergSqrtZetaSignedNumeratorRealCoeff
    (X l : ℕ) : ℝ :=
  selbergSqrtZetaTaperedCoeff X l * (Real.sqrt l)⁻¹

/-- Taking the real part of the complex collected denominator coefficient
gives the explicit finite real factorization sum. -/
theorem selbergSqrtZetaSignedDenominatorCollectedCoeff_re_eq
    (N X k : ℕ) :
    (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k).re =
      selbergSqrtZetaSignedDenominatorCollectedRealCoeff N X k := by
  classical
  unfold selbergSqrtZetaSignedDenominatorCollectedCoeff
    selbergSqrtZetaSignedDenominatorCollectedRealCoeff
    selbergSqrtZetaSignedDenominatorCoeff
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Complex.ofReal_inv, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rfl

/-- Taking the real part of the complex numerator coefficient exposes the
signed taper and its positive square-root normalization. -/
theorem selbergSqrtZetaSignedNumeratorCoeff_re_eq
    (X l : ℕ) :
    (selbergSqrtZetaSignedNumeratorCoeff X l).re =
      selbergSqrtZetaSignedNumeratorRealCoeff X l := by
  unfold selbergSqrtZetaSignedNumeratorCoeff
    selbergSqrtZetaSignedNumeratorRealCoeff
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  rfl

/-- Exact factorization of the actual pair coefficient along the ray
`(a,b)` at scale `d`. -/
theorem selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq
    (N X a b d : ℕ) :
    selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d) =
      selbergSqrtZetaSignedDenominatorCollectedRealCoeff N X (b * d) *
        selbergSqrtZetaSignedNumeratorRealCoeff X (a * d) := by
  unfold selbergSqrtZetaSignedRationalPairCoeff
  rw [selbergSqrtZetaSignedDenominatorCollectedCoeff_re_eq,
    selbergSqrtZetaSignedNumeratorCoeff_re_eq]

/-- Fully expanded ray coefficient.  The first factor is the collected
denominator sum and the second factor displays the signed numerator taper. -/
theorem selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq_explicit
    (N X a b d : ℕ) :
    selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d) =
      (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X (b * d),
          selbergSqrtZetaTaperedCoeff X p.2 *
            (Real.sqrt p.1)⁻¹ * (Real.sqrt p.2)⁻¹) *
        (selbergSqrtZetaTaperedCoeff X (a * d) *
          (Real.sqrt (a * d))⁻¹) := by
  rw [selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq]
  simp only [selbergSqrtZetaSignedDenominatorCollectedRealCoeff,
    selbergSqrtZetaSignedNumeratorRealCoeff, Nat.cast_mul]

/-- The product of two actual coefficients on one ray exposes the product of
the two signed numerator tapers.  This is the exact form in which cancellation
or one-dimensional Cauchy estimates can use their signs. -/
theorem
    selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_product_eq_explicit
    (N X a b d e : ℕ) :
    selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d) *
        selbergSqrtZetaSignedRationalPairCoeff N X (b * e, a * e) =
      (selbergSqrtZetaSignedDenominatorCollectedRealCoeff N X (b * d) *
        selbergSqrtZetaSignedDenominatorCollectedRealCoeff N X (b * e)) *
      ((selbergSqrtZetaTaperedCoeff X (a * d) *
        selbergSqrtZetaTaperedCoeff X (a * e)) *
      ((Real.sqrt (a * d))⁻¹ * (Real.sqrt (a * e))⁻¹)) := by
  rw [selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq,
    selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq]
  simp only [selbergSqrtZetaSignedNumeratorRealCoeff, Nat.cast_mul]
  ring

/-- On a positive numerator index, the normalized numerator factor is
nonnegative exactly when the signed taper is nonnegative. -/
theorem selbergSqrtZetaSignedNumeratorRealCoeff_nonneg_iff
    {X l : ℕ} (hl : 0 < l) :
    0 ≤ selbergSqrtZetaSignedNumeratorRealCoeff X l ↔
      0 ≤ selbergSqrtZetaTaperedCoeff X l := by
  have hsqrt : 0 < (Real.sqrt l)⁻¹ := by positivity
  unfold selbergSqrtZetaSignedNumeratorRealCoeff
  constructor
  · intro h
    by_contra htaper
    have htaper' : selbergSqrtZetaTaperedCoeff X l < 0 :=
      lt_of_not_ge htaper
    exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos htaper' hsqrt)
  · intro h
    exact mul_nonneg h hsqrt.le

/-- On a positive numerator index, the normalized numerator factor is
nonpositive exactly when the signed taper is nonpositive. -/
theorem selbergSqrtZetaSignedNumeratorRealCoeff_nonpos_iff
    {X l : ℕ} (hl : 0 < l) :
    selbergSqrtZetaSignedNumeratorRealCoeff X l ≤ 0 ↔
      selbergSqrtZetaTaperedCoeff X l ≤ 0 := by
  have hsqrt : 0 < (Real.sqrt l)⁻¹ := by positivity
  unfold selbergSqrtZetaSignedNumeratorRealCoeff
  constructor
  · intro h
    by_contra htaper
    have htaper' : 0 < selbergSqrtZetaTaperedCoeff X l :=
      lt_of_not_ge htaper
    exact (not_lt_of_ge h) (mul_pos htaper' hsqrt)
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg h hsqrt.le

/-- An actual collected denominator lies between `1` and the product of the
two original denominator cutoffs. -/
theorem selbergSqrtZetaSignedDenominator_bounds_of_mem
    {N X k : ℕ}
    (hk : k ∈ selbergSqrtZetaSignedDenominatorSupport N X) :
    1 ≤ k ∧ k ≤ N * X := by
  rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hm, hr⟩
  have hm' := Finset.mem_Icc.mp hm
  have hr' := Finset.mem_Icc.mp hr
  exact ⟨Nat.mul_pos hm'.1 hr'.1,
    Nat.mul_le_mul hm'.2 hr'.2⟩

/-- The two scaled pairs in the actual off-diagonal support satisfy the
separate denominator and numerator support constraints. -/
theorem selbergSqrtZetaSignedCoprimeRayScales_pair_support_facts
    {N X : ℕ} {x : SelbergSqrtZetaSignedCoprimeRayScales}
    (hx :
      x ∈ selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X) :
    (x.denominator * x.leftScale) ∈
        selbergSqrtZetaSignedDenominatorSupport N X ∧
      (x.numerator * x.leftScale) ∈
        selbergSqrtZetaSignedNumeratorSupport X ∧
      (x.denominator * x.rightScale) ∈
        selbergSqrtZetaSignedDenominatorSupport N X ∧
      (x.numerator * x.rightScale) ∈
        selbergSqrtZetaSignedNumeratorSupport X := by
  have hscale :=
    selbergSqrtZetaSignedCoprimeRayScales_scale_facts hx
  have hleft :=
    Finset.mem_product.mp hscale.2.2.2.1
  have hright :=
    Finset.mem_product.mp hscale.2.2.2.2
  exact ⟨hleft.1, hleft.2, hright.1, hright.2⟩

/-- The finite set of positive scales on the fixed ray `(a,b)` whose
denominator-numerator pair occurs in the actual coefficient support. -/
noncomputable def selbergSqrtZetaSignedCoprimeRayScaleSupport
    (N X a b : ℕ) : Finset ℕ :=
  (Finset.range (N * X + 1)).filter fun d =>
    0 < d ∧
      (b * d, a * d) ∈
        selbergSqrtZetaSignedDenominatorNumeratorSupport N X

/-- Both scales of every term in the global coprime-ray reindexing occur in
the corresponding fixed-ray scale support.  This connects the exact global
off-diagonal sum to the one-dimensional correlation below. -/
theorem selbergSqrtZetaSignedCoprimeRayScales_mem_fixedScaleSupport
    {N X : ℕ} {x : SelbergSqrtZetaSignedCoprimeRayScales}
    (hx :
      x ∈ selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X) :
    x.leftScale ∈
        selbergSqrtZetaSignedCoprimeRayScaleSupport
          N X x.numerator x.denominator ∧
      x.rightScale ∈
        selbergSqrtZetaSignedCoprimeRayScaleSupport
          N X x.numerator x.denominator := by
  have hscale :=
    selbergSqrtZetaSignedCoprimeRayScales_scale_facts hx
  have hpairs :=
    selbergSqrtZetaSignedCoprimeRayScales_pair_support_facts hx
  have hbPos :=
    selbergSqrtZetaSignedCoprimeRayScales_denominator_pos hx
  have hleftBound :=
    (selbergSqrtZetaSignedDenominator_bounds_of_mem hpairs.1).2
  have hrightBound :=
    (selbergSqrtZetaSignedDenominator_bounds_of_mem hpairs.2.2.1).2
  have hleftLe :
      x.leftScale ≤ x.denominator * x.leftScale := by
    have h := Nat.mul_le_mul_right x.leftScale hbPos
    omega
  have hrightLe :
      x.rightScale ≤ x.denominator * x.rightScale := by
    have h := Nat.mul_le_mul_right x.rightScale hbPos
    omega
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hscale.1, ?_⟩
    · omega
    · exact Finset.mem_product.mpr ⟨hpairs.1, hpairs.2.1⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hscale.2.1, ?_⟩
    · omega
    · exact Finset.mem_product.mpr ⟨hpairs.2.2.1, hpairs.2.2.2⟩

private theorem sum_erase_mul_eq_mul_sum_sub_sq
    {S : Finset ℕ} {f : ℕ → ℝ} {d : ℕ} (hd : d ∈ S) :
    (∑ e ∈ S.erase d, f d * f e) =
      f d * (∑ e ∈ S, f e) - (f d) ^ 2 := by
  have herase :
      (∑ e ∈ S.erase d, f e) = (∑ e ∈ S, f e) - f d := by
    have hadd := Finset.sum_erase_add S f hd
    linarith
  rw [← Finset.mul_sum, herase]
  ring

/-- On one fixed coprime ray, the sum over unequal scales is exactly the
square of the one-dimensional scale sum minus its diagonal square energy.
The identity itself does not require coprimality, so it can be reused before
or after imposing the actual ray-support facts. -/
theorem selbergSqrtZetaSignedCoprimeRayCorrelation_eq_sq_sub_diagonal
    (N X a b : ℕ) :
    (∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
        ∑ e ∈
          (selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b).erase d,
          selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d) *
            selbergSqrtZetaSignedRationalPairCoeff N X (b * e, a * e)) =
      (∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
          selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d)) ^ 2 -
        ∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
          (selbergSqrtZetaSignedRationalPairCoeff N X
            (b * d, a * d)) ^ 2 := by
  classical
  let S := selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b
  let f : ℕ → ℝ := fun d =>
    selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d)
  calc
    (∑ d ∈ S, ∑ e ∈ S.erase d, f d * f e) =
        ∑ d ∈ S, (f d * (∑ e ∈ S, f e) - (f d) ^ 2) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact sum_erase_mul_eq_mul_sum_sub_sq hd
    _ = (∑ d ∈ S, f d) * (∑ e ∈ S, f e) -
        ∑ d ∈ S, (f d) ^ 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = (∑ d ∈ S, f d) ^ 2 - ∑ d ∈ S, (f d) ^ 2 := by ring

end HardyTheorem
