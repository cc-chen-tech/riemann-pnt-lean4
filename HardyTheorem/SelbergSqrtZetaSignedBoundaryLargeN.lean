import HardyTheorem.SelbergSqrtZetaSignedBoundaryScale
import HardyTheorem.SelbergSqrtZetaSignedReducedRayCompleteBoundary

/-!
# Stable boundary rays once the zeta cutoff is large

For a fixed positive reduced ray `(a,b)`, the numerator cutoff forces every
scale to satisfy `d ≤ X / a`.  Consequently `b * X ≤ N` makes the zeta cutoff
inactive on the whole ray.  The boundary support then stabilizes exactly to
the interval `(X / b, X / a]`; it does not vanish in general, but it is empty
on every ray with `b ≤ a`.
-/

open scoped BigOperators

namespace HardyTheorem

/-- Once a positive denominator key lies below `N`, the first coordinate of
its factorization is automatically below `N`.  Thus the finite denominator
fiber is exactly the full divisor antidiagonal restricted only by `r ≤ X`. -/
theorem selbergSqrtZetaSignedDenominatorFiber_eq_divisorsAntidiagonal_filter_snd
    {N X k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    selbergSqrtZetaSignedDenominatorFiber N X k =
      k.divisorsAntidiagonal.filter (fun p => p.2 ≤ X) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpRaw, hprod⟩
    rcases Finset.mem_product.mp hpRaw with ⟨hm, hr⟩
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hk.ne'⟩,
        (Finset.mem_Icc.mp hr).2⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpDiv, hrX⟩
    rcases Nat.mem_divisorsAntidiagonal.mp hpDiv with ⟨hprod, hne⟩
    have hprod0 : p.1 * p.2 ≠ 0 := by
      rw [hprod]
      exact hne
    have hm0 : p.1 ≠ 0 := left_ne_zero_of_mul hprod0
    have hr0 : p.2 ≠ 0 := right_ne_zero_of_mul hprod0
    have hmDvd : p.1 ∣ k := ⟨p.2, hprod.symm⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
      Finset.mem_Icc.mpr ?_⟩, hprod⟩
    · exact ⟨Nat.one_le_iff_ne_zero.mpr hm0,
        (Nat.le_of_dvd hk hmDvd).trans hkN⟩
    · exact ⟨Nat.one_le_iff_ne_zero.mpr hr0, hrX⟩

/-- If `b * X ≤ N`, every positive scale allowed by the numerator cutoff
occurs on the fixed ray.  The full scale support is therefore the exact
interval `[1, X / a]`. -/
theorem selbergSqrtZetaSignedCoprimeRayScaleSupport_eq_Icc_of_b_mul_X_le_N
    {N X a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hX : 1 ≤ X)
    (hlarge : b * X ≤ N) :
    selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b =
      Finset.Icc 1 (X / a) := by
  ext d
  constructor
  · intro hd
    rcases Finset.mem_filter.mp hd with ⟨_hdRange, hdPos, hdPair⟩
    rcases Finset.mem_product.mp hdPair with ⟨_hden, hnum⟩
    change a * d ∈ Finset.Icc 1 X at hnum
    have hadX := (Finset.mem_Icc.mp hnum).2
    apply Finset.mem_Icc.mpr
    refine ⟨hdPos, (Nat.le_div_iff_mul_le ha).2 ?_⟩
    simpa [Nat.mul_comm] using hadX
  · intro hd
    rcases Finset.mem_Icc.mp hd with ⟨hdPos, hdUpper⟩
    have hadX : a * d ≤ X := by
      have := (Nat.le_div_iff_mul_le ha).1 hdUpper
      simpa [Nat.mul_comm] using this
    have hdX : d ≤ X := by
      have hda : d ≤ a * d := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left d ha
      exact hda.trans hadX
    have hbdN : b * d ≤ N :=
      (Nat.mul_le_mul_left b hdX).trans hlarge
    have hNPos : 0 < N :=
      lt_of_lt_of_le (Nat.mul_pos hb hX) hlarge
    have hXNX : X ≤ N * X := by
      calc
        X = 1 * X := by simp
        _ ≤ N * X := Nat.mul_le_mul_right X hNPos
    have hdNX : d ≤ N * X := hdX.trans hXNX
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hdNX), hdPos, ?_⟩
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨(b * d, 1), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_Icc.mpr
          ⟨Nat.mul_pos hb hdPos, hbdN⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, hX⟩
      · simp [selbergSqrtZetaSignedDenominatorKey]
    · change a * d ∈ Finset.Icc 1 X
      exact Finset.mem_Icc.mpr
        ⟨Nat.mul_pos ha hdPos, hadX⟩

/-- Stable support theorem for the truncation defect.  Under `b * X ≤ N`,
the only incomplete scales are exactly `X / b < d ≤ X / a`. -/
theorem
    selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_eq_Ioc_of_b_mul_X_le_N
    {N X a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hX : 1 ≤ X)
    (hlarge : b * X ≤ N) :
    selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b =
      Finset.Ioc (X / b) (X / a) := by
  have hXN : X ≤ N := by
    calc
      X = 1 * X := by simp
      _ ≤ b * X := Nat.mul_le_mul_right X hb
      _ ≤ N := hlarge
  rw [selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_eq_filter_min_div
    N X a b hb, Nat.min_eq_right hXN,
    selbergSqrtZetaSignedCoprimeRayScaleSupport_eq_Icc_of_b_mul_X_le_N
      ha hb hX hlarge]
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_hdPos, hdUpper⟩, hdLower⟩
    exact ⟨hdLower, hdUpper⟩
  · rintro ⟨hdLower, hdUpper⟩
    refine ⟨⟨?_, hdUpper⟩, hdLower⟩
    exact lt_of_le_of_lt (Nat.zero_le (X / b)) hdLower

/-- Exact stabilized boundary term.  Both its scale support and every
denominator fiber on that support are independent of `N`. -/
theorem selbergSqrtZetaSignedReducedRayBoundaryTerm_eq_stable_Ioc
    {N X a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hX : 1 ≤ X)
    (hlarge : b * X ≤ N) :
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b =
      ∑ d ∈ Finset.Ioc (X / b) (X / a),
        (d : ℝ)⁻¹ * selbergSqrtZetaTaperedCoeff X (a * d) *
          ∑ p ∈ (b * d).divisorsAntidiagonal.filter (fun p => p.2 ≤ X),
            selbergSqrtZetaTaperedCoeff X p.2 := by
  unfold selbergSqrtZetaSignedReducedRayBoundaryTerm
  rw [selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_eq_Ioc_of_b_mul_X_le_N
    ha hb hX hlarge]
  apply Finset.sum_congr rfl
  intro d hd
  have hdPos : 0 < d :=
    lt_of_le_of_lt (Nat.zero_le (X / b)) (Finset.mem_Ioc.mp hd).1
  have hdUpper : d ≤ X / a := (Finset.mem_Ioc.mp hd).2
  have hadX : a * d ≤ X := by
    have := (Nat.le_div_iff_mul_le ha).1 hdUpper
    simpa [Nat.mul_comm] using this
  have hdX : d ≤ X := by
    have hda : d ≤ a * d := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left d ha
    exact hda.trans hadX
  have hbdN : b * d ≤ N :=
    (Nat.mul_le_mul_left b hdX).trans hlarge
  rw [selbergSqrtZetaSignedDenominatorFiber_eq_divisorsAntidiagonal_filter_snd
    (Nat.mul_pos hb hdPos) hbdN]

/-- The common asymptotic hypothesis `X² ≤ N` stabilizes every reduced ray
whose denominator coordinate lies in the taper box. -/
theorem selbergSqrtZetaSignedReducedRayBoundaryTerm_eq_stable_Ioc_of_sq_le
    {N X a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hX : 1 ≤ X)
    (hN : X * X ≤ N) (hbX : b ≤ X) :
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b =
      ∑ d ∈ Finset.Ioc (X / b) (X / a),
        (d : ℝ)⁻¹ * selbergSqrtZetaTaperedCoeff X (a * d) *
          ∑ p ∈ (b * d).divisorsAntidiagonal.filter (fun p => p.2 ≤ X),
            selbergSqrtZetaTaperedCoeff X p.2 := by
  apply selbergSqrtZetaSignedReducedRayBoundaryTerm_eq_stable_Ioc
    ha hb hX
  exact (Nat.mul_le_mul_right X hbX).trans hN

/-- Once `X ≤ N`, a boundary scale can occur only below the rational carrier,
i.e. only on a ray with numerator strictly smaller than denominator. -/
theorem selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_numerator_lt_denominator
    {N X a b d : ℕ} (hXN : X ≤ N)
    (hd : d ∈ selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b) :
    a < b := by
  rcases selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_facts hd with
    ⟨_hdPos, _haPos, _hbPos, hadX, _hbdNX, hcross⟩
  have hXbd : X < b * d := by
    rcases hcross with hNbd | hXbd
    · exact lt_of_le_of_lt hXN hNbd
    · exact hXbd
  by_contra hab
  have hba : b ≤ a := Nat.le_of_not_gt hab
  have hbdad : b * d ≤ a * d := Nat.mul_le_mul_right d hba
  omega

/-- Therefore all boundary scales vanish on and above the rational carrier. -/
theorem selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_eq_empty_of_denominator_le_numerator
    {N X a b : ℕ} (hXN : X ≤ N) (hba : b ≤ a) :
    selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b = ∅ := by
  ext d
  constructor
  · intro hd
    exact False.elim ((not_lt_of_ge hba)
      (selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_numerator_lt_denominator
        hXN hd))
  · intro hd
    simp at hd

/-- Exact vanishing of the reduced-ray boundary defect on every ray `a / b ≥ 1`.
This strictly generalizes the previously isolated `(1,1)` carrier case. -/
theorem selbergSqrtZetaSignedReducedRayBoundaryTerm_eq_zero_of_denominator_le_numerator
    {N X a b : ℕ} (hXN : X ≤ N) (hba : b ≤ a) :
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b = 0 := by
  unfold selbergSqrtZetaSignedReducedRayBoundaryTerm
  rw [selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_eq_empty_of_denominator_le_numerator
    hXN hba]
  simp

end HardyTheorem
