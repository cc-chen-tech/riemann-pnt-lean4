import HardyTheorem.SelbergSqrtZetaLowRangeEnergy
import HardyTheorem.SelbergSqrtZetaSignedReducedPairCompleteMainTerm

/-!
# Parseval cancellation for the reduced-pair complete main term

The complete reduced-ray coefficient is a multiplicative ratio coefficient.
Collecting its square over reduced ratios is therefore equal to collecting
the same two coefficient sequences by their product.  On the product side,
the two tapered square-root-zeta factors meet by Dirichlet convolution.

This is the cancellation mechanism that is lost by coefficientwise absolute
values or by a cardinality Cauchy estimate on each ray.
-/

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-- Positive indices in the square-root-zeta taper box. -/
noncomputable def selbergSqrtZetaCompleteIndexSupport (X : ℕ) : Finset ℕ :=
  Finset.Icc 1 X

/-- Ordered numerator-denominator pairs in the complete taper box. -/
noncomputable def selbergSqrtZetaCompletePairSupport
    (X : ℕ) : Finset (ℕ × ℕ) :=
  (selbergSqrtZetaCompleteIndexSupport X).product
    (selbergSqrtZetaCompleteIndexSupport X)

/-- Ratio key of a complete numerator-denominator pair. -/
noncomputable def selbergSqrtZetaCompleteRatioKey
    (p : ℕ × ℕ) : ℚ :=
  (p.1 : ℚ) / (p.2 : ℚ)

/-- Product key of a complete numerator-denominator pair. -/
def selbergSqrtZetaCompleteProductKey
    (p : ℕ × ℕ) : ℕ :=
  p.1 * p.2

/-- Finite set of ratios represented in the complete taper box. -/
noncomputable def selbergSqrtZetaCompleteRatioSupport
    (X : ℕ) : Finset ℚ :=
  (selbergSqrtZetaCompletePairSupport X).image
    selbergSqrtZetaCompleteRatioKey

/-- Finite set of products represented in the complete taper box. -/
noncomputable def selbergSqrtZetaCompleteProductSupport
    (X : ℕ) : Finset ℕ :=
  (selbergSqrtZetaCompletePairSupport X).image
    selbergSqrtZetaCompleteProductKey

/-- Complete pairs representing a fixed rational ratio. -/
noncomputable def selbergSqrtZetaCompleteRatioFiber
    (X : ℕ) (q : ℚ) : Finset (ℕ × ℕ) :=
  (selbergSqrtZetaCompletePairSupport X).filter
    (fun p => selbergSqrtZetaCompleteRatioKey p = q)

/-- Complete pairs representing a fixed integer product. -/
noncomputable def selbergSqrtZetaCompleteProductFiber
    (X n : ℕ) : Finset (ℕ × ℕ) :=
  (selbergSqrtZetaCompletePairSupport X).filter
    (fun p => selbergSqrtZetaCompleteProductKey p = n)

/-- The numerator taper divided by its critical-line square root. -/
noncomputable def selbergSqrtZetaCompleteNumeratorCoeff
    (X n : ℕ) : ℝ :=
  selbergSqrtZetaFullTapered X n / Real.sqrt n

/-- The complete denominator taper, after zeta convolution, divided by its
critical-line square root. -/
noncomputable def selbergSqrtZetaCompleteDenominatorCoeff
    (X n : ℕ) : ℝ :=
  (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      selbergSqrtZetaFullTapered X) n) / Real.sqrt n

/-- The normalized coefficient attached to one complete pair. -/
noncomputable def selbergSqrtZetaCompletePairCoeff
    (X : ℕ) (p : ℕ × ℕ) : ℝ :=
  selbergSqrtZetaCompleteNumeratorCoeff X p.1 *
    selbergSqrtZetaCompleteDenominatorCoeff X p.2

/-- The complete coefficient collected at one rational ratio. -/
noncomputable def selbergSqrtZetaCompleteRatioCoeff
    (X : ℕ) (q : ℚ) : ℝ :=
  ∑ p ∈ selbergSqrtZetaCompleteRatioFiber X q,
    selbergSqrtZetaCompletePairCoeff X p

/-- The complete coefficient collected at one integer product. -/
noncomputable def selbergSqrtZetaCompleteProductCoeff
    (X n : ℕ) : ℝ :=
  ∑ p ∈ selbergSqrtZetaCompleteProductFiber X n,
    selbergSqrtZetaCompletePairCoeff X p

private theorem sum_sq_image_fiber_eq_cross
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (key : α → β) (c : α → ℝ) :
    (∑ y ∈ S.image key,
        (∑ x ∈ S.filter (fun x => key x = y), c x) ^ 2) =
      ∑ x ∈ S, ∑ z ∈ S,
        if key z = key x then c x * c z else 0 := by
  classical
  let Q := S.image key
  have hmaps : ∀ x ∈ S, key x ∈ Q := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  calc
    (∑ y ∈ Q,
        (∑ x ∈ S.filter (fun x => key x = y), c x) ^ 2) =
        ∑ y ∈ Q,
          ∑ x ∈ S.filter (fun x => key x = y),
            ∑ z ∈ S.filter (fun z => key z = y), c x * c z := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
    _ = ∑ y ∈ Q,
          ∑ x ∈ S.filter (fun x => key x = y),
            ∑ z ∈ S.filter (fun z => key z = key x), c x * c z := by
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x ∈ S,
          ∑ z ∈ S.filter (fun z => key z = key x), c x * c z := by
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => ∑ z ∈ S.filter (fun z => key z = key x), c x * c z)
    _ = ∑ x ∈ S, ∑ z ∈ S,
          if key z = key x then c x * c z else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_filter]

private theorem completeRatioKey_eq_iff_cross
    {X : ℕ} {p r : ℕ × ℕ}
    (hp : p ∈ selbergSqrtZetaCompletePairSupport X)
    (hr : r ∈ selbergSqrtZetaCompletePairSupport X) :
    selbergSqrtZetaCompleteRatioKey r =
        selbergSqrtZetaCompleteRatioKey p ↔
      r.1 * p.2 = p.1 * r.2 := by
  have hp2 : 0 < p.2 :=
    (Finset.mem_Icc.mp (Finset.mem_product.mp hp).2).1
  have hr2 : 0 < r.2 :=
    (Finset.mem_Icc.mp (Finset.mem_product.mp hr).2).1
  unfold selbergSqrtZetaCompleteRatioKey
  rw [div_eq_div_iff]
  · norm_cast
  · exact_mod_cast hr2.ne'
  · exact_mod_cast hp2.ne'

private def swapCompleteCross
    (x : (ℕ × ℕ) × (ℕ × ℕ)) :
    (ℕ × ℕ) × (ℕ × ℕ) :=
  ((x.1.1, x.2.2), (x.2.1, x.1.2))

private theorem swapCompleteCross_involutive :
    Function.Involutive swapCompleteCross := by
  intro x
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

private theorem swapCompleteCross_mem
    {X : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)}
    (hx :
      x ∈ (selbergSqrtZetaCompletePairSupport X).product
        (selbergSqrtZetaCompletePairSupport X)) :
    swapCompleteCross x ∈
      (selbergSqrtZetaCompletePairSupport X).product
        (selbergSqrtZetaCompletePairSupport X) := by
  rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
  rcases Finset.mem_product.mp hx1 with ⟨ha, hb⟩
  rcases Finset.mem_product.mp hx2 with ⟨hc, hd⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨ha, hd⟩,
      Finset.mem_product.mpr ⟨hc, hb⟩⟩

/-- Finite multiplicative Parseval identity.  Collecting the two tapered
coefficient sequences by rational ratio or by integer product has exactly the
same square energy. -/
theorem sum_sq_selbergSqrtZetaCompleteRatioCoeff_eq_productCoeff
    (X : ℕ) :
    (∑ q ∈ selbergSqrtZetaCompleteRatioSupport X,
        selbergSqrtZetaCompleteRatioCoeff X q ^ 2) =
      ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
        selbergSqrtZetaCompleteProductCoeff X n ^ 2 := by
  classical
  let P := selbergSqrtZetaCompletePairSupport X
  let c := selbergSqrtZetaCompletePairCoeff X
  unfold selbergSqrtZetaCompleteRatioSupport
    selbergSqrtZetaCompleteRatioCoeff
    selbergSqrtZetaCompleteRatioFiber
    selbergSqrtZetaCompleteProductSupport
    selbergSqrtZetaCompleteProductCoeff
    selbergSqrtZetaCompleteProductFiber
  change
    (∑ q ∈ P.image selbergSqrtZetaCompleteRatioKey,
        (∑ p ∈ P.filter
          (fun p => selbergSqrtZetaCompleteRatioKey p = q), c p) ^ 2) =
      ∑ n ∈ P.image selbergSqrtZetaCompleteProductKey,
        (∑ p ∈ P.filter
          (fun p => selbergSqrtZetaCompleteProductKey p = n), c p) ^ 2
  rw [sum_sq_image_fiber_eq_cross P
      selbergSqrtZetaCompleteRatioKey c,
    sum_sq_image_fiber_eq_cross P
      selbergSqrtZetaCompleteProductKey c]
  change
    (∑ p ∈ P, ∑ r ∈ P,
      if selbergSqrtZetaCompleteRatioKey r =
          selbergSqrtZetaCompleteRatioKey p
      then c p * c r else 0) =
    ∑ p ∈ P, ∑ r ∈ P,
      if selbergSqrtZetaCompleteProductKey r =
          selbergSqrtZetaCompleteProductKey p
      then c p * c r else 0
  calc
    (∑ p ∈ P, ∑ r ∈ P,
        if selbergSqrtZetaCompleteRatioKey r =
            selbergSqrtZetaCompleteRatioKey p
        then c p * c r else 0) =
        ∑ x ∈ P.product P,
          if selbergSqrtZetaCompleteRatioKey x.2 =
              selbergSqrtZetaCompleteRatioKey x.1
          then c x.1 * c x.2 else 0 := by
      exact
        (Finset.sum_product P P
          (fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
            if selbergSqrtZetaCompleteRatioKey x.2 =
                selbergSqrtZetaCompleteRatioKey x.1
            then c x.1 * c x.2 else 0)).symm
    _ = ∑ x ∈ P.product P,
          if selbergSqrtZetaCompleteProductKey x.2 =
              selbergSqrtZetaCompleteProductKey x.1
          then c x.1 * c x.2 else 0 := by
      refine Finset.sum_bij (fun x _hx => swapCompleteCross x) ?_ ?_ ?_ ?_
      · intro x hx
        exact swapCompleteCross_mem hx
      · intro x hx y hy hxy
        exact swapCompleteCross_involutive.injective hxy
      · intro y hy
        refine ⟨swapCompleteCross y, swapCompleteCross_mem hy, ?_⟩
        exact swapCompleteCross_involutive y
      · intro x hx
        have hx' := Finset.mem_product.mp hx
        have hratio :=
          completeRatioKey_eq_iff_cross hx'.1 hx'.2
        rcases x with ⟨⟨a, b⟩, ⟨r, d⟩⟩
        simp only [swapCompleteCross,
          selbergSqrtZetaCompleteProductKey, c,
          selbergSqrtZetaCompletePairCoeff] at hratio ⊢
        by_cases hcross : r * b = a * d
        · rw [if_pos (hratio.mpr hcross), if_pos hcross]
          ring
        · rw [if_neg (fun h => hcross (hratio.mp h)),
            if_neg hcross]
    _ = ∑ p ∈ P, ∑ r ∈ P,
          if selbergSqrtZetaCompleteProductKey r =
              selbergSqrtZetaCompleteProductKey p
          then c p * c r else 0 := by
      exact
        Finset.sum_product P P
          (fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
            if selbergSqrtZetaCompleteProductKey x.2 =
                selbergSqrtZetaCompleteProductKey x.1
            then c x.1 * c x.2 else 0)

private theorem completeScaleSupport_facts
    {N X a b d : ℕ}
    (hd :
      d ∈ selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b) :
    0 < d ∧ a * d ≤ X ∧ b * d ≤ X := by
  have hdComplete := (Finset.mem_filter.mp hd).2
  have hdScale := (Finset.mem_filter.mp hd).1
  have hdRaw := (Finset.mem_filter.mp hdScale).2
  have hp :=
    Finset.mem_product.mp hdRaw.2
  have had :=
    Finset.mem_Icc.mp hp.2
  exact ⟨hdRaw.1, had.2, hdComplete.2⟩

private theorem mem_completeScaleSupport_of_bounds
    {N X a b d : ℕ}
    (hNX : X ≤ N) (hX : 0 < X) (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (had : a * d ≤ X) (hbd : b * d ≤ X) :
    d ∈ selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨?_, hd, ?_⟩
    · apply Finset.mem_range.mpr
      have hdLeX : d ≤ X := by
        have hda : d ≤ a * d := by
          have h := Nat.mul_le_mul_right d ha
          simpa [Nat.mul_comm] using h
        exact hda.trans had
      have hNpos : 0 < N := hX.trans_le hNX
      have hXleNX : X ≤ N * X := by
        simpa using Nat.mul_le_mul_right X hNpos
      omega
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_image.mpr
        refine ⟨(b * d, 1), ?_, ?_⟩
        · apply Finset.mem_product.mpr
          constructor
          · exact Finset.mem_Icc.mpr
              ⟨Nat.mul_pos hb hd, hbd.trans hNX⟩
          · exact Finset.mem_Icc.mpr ⟨by omega, hX⟩
        · simp [selbergSqrtZetaSignedDenominatorKey]
      · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hd, had⟩
  · exact ⟨hbd.trans hNX, hbd⟩

private theorem completePairCoeff_on_ray
    {X a b d : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    selbergSqrtZetaCompletePairCoeff X (a * d, b * d) =
      (Real.sqrt (a * b))⁻¹ *
        ((d : ℝ)⁻¹ *
          (selbergSqrtZetaCoeff (a * d) *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              selbergSqrtZetaCoeff) (b * d))) *
          (1 - Real.log (a * d) / Real.log X) *
          (1 + Real.log (b * d) / Real.log X)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt :
      Real.sqrt (a * d) * Real.sqrt (b * d) =
        Real.sqrt (a * b) * (d : ℝ) := by
    rw [Real.sqrt_mul haR.le, Real.sqrt_mul hbR.le,
      Real.sqrt_mul haR.le]
    calc
      √(a : ℝ) * √(d : ℝ) * (√(b : ℝ) * √(d : ℝ)) =
          √(a : ℝ) * √(b : ℝ) * (√(d : ℝ) * √(d : ℝ)) := by ring
      _ = √(a : ℝ) * √(b : ℝ) * (d : ℝ) := by
        rw [Real.mul_self_sqrt hdR.le]
  unfold selbergSqrtZetaCompletePairCoeff
    selbergSqrtZetaCompleteNumeratorCoeff
    selbergSqrtZetaCompleteDenominatorCoeff
  rw [selbergSqrtZetaFullTapered_apply,
    zeta_mul_selbergSqrtZetaFullTapered_apply]
  simp only [div_eq_mul_inv]
  push_cast
  calc
    (selbergSqrtZetaCoeff (a * d) *
          (1 - Real.log (a * d) * (Real.log X)⁻¹) *
          (Real.sqrt (a * d))⁻¹) *
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              selbergSqrtZetaCoeff) (b * d) *
            (1 + Real.log (b * d) / Real.log X)) *
          (Real.sqrt (b * d))⁻¹) =
        ((Real.sqrt (a * d))⁻¹ * (Real.sqrt (b * d))⁻¹) *
          ((selbergSqrtZetaCoeff (a * d) *
              (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                selbergSqrtZetaCoeff) (b * d))) *
            (1 - Real.log (a * d) / Real.log X) *
            (1 + Real.log (b * d) / Real.log X)) := by ring
    _ = (Real.sqrt (a * b))⁻¹ *
        ((d : ℝ)⁻¹ *
          (selbergSqrtZetaCoeff (a * d) *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              selbergSqrtZetaCoeff) (b * d))) *
          (1 - Real.log (a * d) / Real.log X) *
          (1 + Real.log (b * d) / Real.log X)) := by
      rw [← mul_inv, hsqrt, mul_inv]
      ring

/-- At a positive reduced ratio, the complete ratio coefficient is exactly
the existing signed complete ray term with its critical-line normalization.
The statement is uniform in `N` once the zeta cutoff contains the taper box. -/
theorem selbergSqrtZetaCompleteRatioCoeff_reduced_eq_completeTerm
    {N X a b : ℕ} (hNX : X ≤ N) (hX : 0 < X)
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    selbergSqrtZetaCompleteRatioCoeff X ((a : ℚ) / (b : ℚ)) =
      (Real.sqrt (a * b))⁻¹ *
        selbergSqrtZetaSignedReducedRayCompleteTerm N X a b := by
  classical
  unfold selbergSqrtZetaCompleteRatioCoeff
    selbergSqrtZetaCompleteRatioFiber
    selbergSqrtZetaSignedReducedRayCompleteTerm
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun d _hd => (a * d, b * d)) ?_ ?_ ?_ ?_
  · intro d hd
    have hdf := completeScaleSupport_facts hd
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hdf.1, hdf.2.1⟩,
          Finset.mem_Icc.mpr ⟨Nat.mul_pos hb hdf.1, hdf.2.2⟩⟩
    · unfold selbergSqrtZetaCompleteRatioKey
      apply (div_eq_div_iff
        (by exact_mod_cast (Nat.mul_pos hb hdf.1).ne')
        (by exact_mod_cast hb.ne')).2
      push_cast
      ring
  · intro d hd e he hde
    have hfirst : a * d = a * e := congrArg Prod.fst hde
    exact Nat.eq_of_mul_eq_mul_left ha hfirst
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpBox := Finset.mem_product.mp hp'.1
    have hmPos : 0 < p.1 := (Finset.mem_Icc.mp hpBox.1).1
    have hnPos : 0 < p.2 := (Finset.mem_Icc.mp hpBox.2).1
    have hratio : (p.1 : ℚ) * (b : ℚ) = (a : ℚ) * (p.2 : ℚ) := by
      exact
        (div_eq_div_iff (by exact_mod_cast hnPos.ne')
          (by exact_mod_cast hb.ne')).mp hp'.2
    have hcross : p.1 * b = a * p.2 := by
      exact_mod_cast hratio
    have haDvd : a ∣ p.1 := by
      apply hab.dvd_of_dvd_mul_right
      rw [hcross]
      exact dvd_mul_right a p.2
    let d := p.1 / a
    have hmFactor : p.1 = a * d :=
      (Nat.mul_div_cancel' haDvd).symm
    have hnFactor : p.2 = b * d := by
      apply Nat.eq_of_mul_eq_mul_left ha
      simpa only [hmFactor, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hcross.symm
    have hdPos : 0 < d := by
      have hdNe : d ≠ 0 := by
        intro hd0
        rw [hd0, mul_zero] at hmFactor
        omega
      exact Nat.pos_of_ne_zero hdNe
    have had : a * d ≤ X := by
      simpa only [← hmFactor] using (Finset.mem_Icc.mp hpBox.1).2
    have hbd : b * d ≤ X := by
      simpa only [← hnFactor] using (Finset.mem_Icc.mp hpBox.2).2
    exact ⟨d,
      mem_completeScaleSupport_of_bounds hNX hX ha hb hdPos had hbd,
      by simp only [← hmFactor, ← hnFactor]⟩
  · intro d hd
    exact (completePairCoeff_on_ray ha hb
      (completeScaleSupport_facts hd).1).symm

private theorem completeProductFiber_eq_divisorsAntidiagonal
    {X n : ℕ} (hn : 0 < n) (hnX : n ≤ X) :
    selbergSqrtZetaCompleteProductFiber X n =
      n.divisorsAntidiagonal := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨hp'.2, hn.ne'⟩
  · intro hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hn0⟩
    have hprod0 : p.1 * p.2 ≠ 0 := by
      rw [hprod]
      exact hn0
    have hp1 : 0 < p.1 :=
      Nat.pos_of_ne_zero (left_ne_zero_of_mul hprod0)
    have hp2 : 0 < p.2 :=
      Nat.pos_of_ne_zero (right_ne_zero_of_mul hprod0)
    have hp1Dvd : p.1 ∣ n := ⟨p.2, hprod.symm⟩
    have hp2Dvd : p.2 ∣ n :=
      ⟨p.1, by simpa [Nat.mul_comm] using hprod.symm⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr
            ⟨hp1, (Nat.le_of_dvd hn hp1Dvd).trans hnX⟩,
          Finset.mem_Icc.mpr
            ⟨hp2, (Nat.le_of_dvd hn hp2Dvd).trans hnX⟩⟩
    · exact hprod

private theorem completePairCoeff_eq_invSqrtProduct_mul
    {X : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ selbergSqrtZetaCompletePairSupport X) :
    selbergSqrtZetaCompletePairCoeff X p =
      (Real.sqrt (p.1 * p.2))⁻¹ *
        (selbergSqrtZetaFullTapered X p.1 *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaFullTapered X) p.2)) := by
  have hp' := Finset.mem_product.mp hp
  have hp1 : (0 : ℝ) ≤ p.1 := by positivity
  unfold selbergSqrtZetaCompletePairCoeff
    selbergSqrtZetaCompleteNumeratorCoeff
    selbergSqrtZetaCompleteDenominatorCoeff
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [Real.sqrt_mul hp1]
  ring

/-- On the complete product range `n ≤ X`, the product-collected coefficient
is the exact Dirichlet convolution of the two full taper factors, divided by
`sqrt n`. -/
theorem selbergSqrtZetaCompleteProductCoeff_eq_collected_div_sqrt
    {X n : ℕ} (hn : 0 < n) (hnX : n ≤ X) :
    selbergSqrtZetaCompleteProductCoeff X n =
      ((((selbergSqrtZetaFullTapered X *
          selbergSqrtZetaFullTapered X) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) /
          Real.sqrt n) := by
  classical
  unfold selbergSqrtZetaCompleteProductCoeff
  rw [completeProductFiber_eq_divisorsAntidiagonal hn hnX]
  rw [show
      (selbergSqrtZetaFullTapered X *
          selbergSqrtZetaFullTapered X) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
        selbergSqrtZetaFullTapered X *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaFullTapered X) by ring]
  rw [ArithmeticFunction.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hpProd :=
    (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hpBox :
      p ∈ selbergSqrtZetaCompletePairSupport X := by
    have hpFiber :
        p ∈ selbergSqrtZetaCompleteProductFiber X n := by
      rw [completeProductFiber_eq_divisorsAntidiagonal hn hnX]
      exact hp
    exact (Finset.mem_filter.mp hpFiber).1
  have hpProdR : (p.1 : ℝ) * (p.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast hpProd
  rw [completePairCoeff_eq_invSqrtProduct_mul hpBox, hpProdR]
  ring

/-- Explicit high-product tail left after the exact ratio/product Parseval
reindexing.  It keeps the signed truncated convolution coefficient intact. -/
noncomputable def selbergSqrtZetaCompleteProductHighEnergy
    (X : ℕ) : ℝ :=
  ∑ n ∈ (selbergSqrtZetaCompleteProductSupport X).filter (fun n => X < n),
    selbergSqrtZetaCompleteProductCoeff X n ^ 2

/-- The full product-side Parseval energy is bounded by the proved low-range
constant plus one explicit signed high-product tail. -/
theorem sum_sq_selbergSqrtZetaCompleteProductCoeff_le_nineteen_fourths_add_high
    {X : ℕ} (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    (∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
        selbergSqrtZetaCompleteProductCoeff X n ^ 2) ≤
      (19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X := by
  classical
  let S := selbergSqrtZetaCompleteProductSupport X
  have hsplit :
      (∑ n ∈ S, selbergSqrtZetaCompleteProductCoeff X n ^ 2) =
        (∑ n ∈ S.filter (fun n => n ≤ X),
          selbergSqrtZetaCompleteProductCoeff X n ^ 2) +
        ∑ n ∈ S.filter (fun n => X < n),
          selbergSqrtZetaCompleteProductCoeff X n ^ 2 := by
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not S
        (fun n => n ≤ X)
        (fun n => selbergSqrtZetaCompleteProductCoeff X n ^ 2)).symm
  rw [hsplit]
  unfold selbergSqrtZetaCompleteProductHighEnergy
  have hlowSubset :
      S.filter (fun n => n ≤ X) ⊆ Finset.Icc 1 X := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    rcases Finset.mem_image.mp hn'.1 with ⟨p, hp, hprod⟩
    have hp' := Finset.mem_product.mp hp
    have hnPos : 0 < n := by
      rw [← hprod]
      exact Nat.mul_pos
        (Finset.mem_Icc.mp hp'.1).1
        (Finset.mem_Icc.mp hp'.2).1
    exact Finset.mem_Icc.mpr ⟨hnPos, hn'.2⟩
  have hlow :
      (∑ n ∈ S.filter (fun n => n ≤ X),
        selbergSqrtZetaCompleteProductCoeff X n ^ 2) ≤
        (19 : ℝ) / 4 := by
    calc
      (∑ n ∈ S.filter (fun n => n ≤ X),
        selbergSqrtZetaCompleteProductCoeff X n ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 X,
          selbergSqrtZetaCompleteProductCoeff X n ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hlowSubset (by
          intro n _hn _hnot
          positivity)
      _ = 1 +
          ∑ n ∈ Finset.Ioc 1 X,
            selbergSqrtZetaLowRangeCoeff X n ^ 2 / (n : ℝ) := by
        have hset :
            Finset.Icc 1 X = insert 1 (Finset.Ioc 1 X) := by
          ext n
          simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
          omega
        rw [hset, Finset.sum_insert (by simp)]
        have hone :
            selbergSqrtZetaCompleteProductCoeff X 1 = 1 := by
          rw [selbergSqrtZetaCompleteProductCoeff_eq_collected_div_sqrt
            (by omega) (by omega)]
          simp
        rw [hone]
        simp only [one_pow]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        have hn1 : 1 < n := (Finset.mem_Ioc.mp hn).1
        have hnX : n ≤ X := (Finset.mem_Ioc.mp hn).2
        rw [selbergSqrtZetaCompleteProductCoeff_eq_collected_div_sqrt
          (by omega) hnX]
        rw [show
            (((selbergSqrtZetaFullTapered X *
                selbergSqrtZetaFullTapered X) *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) =
              selbergSqrtZetaLowRangeCoeff X n by
          rw [← selbergShortTaperedSqrtZeta_collected_eq_full_of_le
            (by omega) hnX]
          exact selbergShortTaperedSqrtZeta_collected_eq_lowRangeCoeff
            hX hn1 hnX]
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        rw [div_pow, Real.sq_sqrt hn0.le]
      _ ≤ 1 + 15 / 4 := by
        gcongr
        exact sum_sq_selbergSqrtZetaLowRangeCoeff_div_le_fifteen_fourths
          hX hlarge
      _ = 19 / 4 := by ring
  change
    (∑ n ∈ S.filter (fun n => n ≤ X),
        selbergSqrtZetaCompleteProductCoeff X n ^ 2) +
      (∑ n ∈ S.filter (fun n => X < n),
        selbergSqrtZetaCompleteProductCoeff X n ^ 2) ≤
    (19 : ℝ) / 4 +
      (∑ n ∈ S.filter (fun n => X < n),
        selbergSqrtZetaCompleteProductCoeff X n ^ 2)
  linarith

private theorem inv_mul_completeTerm_sq_eq_ratioCoeff_sq
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

private theorem completeTerm_eq_zero_of_coordinate_outside
    {N X a b : ℕ} (hout : X < a ∨ X < b) :
    selbergSqrtZetaSignedReducedRayCompleteTerm N X a b = 0 := by
  unfold selbergSqrtZetaSignedReducedRayCompleteTerm
  apply Finset.sum_eq_zero
  intro d hd
  have hdf := completeScaleSupport_facts hd
  rcases hout with ha | hb
  · have : a ≤ a * d := by
      have := Nat.mul_le_mul_left a hdf.1
      simpa using this
    omega
  · have : b ≤ b * d := by
      have := Nat.mul_le_mul_left b hdf.1
      simpa using this
    omega

private theorem completeRatioCoeff_eq_zero_of_coordinate_outside
    {N X a b : ℕ} (hNX : X ≤ N) (hX : 0 < X)
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hout : X < a ∨ X < b) :
    selbergSqrtZetaCompleteRatioCoeff X ((a : ℚ) / (b : ℚ)) = 0 := by
  rw [selbergSqrtZetaCompleteRatioCoeff_reduced_eq_completeTerm
    hNX hX ha hb hab,
    completeTerm_eq_zero_of_coordinate_outside hout, mul_zero]

private theorem reducedPairCompleteEnergy_pointwise_le_ratio
    {N X : ℕ} (hNX : X ≤ N) (hX : 0 < X)
    {p : ℕ × ℕ}
    (hp : p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X) :
    ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
        ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          selbergSqrtZetaSignedReducedRayCompleteTerm
            N X p.1 p.2 ^ 2) ≤
      (((X : ℝ) ^ 2 + 1) *
        selbergSqrtZetaCompleteRatioCoeff X
          (selbergSqrtZetaSignedReducedPairKey p) ^ 2) := by
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
  by_cases hin : p.1 ≤ X ∧ p.2 ≤ X
  · have hNle : N ≤ p.1 * N := by
      have := Nat.mul_le_mul_right N hpFacts.1
      simpa [Nat.mul_comm] using this
    have hmin : min (p.1 * N) p.2 = p.2 :=
      Nat.min_eq_right (hin.2.trans (hNX.trans hNle))
    have hweight :
        (((X * p.2 + 1 : ℕ) : ℝ)) ≤ (X : ℝ) ^ 2 + 1 := by
      calc
        (((X * p.2 + 1 : ℕ) : ℝ)) ≤
            ((X * X + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_le_add_right
            (Nat.mul_le_mul_left X hin.2) 1
        _ = (X : ℝ) ^ 2 + 1 := by
          push_cast
          ring
    have hratio :=
      inv_mul_completeTerm_sq_eq_ratioCoeff_sq
        hNX hX hpFacts.1 hpFacts.2.1 hpFacts.2.2.1
    rw [hmin, hratio]
    exact mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
  · have hout : X < p.1 ∨ X < p.2 := by omega
    rw [completeTerm_eq_zero_of_coordinate_outside hout]
    nlinarith [sq_nonneg
      (selbergSqrtZetaCompleteRatioCoeff X
        (selbergSqrtZetaSignedReducedPairKey p))]

private theorem sum_sq_ratioCoeff_over_reducedPairSupport_le
    {N X : ℕ} (hNX : X ≤ N) (hX : 0 < X) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        selbergSqrtZetaCompleteRatioCoeff X
          (selbergSqrtZetaSignedReducedPairKey p) ^ 2) ≤
      ∑ q ∈ selbergSqrtZetaCompleteRatioSupport X,
        selbergSqrtZetaCompleteRatioCoeff X q ^ 2 := by
  classical
  let R := selbergSqrtZetaSignedRationalReducedPairSupport N X
  let C := R.filter (fun p => p.1 ≤ X ∧ p.2 ≤ X)
  let key := selbergSqrtZetaSignedReducedPairKey
  let f : ℚ → ℝ := fun q =>
    selbergSqrtZetaCompleteRatioCoeff X q ^ 2
  have houtside :
      ∀ p ∈ R, p ∉ C → f (key p) = 0 := by
    intro p hp hpC
    have hpFacts :=
      selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
    have hout : X < p.1 ∨ X < p.2 := by
      simp only [C, Finset.mem_filter, hp, true_and] at hpC
      omega
    unfold f key selbergSqrtZetaSignedReducedPairKey
    rw [completeRatioCoeff_eq_zero_of_coordinate_outside
      hNX hX hpFacts.1 hpFacts.2.1 hpFacts.2.2.1 hout]
    simp
  have hrestrict :
      (∑ p ∈ R, f (key p)) = ∑ p ∈ C, f (key p) := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro p hpR hpNot
      exact houtside p hpR hpNot)
  have hinj :
      Set.InjOn key (C : Set (ℕ × ℕ)) := by
    intro p hp r hr hpr
    change p ∈ C at hp
    change r ∈ C at hr
    dsimp only [C] at hp hr
    exact selbergSqrtZetaSignedReducedPairKey_injOn N X
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hr).1 hpr
  have himage :
      C.image key ⊆ selbergSqrtZetaCompleteRatioSupport X := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hpC, rfl⟩
    have hpC' := Finset.mem_filter.mp hpC
    have hpFacts :=
      selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hpC'.1
    apply Finset.mem_image.mpr
    refine ⟨p, ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpFacts.1, hpC'.2.1⟩,
        Finset.mem_Icc.mpr ⟨hpFacts.2.1, hpC'.2.2⟩⟩
  rw [hrestrict]
  calc
    (∑ p ∈ C, f (key p)) =
        ∑ q ∈ C.image key, f q := by
      exact (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ selbergSqrtZetaCompleteRatioSupport X, f q :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro q _hq _hnot
        unfold f
        positivity)

/-- The canonical complete main-term energy loses no factor depending on the
zeta cutoff `N`.  Multiplicative Parseval and the exact two-taper convolution
reduce it to `X² + 1` times a one-dimensional signed product energy. -/
theorem sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_le_productEnergy
    {N X : ℕ} (hNX : X ≤ N) (hX : 0 < X) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2 ^ 2)) ≤
      (((X : ℝ) ^ 2 + 1) *
        ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
          selbergSqrtZetaCompleteProductCoeff X n ^ 2) := by
  calc
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2 ^ 2)) ≤
        ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
          (((X : ℝ) ^ 2 + 1) *
            selbergSqrtZetaCompleteRatioCoeff X
              (selbergSqrtZetaSignedReducedPairKey p) ^ 2) :=
      Finset.sum_le_sum fun p hp =>
        reducedPairCompleteEnergy_pointwise_le_ratio hNX hX hp
    _ = ((X : ℝ) ^ 2 + 1) *
        ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
          selbergSqrtZetaCompleteRatioCoeff X
            (selbergSqrtZetaSignedReducedPairKey p) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ((X : ℝ) ^ 2 + 1) *
        ∑ q ∈ selbergSqrtZetaCompleteRatioSupport X,
          selbergSqrtZetaCompleteRatioCoeff X q ^ 2 :=
      mul_le_mul_of_nonneg_left
        (sum_sq_ratioCoeff_over_reducedPairSupport_le hNX hX)
        (by positivity)
    _ = ((X : ℝ) ^ 2 + 1) *
        ∑ n ∈ selbergSqrtZetaCompleteProductSupport X,
          selbergSqrtZetaCompleteProductCoeff X n ^ 2 := by
      rw [sum_sq_selbergSqrtZetaCompleteRatioCoeff_eq_productCoeff]

/-- Strongest unconditional compiled complete-main-term estimate currently
available: the full canonical square sum has the natural `X²` prefactor, the
complete low product range costs only `19/4`, and the sole remaining term is
the signed truncated-convolution energy on `X < n ≤ X²`. -/
theorem
    sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_le_nineteen_fourths_add_high
    {N X : ℕ} (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2 ^ 2)) ≤
      (((X : ℝ) ^ 2 + 1) *
        ((19 : ℝ) / 4 +
          selbergSqrtZetaCompleteProductHighEnergy X)) := by
  exact
    (sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_le_productEnergy
      hNX (by omega)).trans
      (mul_le_mul_of_nonneg_left
        (sum_sq_selbergSqrtZetaCompleteProductCoeff_le_nineteen_fourths_add_high
          hX hlarge)
        (by positivity))

end HardyTheorem
