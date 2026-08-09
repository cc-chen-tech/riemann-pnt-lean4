import HardyTheorem.SelbergSqrtZetaSignedRationalCoefficientEnergySharp
import HardyTheorem.SelbergSqrtZetaLowRangeSliding
import HardyTheorem.SelbergSqrtZetaShortCollected

/-!
# Rectangular multiplicative Parseval for the finite square-root-zeta model

The finite support is rectangular after grouping `(m,d)` as a denominator
index and keeping `l` as the numerator index.  On two copies of this support,
swapping the numerator coordinates converts equality of ratios

`l / (m*d) = l' / (m'*d')`

into equality of products

`m*d*l' = m'*d'*l`.

The swap preserves the product of the signed real coefficients.  Consequently
the exact square energy obtained by collecting at rational frequencies equals
the exact square energy obtained by collecting the same finite model at
integer products.  The latter coefficients are the existing short Dirichlet
coefficients, not a majorant; hence all Möbius/taper signs are retained.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- Integer product key of one point in the finite rectangular support. -/
def selbergSqrtZetaRectangularProductKey
    (p : ℕ × (ℕ × ℕ)) : ℕ :=
  p.1 * p.2.1 * p.2.2

/-- The products actually represented by the finite rectangular support.
Unlike `selbergShortDirichletCollectedSupport`, this image contains no
zero-coefficient gaps. -/
noncomputable def selbergSqrtZetaRectangularProductSupport
    (N X : ℕ) : Finset ℕ :=
  (selbergSqrtZetaSignedPhaseSupport N X).image
    selbergSqrtZetaRectangularProductKey

/-- The real coefficient of one raw rectangular point. -/
noncomputable def selbergSqrtZetaRectangularRawCoeff
    (X : ℕ) (p : ℕ × (ℕ × ℕ)) : ℝ :=
  (selbergSqrtZetaSignedPhaseCoeff X p).re

private theorem selbergSqrtZetaSignedPhaseCoeff_im_eq_zero
    (X : ℕ) (p : ℕ × (ℕ × ℕ)) :
    (selbergSqrtZetaSignedPhaseCoeff X p).im = 0 := by
  unfold selbergSqrtZetaSignedPhaseCoeff
  simp

private theorem selbergSqrtZetaSignedPhaseCoeff_eq_ofReal_rawCoeff
    (X : ℕ) (p : ℕ × (ℕ × ℕ)) :
    selbergSqrtZetaSignedPhaseCoeff X p =
      (selbergSqrtZetaRectangularRawCoeff X p : ℂ) := by
  apply Complex.ext
  · rfl
  · simp [selbergSqrtZetaSignedPhaseCoeff_im_eq_zero]

private theorem selbergSqrtZetaShortDirichletTripleCoeff_eq_signedPhaseCoeff
    {N X : ℕ} {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X) :
    selbergSqrtZetaShortDirichletTripleCoeff X p =
      selbergSqrtZetaSignedPhaseCoeff X p := by
  rcases p with ⟨m, d, l⟩
  rcases Finset.mem_product.mp hp with ⟨hm, hdl⟩
  rcases Finset.mem_product.mp hdl with ⟨hd, hl⟩
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hsqrt :
      Real.sqrt (((m * d * l : ℕ) : ℝ)) =
        Real.sqrt m * Real.sqrt d * Real.sqrt l := by
    push_cast
    rw [show (m : ℝ) * d * l = ((m : ℝ) * d) * l by ring,
      Real.sqrt_mul (mul_nonneg hm0 hd0), Real.sqrt_mul hm0]
  unfold selbergSqrtZetaShortDirichletTripleCoeff
    selbergSqrtZetaSignedPhaseCoeff
  rw [hsqrt]
  push_cast
  ring

private theorem selbergSqrtZetaSignedRationalCoeff_eq_ofReal_rawFiberSum
    (N X : ℕ) (q : ℚ) :
    selbergSqrtZetaSignedRationalCoeff N X q =
      ((∑ p ∈ selbergSqrtZetaSignedRationalFiber N X q,
          selbergSqrtZetaRectangularRawCoeff X p : ℝ) : ℂ) := by
  unfold selbergSqrtZetaSignedRationalCoeff
  simp_rw [selbergSqrtZetaSignedPhaseCoeff_eq_ofReal_rawCoeff]
  push_cast
  rfl

private theorem
    selbergSqrtZetaShortDirichletCollectedCoeff_eq_ofReal_rawProductFiberSum
    (N X k : ℕ) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X k =
      ((∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaRectangularProductKey p = k),
          selbergSqrtZetaRectangularRawCoeff X p : ℝ) : ℂ) := by
  classical
  unfold selbergSqrtZetaShortDirichletCollectedCoeff
    selbergShortDirichletTriples
  change
    (∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
        (fun p => selbergSqrtZetaRectangularProductKey p = k),
        selbergSqrtZetaShortDirichletTripleCoeff X p) = _
  calc
    (∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
        (fun p => selbergSqrtZetaRectangularProductKey p = k),
        selbergSqrtZetaShortDirichletTripleCoeff X p) =
        ∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaRectangularProductKey p = k),
          (selbergSqrtZetaRectangularRawCoeff X p : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [selbergSqrtZetaShortDirichletTripleCoeff_eq_signedPhaseCoeff
        (Finset.mem_filter.mp hp).1,
        selbergSqrtZetaSignedPhaseCoeff_eq_ofReal_rawCoeff]
    _ = ((∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
          (fun p => selbergSqrtZetaRectangularProductKey p = k),
          selbergSqrtZetaRectangularRawCoeff X p : ℝ) : ℂ) := by
      push_cast
      rfl

private theorem sum_sq_image_fiber_eq_cross_rectangular
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

private theorem sum_sq_image_fiber_filter_eq_cross_rectangular
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (key : α → β) (c : α → ℝ)
    (pred : β → Prop) [DecidablePred pred] :
    (∑ y ∈ (S.image key).filter pred,
        (∑ x ∈ S.filter (fun x => key x = y), c x) ^ 2) =
      ∑ x ∈ S, ∑ z ∈ S,
        if key z = key x ∧ pred (key x) then c x * c z else 0 := by
  classical
  let S' := S.filter (fun x => pred (key x))
  have hsupport : S'.image key = (S.image key).filter pred := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr
            ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩,
          (Finset.mem_filter.mp hx).2⟩
    · intro hy
      rcases Finset.mem_filter.mp hy with ⟨hyImage, hpred⟩
      rcases Finset.mem_image.mp hyImage with ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨hx, hpred⟩, rfl⟩
  have hfiber (y : β) (hy : pred y) :
      S'.filter (fun x => key x = y) =
        S.filter (fun x => key x = y) := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
          (Finset.mem_filter.mp hx).2⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxS, hkey⟩
      have hxPred : pred (key x) := by simpa [hkey] using hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hxS, hxPred⟩, hkey⟩
  calc
    (∑ y ∈ (S.image key).filter pred,
        (∑ x ∈ S.filter (fun x => key x = y), c x) ^ 2) =
        ∑ y ∈ S'.image key,
          (∑ x ∈ S.filter (fun x => key x = y), c x) ^ 2 := by
      rw [hsupport]
    _ = ∑ y ∈ S'.image key,
          (∑ x ∈ S'.filter (fun x => key x = y), c x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      rw [hfiber]
      exact (Finset.mem_filter.mp hx).2
    _ = ∑ x ∈ S', ∑ z ∈ S',
          if key z = key x then c x * c z else 0 :=
      sum_sq_image_fiber_eq_cross_rectangular S' key c
    _ = ∑ x ∈ S, ∑ z ∈ S,
          if key z = key x ∧ pred (key x) then c x * c z else 0 := by
      simp only [S', Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxPred : pred (key x)
      · rw [if_pos hxPred]
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hkey : key z = key x
        · have hzPred : pred (key z) := by simpa [hkey] using hxPred
          simp [hkey, hxPred]
        · simp [hkey, hxPred]
      · simp [hxPred]

private def swapRectangularNumerators
    (x : (ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) :
    (ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) :=
  ((x.1.1, x.1.2.1, x.2.2.2),
    (x.2.1, x.2.2.1, x.1.2.2))

private theorem swapRectangularNumerators_involutive :
    Function.Involutive swapRectangularNumerators := by
  intro x
  rcases x with ⟨⟨m, d, l⟩, ⟨m', d', l'⟩⟩
  rfl

private theorem swapRectangularNumerators_mem
    {N X : ℕ}
    {x : (ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))}
    (hx : x ∈ (selbergSqrtZetaSignedPhaseSupport N X).product
        (selbergSqrtZetaSignedPhaseSupport N X)) :
    swapRectangularNumerators x ∈
      (selbergSqrtZetaSignedPhaseSupport N X).product
        (selbergSqrtZetaSignedPhaseSupport N X) := by
  rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
  rcases Finset.mem_product.mp hx1 with ⟨hm, hdl⟩
  rcases Finset.mem_product.mp hdl with ⟨hd, hl⟩
  rcases Finset.mem_product.mp hx2 with ⟨hm', hdl'⟩
  rcases Finset.mem_product.mp hdl' with ⟨hd', hl'⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr
        ⟨hm, Finset.mem_product.mpr ⟨hd, hl'⟩⟩,
      Finset.mem_product.mpr
        ⟨hm', Finset.mem_product.mpr ⟨hd', hl⟩⟩⟩

private theorem rationalKey_eq_iff_swappedProductKey_eq
    {N X : ℕ} {p r : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedPhaseSupport N X) :
    selbergSqrtZetaSignedRationalKey r =
        selbergSqrtZetaSignedRationalKey p ↔
      selbergSqrtZetaRectangularProductKey
          (r.1, r.2.1, p.2.2) =
        selbergSqrtZetaRectangularProductKey
          (p.1, p.2.1, r.2.2) := by
  have hpDen : 0 < p.1 * p.2.1 := by
    rcases Finset.mem_product.mp hp with ⟨hm, hdl⟩
    exact Nat.mul_pos (Finset.mem_Icc.mp hm).1
      (Finset.mem_Icc.mp (Finset.mem_product.mp hdl).1).1
  have hrDen : 0 < r.1 * r.2.1 := by
    rcases Finset.mem_product.mp hr with ⟨hm, hdl⟩
    exact Nat.mul_pos (Finset.mem_Icc.mp hm).1
      (Finset.mem_Icc.mp (Finset.mem_product.mp hdl).1).1
  unfold selbergSqrtZetaSignedRationalKey
    selbergSqrtZetaRectangularProductKey
  rw [div_eq_div_iff]
  · norm_cast
    change
      r.2.2 * (p.1 * p.2.1) = p.2.2 * (r.1 * r.2.1) ↔
        r.1 * r.2.1 * p.2.2 = p.1 * p.2.1 * r.2.2
    constructor
    · intro h
      calc
        r.1 * r.2.1 * p.2.2 = p.2.2 * (r.1 * r.2.1) := by ac_rfl
        _ = r.2.2 * (p.1 * p.2.1) := h.symm
        _ = p.1 * p.2.1 * r.2.2 := by ac_rfl
    · intro h
      calc
        r.2.2 * (p.1 * p.2.1) = p.1 * p.2.1 * r.2.2 := by ac_rfl
        _ = r.1 * r.2.1 * p.2.2 := h.symm
        _ = p.2.2 * (r.1 * r.2.1) := by ac_rfl
  · exact_mod_cast hrDen.ne'
  · exact_mod_cast hpDen.ne'

private theorem rawCoeff_mul_swapRectangularNumerators
    (X : ℕ)
    (x : (ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) :
    selbergSqrtZetaRectangularRawCoeff X x.1 *
        selbergSqrtZetaRectangularRawCoeff X x.2 =
      selbergSqrtZetaRectangularRawCoeff X
          (swapRectangularNumerators x).1 *
        selbergSqrtZetaRectangularRawCoeff X
          (swapRectangularNumerators x).2 := by
  rcases x with ⟨⟨m, d, l⟩, ⟨m', d', l'⟩⟩
  simp only [swapRectangularNumerators,
    selbergSqrtZetaRectangularRawCoeff,
    selbergSqrtZetaSignedPhaseCoeff]
  simp
  ring

/-- The mixed product produced on the first component when the two numerator
coordinates are exchanged. -/
def selbergSqrtZetaRectangularMixedProductKey
    (p r : ℕ × (ℕ × ℕ)) : ℕ :=
  p.1 * p.2.1 * r.2.2

/-- Signed rational correlation restricted to pairs whose mixed product lies
above `K`.  Unlike the full rational energy, this remembers the original
integer-product tail condition through the numerator exchange. -/
noncomputable def selbergSqrtZetaSignedRationalMixedProductTailEnergy
    (N X K : ℕ) : ℝ :=
  ∑ p ∈ selbergSqrtZetaSignedPhaseSupport N X,
    ∑ r ∈ selbergSqrtZetaSignedPhaseSupport N X,
      if selbergSqrtZetaSignedRationalKey r =
            selbergSqrtZetaSignedRationalKey p ∧
          K < selbergSqrtZetaRectangularMixedProductKey p r
      then selbergSqrtZetaRectangularRawCoeff X p *
        selbergSqrtZetaRectangularRawCoeff X r
      else 0

private theorem rectangular_ratio_energy_eq_product_energy
    (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        (∑ p ∈ selbergSqrtZetaSignedRationalFiber N X q,
          selbergSqrtZetaRectangularRawCoeff X p) ^ 2) =
      ∑ k ∈ selbergSqrtZetaRectangularProductSupport N X,
        (∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
            (fun p => selbergSqrtZetaRectangularProductKey p = k),
          selbergSqrtZetaRectangularRawCoeff X p) ^ 2 := by
  classical
  let P := selbergSqrtZetaSignedPhaseSupport N X
  let c := selbergSqrtZetaRectangularRawCoeff X
  unfold selbergSqrtZetaSignedRationalSupport
    selbergSqrtZetaSignedRationalFiber
    selbergSqrtZetaRectangularProductSupport
  rw [sum_sq_image_fiber_eq_cross_rectangular P
      selbergSqrtZetaSignedRationalKey c,
    sum_sq_image_fiber_eq_cross_rectangular P
      selbergSqrtZetaRectangularProductKey c]
  change
    (∑ p ∈ P, ∑ r ∈ P,
      if selbergSqrtZetaSignedRationalKey r =
          selbergSqrtZetaSignedRationalKey p
      then c p * c r else 0) =
    ∑ p ∈ P, ∑ r ∈ P,
      if selbergSqrtZetaRectangularProductKey r =
          selbergSqrtZetaRectangularProductKey p
      then c p * c r else 0
  calc
    (∑ p ∈ P, ∑ r ∈ P,
        if selbergSqrtZetaSignedRationalKey r =
            selbergSqrtZetaSignedRationalKey p
        then c p * c r else 0) =
        ∑ x ∈ P.product P,
          if selbergSqrtZetaSignedRationalKey x.2 =
              selbergSqrtZetaSignedRationalKey x.1
          then c x.1 * c x.2 else 0 := by
      exact
        (Finset.sum_product P P
          (fun x : (ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) =>
            if selbergSqrtZetaSignedRationalKey x.2 =
                selbergSqrtZetaSignedRationalKey x.1
            then c x.1 * c x.2 else 0)).symm
    _ = ∑ x ∈ P.product P,
          if selbergSqrtZetaRectangularProductKey x.2 =
              selbergSqrtZetaRectangularProductKey x.1
          then c x.1 * c x.2 else 0 := by
      refine Finset.sum_bij
        (fun x _hx => swapRectangularNumerators x) ?_ ?_ ?_ ?_
      · intro x hx
        exact swapRectangularNumerators_mem hx
      · intro x _hx y _hy hxy
        exact swapRectangularNumerators_involutive.injective hxy
      · intro y hy
        refine ⟨swapRectangularNumerators y,
          swapRectangularNumerators_mem hy, ?_⟩
        exact swapRectangularNumerators_involutive y
      · intro x hx
        have hx' := Finset.mem_product.mp hx
        have hkey := rationalKey_eq_iff_swappedProductKey_eq hx'.1 hx'.2
        have hkeySwap :
            selbergSqrtZetaSignedRationalKey x.2 =
                selbergSqrtZetaSignedRationalKey x.1 ↔
              selbergSqrtZetaRectangularProductKey
                  (swapRectangularNumerators x).2 =
                selbergSqrtZetaRectangularProductKey
                  (swapRectangularNumerators x).1 := by
          simpa only [swapRectangularNumerators] using hkey
        change
          (if selbergSqrtZetaSignedRationalKey x.2 =
              selbergSqrtZetaSignedRationalKey x.1
            then c x.1 * c x.2 else 0) =
          if selbergSqrtZetaRectangularProductKey
                (swapRectangularNumerators x).2 =
              selbergSqrtZetaRectangularProductKey
                (swapRectangularNumerators x).1
          then c (swapRectangularNumerators x).1 *
            c (swapRectangularNumerators x).2 else 0
        by_cases hratio : selbergSqrtZetaSignedRationalKey x.2 =
            selbergSqrtZetaSignedRationalKey x.1
        · rw [if_pos hratio, if_pos (hkeySwap.mp hratio)]
          exact rawCoeff_mul_swapRectangularNumerators X x
        · have hprod :
              selbergSqrtZetaRectangularProductKey
                  (swapRectangularNumerators x).2 ≠
                selbergSqrtZetaRectangularProductKey
                  (swapRectangularNumerators x).1 := by
            intro h
            exact hratio (hkeySwap.mpr h)
          rw [if_neg hratio, if_neg hprod]
    _ = ∑ p ∈ P, ∑ r ∈ P,
          if selbergSqrtZetaRectangularProductKey r =
              selbergSqrtZetaRectangularProductKey p
          then c p * c r else 0 := Finset.sum_product P P _

private theorem
    rectangular_ratio_mixed_tail_energy_eq_product_tail_energy
    (N X K : ℕ) :
    selbergSqrtZetaSignedRationalMixedProductTailEnergy N X K =
      ∑ k ∈ (selbergSqrtZetaRectangularProductSupport N X).filter
          (fun k => K < k),
        (∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
            (fun p => selbergSqrtZetaRectangularProductKey p = k),
          selbergSqrtZetaRectangularRawCoeff X p) ^ 2 := by
  classical
  let P := selbergSqrtZetaSignedPhaseSupport N X
  let c := selbergSqrtZetaRectangularRawCoeff X
  unfold selbergSqrtZetaSignedRationalMixedProductTailEnergy
    selbergSqrtZetaRectangularProductSupport
  rw [sum_sq_image_fiber_filter_eq_cross_rectangular P
      selbergSqrtZetaRectangularProductKey c (fun k => K < k)]
  change
    (∑ p ∈ P, ∑ r ∈ P,
      if selbergSqrtZetaSignedRationalKey r =
            selbergSqrtZetaSignedRationalKey p ∧
          K < selbergSqrtZetaRectangularMixedProductKey p r
      then c p * c r else 0) =
    ∑ p ∈ P, ∑ r ∈ P,
      if selbergSqrtZetaRectangularProductKey r =
            selbergSqrtZetaRectangularProductKey p ∧
          K < selbergSqrtZetaRectangularProductKey p
      then c p * c r else 0
  calc
    (∑ p ∈ P, ∑ r ∈ P,
        if selbergSqrtZetaSignedRationalKey r =
              selbergSqrtZetaSignedRationalKey p ∧
            K < selbergSqrtZetaRectangularMixedProductKey p r
        then c p * c r else 0) =
        ∑ x ∈ P.product P,
          if selbergSqrtZetaSignedRationalKey x.2 =
                selbergSqrtZetaSignedRationalKey x.1 ∧
              K < selbergSqrtZetaRectangularMixedProductKey x.1 x.2
          then c x.1 * c x.2 else 0 := by
      exact
        (Finset.sum_product P P
          (fun x : (ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) =>
            if selbergSqrtZetaSignedRationalKey x.2 =
                  selbergSqrtZetaSignedRationalKey x.1 ∧
                K < selbergSqrtZetaRectangularMixedProductKey x.1 x.2
            then c x.1 * c x.2 else 0)).symm
    _ = ∑ x ∈ P.product P,
          if selbergSqrtZetaRectangularProductKey x.2 =
                selbergSqrtZetaRectangularProductKey x.1 ∧
              K < selbergSqrtZetaRectangularProductKey x.1
          then c x.1 * c x.2 else 0 := by
      refine Finset.sum_bij
        (fun x _hx => swapRectangularNumerators x) ?_ ?_ ?_ ?_
      · intro x hx
        exact swapRectangularNumerators_mem hx
      · intro x _hx y _hy hxy
        exact swapRectangularNumerators_involutive.injective hxy
      · intro y hy
        refine ⟨swapRectangularNumerators y,
          swapRectangularNumerators_mem hy, ?_⟩
        exact swapRectangularNumerators_involutive y
      · intro x hx
        have hx' := Finset.mem_product.mp hx
        have hkey := rationalKey_eq_iff_swappedProductKey_eq hx'.1 hx'.2
        have hkeySwap :
            selbergSqrtZetaSignedRationalKey x.2 =
                selbergSqrtZetaSignedRationalKey x.1 ↔
              selbergSqrtZetaRectangularProductKey
                  (swapRectangularNumerators x).2 =
                selbergSqrtZetaRectangularProductKey
                  (swapRectangularNumerators x).1 := by
          simpa only [swapRectangularNumerators] using hkey
        have htailSwap :
            K < selbergSqrtZetaRectangularMixedProductKey x.1 x.2 ↔
              K < selbergSqrtZetaRectangularProductKey
                (swapRectangularNumerators x).1 := by
          rfl
        change
          (if selbergSqrtZetaSignedRationalKey x.2 =
                selbergSqrtZetaSignedRationalKey x.1 ∧
              K < selbergSqrtZetaRectangularMixedProductKey x.1 x.2
            then c x.1 * c x.2 else 0) =
          if selbergSqrtZetaRectangularProductKey
                  (swapRectangularNumerators x).2 =
                selbergSqrtZetaRectangularProductKey
                  (swapRectangularNumerators x).1 ∧
              K < selbergSqrtZetaRectangularProductKey
                (swapRectangularNumerators x).1
          then c (swapRectangularNumerators x).1 *
            c (swapRectangularNumerators x).2 else 0
        by_cases hsource :
            selbergSqrtZetaSignedRationalKey x.2 =
                selbergSqrtZetaSignedRationalKey x.1 ∧
              K < selbergSqrtZetaRectangularMixedProductKey x.1 x.2
        · rw [if_pos hsource,
            if_pos ⟨hkeySwap.mp hsource.1, htailSwap.mp hsource.2⟩]
          exact rawCoeff_mul_swapRectangularNumerators X x
        · rw [if_neg hsource]
          symm
          apply if_neg
          intro htarget
          exact hsource
            ⟨hkeySwap.mpr htarget.1, htailSwap.mpr htarget.2⟩
    _ = ∑ p ∈ P, ∑ r ∈ P,
          if selbergSqrtZetaRectangularProductKey r =
                selbergSqrtZetaRectangularProductKey p ∧
              K < selbergSqrtZetaRectangularProductKey p
          then c p * c r else 0 := Finset.sum_product P P _

/-- Every actually represented rectangular product lies in the explicit
positive product interval used by the collected short polynomial. -/
theorem selbergSqrtZetaRectangularProductSupport_subset_collectedSupport
    (N X : ℕ) :
    selbergSqrtZetaRectangularProductSupport N X ⊆
      selbergShortDirichletCollectedSupport N X := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hm, hdl⟩
  rcases Finset.mem_product.mp hdl with ⟨hd, hl⟩
  rcases Finset.mem_Icc.mp hm with ⟨hm1, hmN⟩
  rcases Finset.mem_Icc.mp hd with ⟨hd1, hdX⟩
  rcases Finset.mem_Icc.mp hl with ⟨hl1, hlX⟩
  exact Finset.mem_Icc.mpr
    ⟨Nat.mul_pos (Nat.mul_pos hm1 hd1) hl1,
      Nat.mul_le_mul (Nat.mul_le_mul hmN hdX) hlX⟩

/-- An index outside the actually represented product image has zero finite
collected coefficient. -/
theorem
    selbergSqrtZetaShortDirichletCollectedCoeff_eq_zero_of_not_mem_rectangularProductSupport
    {N X k : ℕ}
    (hk : k ∉ selbergSqrtZetaRectangularProductSupport N X) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X k = 0 := by
  rw [selbergSqrtZetaShortDirichletCollectedCoeff_eq_ofReal_rawProductFiberSum]
  simp only [ofReal_eq_zero]
  apply Finset.sum_eq_zero
  intro p hp
  exact False.elim
    (hk (Finset.mem_image.mpr
      ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩))

/-- Exact rectangular multiplicative Parseval on the products that actually
occur.  The left side uses the repository's genuine finite short Dirichlet
coefficient; the right side uses the genuine signed rational coefficient.
No absolute-value majorant or fiber-cardinality loss is introduced. -/
theorem
    sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_rectangularProductSupport_eq_signedRationalEnergy
    (N X : ℕ) :
    (∑ k ∈ selbergSqrtZetaRectangularProductSupport N X,
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k)) =
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X q) := by
  classical
  calc
    (∑ k ∈ selbergSqrtZetaRectangularProductSupport N X,
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k)) =
        ∑ k ∈ selbergSqrtZetaRectangularProductSupport N X,
          (∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
              (fun p => selbergSqrtZetaRectangularProductKey p = k),
            selbergSqrtZetaRectangularRawCoeff X p) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [selbergSqrtZetaShortDirichletCollectedCoeff_eq_ofReal_rawProductFiberSum]
      simp [Complex.normSq_apply, pow_two]
    _ = ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          (∑ p ∈ selbergSqrtZetaSignedRationalFiber N X q,
            selbergSqrtZetaRectangularRawCoeff X p) ^ 2 :=
      (rectangular_ratio_energy_eq_product_energy N X).symm
    _ = ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedRationalCoeff N X q) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [selbergSqrtZetaSignedRationalCoeff_eq_ofReal_rawFiberSum]
      simp [Complex.normSq_apply, pow_two]

/-- Exact filtered rectangular Parseval identity for the genuine product tail.
The right side retains the mixed-product cutoff created by exchanging the two
numerator coordinates, rather than enlarging the tail to the full rational
coefficient energy. -/
theorem
    sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_rectangularProductTail_eq_signedRationalMixedProductTailEnergy
    (N X K : ℕ) :
    (∑ k ∈ (selbergSqrtZetaRectangularProductSupport N X).filter
        (fun k => K < k),
      Complex.normSq
        (selbergSqrtZetaShortDirichletCollectedCoeff N X k)) =
      selbergSqrtZetaSignedRationalMixedProductTailEnergy N X K := by
  calc
    (∑ k ∈ (selbergSqrtZetaRectangularProductSupport N X).filter
        (fun k => K < k),
      Complex.normSq
        (selbergSqrtZetaShortDirichletCollectedCoeff N X k)) =
        ∑ k ∈ (selbergSqrtZetaRectangularProductSupport N X).filter
            (fun k => K < k),
          (∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
              (fun p => selbergSqrtZetaRectangularProductKey p = k),
            selbergSqrtZetaRectangularRawCoeff X p) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [selbergSqrtZetaShortDirichletCollectedCoeff_eq_ofReal_rawProductFiberSum]
      simp [Complex.normSq_apply, pow_two]
    _ = selbergSqrtZetaSignedRationalMixedProductTailEnergy N X K :=
      (rectangular_ratio_mixed_tail_energy_eq_product_tail_energy N X K).symm

/-- Although it is presented as a signed rational correlation, the filtered
mixed-product tail energy is nonnegative because it is exactly a sum of
squared collected product coefficients. -/
theorem selbergSqrtZetaSignedRationalMixedProductTailEnergy_nonneg
    (N X K : ℕ) :
    0 ≤ selbergSqrtZetaSignedRationalMixedProductTailEnergy N X K := by
  rw [←
    sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_rectangularProductTail_eq_signedRationalMixedProductTailEnergy]
  exact Finset.sum_nonneg (fun k _hk => Complex.normSq_nonneg _)

/-- Raising the product cutoff can only decrease the exact filtered tail
energy. -/
theorem selbergSqrtZetaSignedRationalMixedProductTailEnergy_antitone_cutoff
    (N X : ℕ) {K L : ℕ} (hKL : K ≤ L) :
    selbergSqrtZetaSignedRationalMixedProductTailEnergy N X L ≤
      selbergSqrtZetaSignedRationalMixedProductTailEnergy N X K := by
  rw [←
      sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_rectangularProductTail_eq_signedRationalMixedProductTailEnergy,
    ←
      sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_rectangularProductTail_eq_signedRationalMixedProductTailEnergy]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkSupport, hkL⟩
    exact Finset.mem_filter.mpr ⟨hkSupport, hKL.trans_lt hkL⟩
  · intro k _hk _hnot
    exact Complex.normSq_nonneg _

/-- The explicit interval tail equals the filtered mixed-product energy.  Any
interval point not represented by a rectangular triple has zero collected
coefficient, so no enlargement to the full rational energy is needed. -/
theorem
    sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_tail_eq_signedRationalMixedProductTailEnergy
    (N X : ℕ) :
    (∑ k ∈ Finset.Ioc N (N * X * X),
      Complex.normSq
        (selbergSqrtZetaShortDirichletCollectedCoeff N X k)) =
      selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N := by
  have hsubset :
      (selbergSqrtZetaRectangularProductSupport N X).filter
          (fun k => N < k) ⊆
        Finset.Ioc N (N * X * X) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkProduct, hkN⟩
    have hkCollected :=
      selbergSqrtZetaRectangularProductSupport_subset_collectedSupport N X
        hkProduct
    rw [selbergShortDirichletCollectedSupport] at hkCollected
    exact Finset.mem_Ioc.mpr ⟨hkN, (Finset.mem_Icc.mp hkCollected).2⟩
  calc
    (∑ k ∈ Finset.Ioc N (N * X * X),
      Complex.normSq
        (selbergSqrtZetaShortDirichletCollectedCoeff N X k)) =
        ∑ k ∈ (selbergSqrtZetaRectangularProductSupport N X).filter
            (fun k => N < k),
          Complex.normSq
            (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
      symm
      exact Finset.sum_subset hsubset
        (by
          intro k hkInterval hkNotFiltered
          have hkNotProduct :
              k ∉ selbergSqrtZetaRectangularProductSupport N X := by
            intro hkProduct
            exact hkNotFiltered
              (Finset.mem_filter.mpr
                ⟨hkProduct, (Finset.mem_Ioc.mp hkInterval).1⟩)
          rw [selbergSqrtZetaShortDirichletCollectedCoeff_eq_zero_of_not_mem_rectangularProductSupport
            hkNotProduct]
          simp)
    _ = selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N :=
      sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_rectangularProductTail_eq_signedRationalMixedProductTailEnergy
        N X N

private theorem
    normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_tail_le_logDecay_mul
    {N k : ℕ} (hN : 1 ≤ N) (hkN : N < k) (X : ℕ) (H : ℝ) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k) ≤
      (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
  have hN1 : (1 : ℝ) < (N + 1 : ℕ) := by
    exact_mod_cast (show 1 < N + 1 by omega)
  have hk1 : (1 : ℝ) < k := by
    exact_mod_cast (show 1 < k by omega)
  have hlogN : 0 < Real.log ((N + 1 : ℕ) : ℝ) := Real.log_pos hN1
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hNk : ((N + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (show N + 1 ≤ k by omega)
  have hlogMono :
      Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log (k : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (zero_lt_one.trans hN1) (zero_lt_one.trans hk1) hNk
  have hdiv :
      2 / Real.log (k : ℝ) ≤ 2 / Real.log ((N + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hlogN hlogMono
  have hfreq : selbergShortDirichletCollectedFrequency k ≠ 0 := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log]
    exact neg_ne_zero.mpr hlogk.ne'
  have hfreqAbs :
      |selbergShortDirichletCollectedFrequency k| = Real.log (k : ℝ) := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log, abs_neg,
      abs_of_pos hlogk]
  have hslide := MathlibAux.norm_slidingExponentialCoefficient_le_min
    (selbergSqrtZetaShortDirichletCollectedCoeff N X)
    selbergShortDirichletCollectedFrequency k hfreq (H := H)
  rw [hfreqAbs] at hslide
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖MathlibAux.slidingExponentialCoefficient H
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k‖ ^ 2 ≤
        (‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ *
          min |H| (2 / Real.log (k : ℝ))) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hslide
    _ ≤ (‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ *
          (2 / Real.log ((N + 1 : ℕ) : ℝ))) ^ 2 := by
      apply sq_le_sq₀ (by positivity) (by positivity) |>.2
      exact mul_le_mul_of_nonneg_left
        ((min_le_right _ _).trans hdiv) (norm_nonneg _)
    _ = (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
          Complex.normSq
            (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
      rw [Complex.normSq_eq_norm_sq]
      ring

/-- The sliding-window tail is controlled by the exact filtered mixed-product
energy.  This retains the high-frequency cutoff instead of enlarging the
right side to the entire rational coefficient energy. -/
theorem
    sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_tail_le_logDecay_mul_signedRationalMixedProductTailEnergy
    {N : ℕ} (hN : 1 ≤ N) (X : ℕ) (H : ℝ) :
    (∑ k ∈ Finset.Ioc N (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
        selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N := by
  calc
    (∑ k ∈ Finset.Ioc N (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
        ∑ k ∈ Finset.Ioc N (N * X * X),
          (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
            Complex.normSq
              (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact
        normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_tail_le_logDecay_mul
          hN (Finset.mem_Ioc.mp hk).1 X H
    _ = (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
        ∑ k ∈ Finset.Ioc N (N * X * X),
          Complex.normSq
            (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
      rw [Finset.mul_sum]
    _ = (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
        selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N := by
      rw [sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_tail_eq_signedRationalMixedProductTailEnergy]

/-- The same exact Parseval identity over the existing explicit interval
`1 <= k <= N*X*X`.  The additional interval points contribute zero because
they are not represented by a finite triple. -/
theorem sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_eq_signedRationalEnergy
    (N X : ℕ) :
    (∑ k ∈ selbergShortDirichletCollectedSupport N X,
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k)) =
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X q) := by
  classical
  rw [←
    sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_rectangularProductSupport_eq_signedRationalEnergy]
  symm
  exact Finset.sum_subset
    (selbergSqrtZetaRectangularProductSupport_subset_collectedSupport N X)
    (by
      intro k hk hnot
      rw [selbergSqrtZetaShortDirichletCollectedCoeff_eq_zero_of_not_mem_rectangularProductSupport
        hnot]
      simp)

/-- Exact decomposition of the full rational coefficient energy into the
integer-product block `k <= N` and the genuinely truncated product tail.
The latter keeps the mixed-product cutoff from filtered rectangular Parseval. -/
theorem
    sum_normSq_lowProduct_add_signedRationalMixedProductTailEnergy_eq_signedRationalEnergy
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (∑ k ∈ Finset.Icc 1 N,
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k)) +
        selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N =
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X q) := by
  have hNtop : N ≤ N * X * X := by
    calc
      N = N * 1 * 1 := by simp
      _ ≤ N * X * X := Nat.mul_le_mul (Nat.mul_le_mul_left N hX) hX
  have hsplit :
      Finset.Icc 1 N ∪ Finset.Ioc N (N * X * X) =
        Finset.Icc 1 (N * X * X) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisjoint :
      Disjoint (Finset.Icc 1 N) (Finset.Ioc N (N * X * X)) := by
    rw [Finset.disjoint_left]
    intro k hkLow hkTail
    simp only [Finset.mem_Icc] at hkLow
    simp only [Finset.mem_Ioc] at hkTail
    omega
  rw [←
    sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_tail_eq_signedRationalMixedProductTailEnergy
      N X]
  rw [← Finset.sum_union hdisjoint, hsplit, ← selbergShortDirichletCollectedSupport]
  exact
    sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_eq_signedRationalEnergy
      N X

/-- Subtractive form of the exact filtered-tail decomposition.  This is the
interface for combining a full reduced-pair energy estimate with a separately
controlled low-product block. -/
theorem
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_eq_signedRationalEnergy_sub_lowProduct
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N =
      (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedRationalCoeff N X q)) -
        ∑ k ∈ Finset.Icc 1 N,
          Complex.normSq
            (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
  linarith only
    [sum_normSq_lowProduct_add_signedRationalMixedProductTailEnergy_eq_signedRationalEnergy
      hN hX]

/-- The genuinely zeta-truncated product tail is controlled by the same exact
rational coefficient energy.  Since every tail frequency has `k > N`, the
sliding-window multiplier contributes the uniform decay
`(2 / log (N + 1))^2`; no separate tail majorant or fiber count is introduced. -/
theorem
    sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_tail_le_logDecay_mul_signedRationalEnergy
    {N : ℕ} (hN : 1 ≤ N) (X : ℕ) (H : ℝ) :
    (∑ k ∈ Finset.Ioc N (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedRationalCoeff N X q) := by
  have hsubset :
      Finset.Ioc N (N * X * X) ⊆
        selbergShortDirichletCollectedSupport N X := by
    intro k hk
    obtain ⟨hkN, hkTop⟩ := Finset.mem_Ioc.mp hk
    rw [selbergShortDirichletCollectedSupport]
    exact Finset.mem_Icc.mpr ⟨by omega, hkTop⟩
  calc
    (∑ k ∈ Finset.Ioc N (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
        ∑ k ∈ Finset.Ioc N (N * X * X),
          (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 * Complex.normSq
            (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact
        normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_tail_le_logDecay_mul
          hN (Finset.mem_Ioc.mp hk).1 X H
    _ = (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
        ∑ k ∈ Finset.Ioc N (N * X * X),
          Complex.normSq
            (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
      rw [Finset.mul_sum]
    _ ≤ (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
        ∑ k ∈ selbergShortDirichletCollectedSupport N X,
          Complex.normSq
            (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun k _hk _hnot => Complex.normSq_nonneg _)
      · positivity
    _ = (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedRationalCoeff N X q) := by
      rw [sum_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_eq_signedRationalEnergy]

end HardyTheorem
