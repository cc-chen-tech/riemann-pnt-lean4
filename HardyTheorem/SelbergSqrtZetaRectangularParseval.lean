import HardyTheorem.SelbergSqrtZetaSignedRationalCoefficientEnergySharp
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

end HardyTheorem
