import HardyTheorem.SelbergSqrtZetaRectangularParseval
import HardyTheorem.SelbergSqrtZetaSignedRationalCoefficientReducedPairEnergy
import HardyTheorem.SelbergSqrtZetaSignedReducedPairCompleteCancellation
import HardyTheorem.SelbergSqrtZetaSignedReducedRayBoundaryTaperEnergy

/-!
# Reduced-pair control of the filtered product tail

The exact filtered Parseval identity separates the low integer-product block
from the full signed rational coefficient energy.  Combining that subtraction
with the existing reduced-pair complete/boundary estimate retains the low block
instead of enlarging the filtered tail back to the full rational energy.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The mixed-product tail is bounded by the reduced-pair complete/boundary
budget after subtracting the exact low integer-product block.  This does not
remove the rational carrier: ratio-one terms can still occur above the product
cutoff. -/
theorem
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_le_reducedPairComplete_add_boundary_sub_lowProduct
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N ≤
      (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) +
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2)))) -
        ∑ k ∈ Finset.Icc 1 N,
          Complex.normSq
            (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
  rw [
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_eq_signedRationalEnergy_sub_lowProduct
      hN hX]
  exact sub_le_sub_right
    (sum_normSq_selbergSqrtZetaSignedRationalCoeff_le_reducedPairComplete_add_boundary
      N X) _

/-- After the complete reduced-ray contribution is evaluated by multiplicative
Parseval, the filtered tail is reduced to the high complete-product energy,
the boundary defect, and the exact low-product subtraction.  In particular,
the complete contribution no longer carries a loss depending on `N`. -/
theorem
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_le_completeProductHigh_add_boundary_sub_lowProduct
    {N X : ℕ} (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N ≤
      2 * (((X : ℝ) ^ 2 + 1) *
        ((19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X)) +
      2 *
        (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
          ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
            ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2) ^ 2)) -
      ∑ k ∈ Finset.Icc 1 N,
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
  have hN : 1 ≤ N := (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hXone : 1 ≤ X := hX.le
  have htail :=
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_le_reducedPairComplete_add_boundary_sub_lowProduct
      hN hXone
  have hcomplete :=
    sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_le_nineteen_fourths_add_high
      hNX hX hlarge
  have hsplit :
      (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) +
        2 * (((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2)))) =
        2 *
          (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
            ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayCompleteTerm
                  N X p.1 p.2) ^ 2)) +
        2 *
          (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
            ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
              ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (selbergSqrtZetaSignedReducedRayBoundaryTerm
                  N X p.1 p.2) ^ 2)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit] at htail
  exact htail.trans
    (sub_le_sub_right
      (add_le_add
        (mul_le_mul_of_nonneg_left hcomplete (by norm_num)) le_rfl) _)

/-- The reciprocal mass of a finite open-closed interval is exactly the
difference of the corresponding harmonic numbers. -/
theorem sum_inv_Ioc_eq_harmonic_sub
    {L U : ℕ} (hLU : L ≤ U) :
    (∑ d ∈ Finset.Ioc L U, (d : ℝ)⁻¹) =
      (harmonic U : ℝ) - (harmonic L : ℝ) := by
  have hdisj : Disjoint (Finset.Icc 1 L) (Finset.Ioc L U) := by
    rw [Finset.disjoint_left]
    intro d hdL hdU
    simp only [Finset.mem_Icc] at hdL
    simp only [Finset.mem_Ioc] at hdU
    omega
  have hunion : Finset.Icc 1 L ∪ Finset.Ioc L U = Finset.Icc 1 U := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsum := Finset.sum_union hdisj (f := fun d : ℕ => (d : ℝ)⁻¹)
  rw [hunion] at hsum
  rw [show (harmonic U : ℝ) =
      ∑ d ∈ Finset.Icc 1 U, (d : ℝ)⁻¹ by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast],
    show (harmonic L : ℝ) =
      ∑ d ∈ Finset.Icc 1 L, (d : ℝ)⁻¹ by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]]
  linarith

/-- Every canonical reduced numerator comes from the original numerator box,
and every canonical reduced denominator comes from the original denominator
product box. -/
theorem
    selbergSqrtZetaSignedRationalReducedPairSupport_coordinate_bounds
    {N X : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X) :
    p.1 ≤ X ∧ p.2 ≤ N * X := by
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
  rcases Finset.mem_image.mp hpFacts.2.2.2 with ⟨r, hr, hkey⟩
  rcases Finset.mem_product.mp hr with ⟨hm, hdl⟩
  rcases Finset.mem_product.mp hdl with ⟨hd, hl⟩
  have hmFacts := Finset.mem_Icc.mp hm
  have hdFacts := Finset.mem_Icc.mp hd
  have hlFacts := Finset.mem_Icc.mp hl
  have hkPos : 0 < r.1 * r.2.1 :=
    Nat.mul_pos hmFacts.1 hdFacts.1
  have hkey' :
      (r.2.2 : ℚ) / ((r.1 * r.2.1 : ℕ) : ℚ) =
        (p.1 : ℚ) / (p.2 : ℚ) := by
    simpa only [selbergSqrtZetaSignedRationalKey,
      selbergSqrtZetaSignedReducedPairKey] using hkey
  have hcrossQ :
      (r.2.2 : ℚ) * (p.2 : ℚ) =
        (p.1 : ℚ) * ((r.1 * r.2.1 : ℕ) : ℚ) :=
    (div_eq_div_iff
      (by exact_mod_cast hkPos.ne')
      (by exact_mod_cast hpFacts.2.1.ne')).mp hkey'
  have hcross :
      r.2.2 * p.2 = p.1 * (r.1 * r.2.1) := by
    exact_mod_cast hcrossQ
  have haDvd : p.1 ∣ r.2.2 := by
    apply hpFacts.2.2.1.dvd_of_dvd_mul_right
    rw [hcross]
    exact dvd_mul_right p.1 (r.1 * r.2.1)
  have hbDvd : p.2 ∣ r.1 * r.2.1 := by
    apply hpFacts.2.2.1.symm.dvd_of_dvd_mul_left
    rw [← hcross]
    exact dvd_mul_left p.2 r.2.2
  constructor
  · exact (Nat.le_of_dvd hlFacts.1 haDvd).trans hlFacts.2
  · exact
      (Nat.le_of_dvd hkPos hbDvd).trans
        (Nat.mul_le_mul hmFacts.2 hdFacts.2)

/-- The reciprocal scale tail on one boundary ray is bounded by the harmonic
mass allowed by its reduced numerator.  This keeps the numerator dependence
instead of replacing the tail by the global harmonic number. -/
theorem sum_inv_boundaryScaleIoc_le_harmonic_div
    (N X a b : ℕ) :
    (∑ d ∈ Finset.Ioc
        (min N X / b)
        (min (X / a) (N * X / b)),
        (d : ℝ)⁻¹) ≤
      (harmonic (X / a) : ℝ) := by
  rw [show (harmonic (X / a) : ℝ) =
      ∑ d ∈ Finset.Icc 1 (X / a), (d : ℝ)⁻¹ by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    have hdFacts := Finset.mem_Ioc.mp hd
    have hdPos : 0 < d :=
      lt_of_le_of_lt (Nat.zero_le _) hdFacts.1
    exact Finset.mem_Icc.mpr
      ⟨hdPos, hdFacts.2.trans (min_le_left _ _)⟩
  · intro d _hd _hnot
    positivity

/-- One reduced ray's contribution to the explicit boundary taper budget. -/
noncomputable def selbergSqrtZetaSignedRationalBoundaryTaperSummand
    (N X : ℕ) (p : ℕ × ℕ) : ℝ :=
    (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
      ((∑ d ∈ Finset.Ioc
          (min N X / p.2)
          (min (X / p.1) (N * X / p.2)),
          (d : ℝ)⁻¹) ^ 2 *
        (harmonic X : ℝ) *
        (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2))

/-- Pointwise harmonic-ray bound for one boundary-budget summand.  The
dependence on the reduced denominator remains as `1 / b`, while the scale
tail is compressed to `H_{X/a}`. -/
theorem
    selbergSqrtZetaSignedRationalBoundaryTaperSummand_le_harmonicRay
    (N X : ℕ) (p : ℕ × ℕ) :
    selbergSqrtZetaSignedRationalBoundaryTaperSummand N X p ≤
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        ((harmonic (X / p.1) : ℝ) ^ 2 *
          (harmonic X : ℝ) *
          (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2)) := by
  unfold selbergSqrtZetaSignedRationalBoundaryTaperSummand
  have htailNonneg :
      0 ≤ ∑ d ∈ Finset.Ioc
          (min N X / p.2)
          (min (X / p.1) (N * X / p.2)),
          (d : ℝ)⁻¹ := by
    apply Finset.sum_nonneg
    intro d _hd
    positivity
  have hharmNonneg : 0 ≤ (harmonic (X / p.1) : ℝ) := by
    rw [show (harmonic (X / p.1) : ℝ) =
        ∑ d ∈ Finset.Icc 1 (X / p.1), (d : ℝ)⁻¹ by
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
            Rat.cast_natCast]]
    positivity
  have hharmXNonneg : 0 ≤ (harmonic X : ℝ) := by
    rw [show (harmonic X : ℝ) =
        ∑ d ∈ Finset.Icc 1 X, (d : ℝ)⁻¹ by
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
            Rat.cast_natCast]]
    positivity
  have htailSq :
      (∑ d ∈ Finset.Ioc
          (min N X / p.2)
          (min (X / p.1) (N * X / p.2)),
          (d : ℝ)⁻¹) ^ 2 ≤
        (harmonic (X / p.1) : ℝ) ^ 2 :=
    (sq_le_sq₀ htailNonneg hharmNonneg).2
      (sum_inv_boundaryScaleIoc_le_harmonic_div N X p.1 p.2)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right htailSq hharmXNonneg

/-- Explicit full-support boundary budget retaining the reciprocal ray weight,
the exact containing harmonic tail, and the logarithmic taper saving. -/
noncomputable def selbergSqrtZetaSignedRationalBoundaryTaperBudget
    (N X : ℕ) : ℝ :=
  ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
    selbergSqrtZetaSignedRationalBoundaryTaperSummand N X p

/-- When the zeta cutoff contains the taper box, every explicit boundary
budget term on or above the rational carrier vanishes.  Thus the full budget
is exactly supported on reduced rays with numerator smaller than denominator;
in particular the `(1,1)` carrier contributes zero. -/
theorem
    selbergSqrtZetaSignedRationalBoundaryTaperBudget_eq_filter_numerator_lt_denominator
    {N X : ℕ} (hXN : X ≤ N) :
    selbergSqrtZetaSignedRationalBoundaryTaperBudget N X =
      ∑ p ∈
          (selbergSqrtZetaSignedRationalReducedPairSupport N X).filter
            (fun p => p.1 < p.2),
        selbergSqrtZetaSignedRationalBoundaryTaperSummand N X p := by
  classical
  unfold selbergSqrtZetaSignedRationalBoundaryTaperBudget
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
  have hba : p.2 ≤ p.1 := by
    simp only [Finset.mem_filter, hp, true_and] at hnot
    exact Nat.le_of_not_gt hnot
  have hdiv : X / p.1 ≤ X / p.2 :=
    Nat.div_le_div le_rfl hba hpFacts.2.1.ne'
  have hupper :
      min (X / p.1) (N * X / p.2) ≤ X / p.2 :=
    (min_le_left _ _).trans hdiv
  unfold selbergSqrtZetaSignedRationalBoundaryTaperSummand
  rw [Nat.min_eq_right hXN, Finset.Ioc_eq_empty_of_le hupper]
  simp

private theorem harmonic_cast_nonneg_mixedProductTail (K : ℕ) :
    0 ≤ (harmonic K : ℝ) := by
  rw [show (harmonic K : ℝ) =
      ∑ d ∈ Finset.Icc 1 K, (d : ℝ)⁻¹ by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]]
  positivity

/-- The full boundary taper budget is bounded by a one-dimensional harmonic
ray sum.  The proof expands only to the genuine triangular envelope
`1 ≤ a ≤ X`, `a < b ≤ N*X`; no support-cardinality factor is introduced. -/
theorem
    selbergSqrtZetaSignedRationalBoundaryTaperBudget_le_harmonicRaySum
    {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) :
    selbergSqrtZetaSignedRationalBoundaryTaperBudget N X ≤
      ∑ a ∈ Finset.Icc 1 X,
        (a : ℝ)⁻¹ *
          (harmonic (X / a) : ℝ) ^ 2 *
          ((harmonic (N * X) : ℝ) - (harmonic a : ℝ)) *
          (harmonic X : ℝ) *
          (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2) := by
  classical
  let majorant : ℕ × ℕ → ℝ := fun p =>
    (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
      ((harmonic (X / p.1) : ℝ) ^ 2 *
        (harmonic X : ℝ) *
        (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2))
  have hmajorantNonneg : ∀ p : ℕ × ℕ, 0 ≤ majorant p := by
    intro p
    unfold majorant
    exact mul_nonneg (by positivity)
      (mul_nonneg
        (mul_nonneg (sq_nonneg _)
          (harmonic_cast_nonneg_mixedProductTail X))
        (by positivity))
  have hsubset :
      (selbergSqrtZetaSignedRationalReducedPairSupport N X).filter
          (fun p => p.1 < p.2) ⊆
        ((Finset.Icc 1 X).product (Finset.Icc 1 (N * X))).filter
          (fun p => p.1 < p.2) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hpLt⟩
    have hpFacts :=
      selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hpSupport
    have hpBounds :=
      selbergSqrtZetaSignedRationalReducedPairSupport_coordinate_bounds
        hpSupport
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpFacts.1, hpBounds.1⟩,
          Finset.mem_Icc.mpr ⟨hpFacts.2.1, hpBounds.2⟩⟩,
        hpLt⟩
  rw [
    selbergSqrtZetaSignedRationalBoundaryTaperBudget_eq_filter_numerator_lt_denominator
      hXN]
  calc
    (∑ p ∈
        (selbergSqrtZetaSignedRationalReducedPairSupport N X).filter
          (fun p => p.1 < p.2),
        selbergSqrtZetaSignedRationalBoundaryTaperSummand N X p) ≤
        ∑ p ∈
          (selbergSqrtZetaSignedRationalReducedPairSupport N X).filter
            (fun p => p.1 < p.2),
          majorant p := by
      apply Finset.sum_le_sum
      intro p _hp
      exact
        selbergSqrtZetaSignedRationalBoundaryTaperSummand_le_harmonicRay
          N X p
    _ ≤ ∑ p ∈
          ((Finset.Icc 1 X).product (Finset.Icc 1 (N * X))).filter
            (fun p => p.1 < p.2),
          majorant p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro p _hp _hnot
        exact hmajorantNonneg p)
    _ = ∑ a ∈ Finset.Icc 1 X,
          ∑ b ∈ Finset.Ioc a (N * X), majorant (a, b) := by
      rw [Finset.sum_filter]
      calc
        (∑ p ∈ (Finset.Icc 1 X).product (Finset.Icc 1 (N * X)),
            if p.1 < p.2 then majorant p else 0) =
            ∑ a ∈ Finset.Icc 1 X,
              ∑ b ∈ Finset.Icc 1 (N * X),
                if a < b then majorant (a, b) else 0 := by
          exact Finset.sum_product _ _ _
        _ = ∑ a ∈ Finset.Icc 1 X,
              ∑ b ∈ Finset.Ioc a (N * X), majorant (a, b) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext b
            have haFacts := Finset.mem_Icc.mp ha
            simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
            omega
          · intro b _hb
            rfl
    _ = ∑ a ∈ Finset.Icc 1 X,
          (a : ℝ)⁻¹ *
            (harmonic (X / a) : ℝ) ^ 2 *
            ((harmonic (N * X) : ℝ) - (harmonic a : ℝ)) *
            (harmonic X : ℝ) *
            (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2) := by
      apply Finset.sum_congr rfl
      intro a ha
      have haFacts := Finset.mem_Icc.mp ha
      have hNPos : 0 < N := hX.trans hXN
      have haNX : a ≤ N * X :=
        haFacts.2.trans (Nat.le_mul_of_pos_left X hNPos)
      calc
        (∑ b ∈ Finset.Ioc a (N * X), majorant (a, b)) =
            ∑ b ∈ Finset.Ioc a (N * X),
              ((a : ℝ)⁻¹ *
                (harmonic (X / a) : ℝ) ^ 2 *
                (harmonic X : ℝ) *
                (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2)) *
                (b : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro b _hb
          unfold majorant
          simp only [Nat.cast_mul, mul_inv]
          ring
        _ = ((a : ℝ)⁻¹ *
                (harmonic (X / a) : ℝ) ^ 2 *
                (harmonic X : ℝ) *
                (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2)) *
              (∑ b ∈ Finset.Ioc a (N * X), (b : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
        _ = (a : ℝ)⁻¹ *
              (harmonic (X / a) : ℝ) ^ 2 *
              ((harmonic (N * X) : ℝ) - (harmonic a : ℝ)) *
              (harmonic X : ℝ) *
              (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2) := by
          rw [sum_inv_Ioc_eq_harmonic_sub haNX]
          ring

private theorem harmonic_cast_mono_mixedProductTail
    {L U : ℕ} (hLU : L ≤ U) :
    (harmonic L : ℝ) ≤ (harmonic U : ℝ) := by
  have hsumNonneg :
      0 ≤ ∑ d ∈ Finset.Ioc L U, (d : ℝ)⁻¹ := by
    positivity
  rw [sum_inv_Ioc_eq_harmonic_sub hLU] at hsumNonneg
  linarith

/-- A scalar harmonic-polynomial bound for the boundary budget.  This step
does replace `H_{X/a}` and `H_{NX}-H_a` by their endpoint maxima, but it still
introduces no finite-support cardinality or coefficientwise absolute-value
loss. -/
theorem
    selbergSqrtZetaSignedRationalBoundaryTaperBudget_le_harmonicPolynomial
    {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) :
    selbergSqrtZetaSignedRationalBoundaryTaperBudget N X ≤
      (harmonic X : ℝ) ^ 4 * (harmonic (N * X) : ℝ) *
        (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2) := by
  have hRay :=
    selbergSqrtZetaSignedRationalBoundaryTaperBudget_le_harmonicRaySum
      hX hXN
  calc
    selbergSqrtZetaSignedRationalBoundaryTaperBudget N X ≤
        ∑ a ∈ Finset.Icc 1 X,
          (a : ℝ)⁻¹ *
            (harmonic (X / a) : ℝ) ^ 2 *
            ((harmonic (N * X) : ℝ) - (harmonic a : ℝ)) *
            (harmonic X : ℝ) *
            (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2) := hRay
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          (a : ℝ)⁻¹ *
            (harmonic X : ℝ) ^ 2 *
            (harmonic (N * X) : ℝ) *
            (harmonic X : ℝ) *
            (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2) := by
      apply Finset.sum_le_sum
      intro a ha
      have haFacts := Finset.mem_Icc.mp ha
      have hNPos : 0 < N := hX.trans hXN
      have haNX : a ≤ N * X :=
        haFacts.2.trans (Nat.le_mul_of_pos_left X hNPos)
      have hdivH :
          (harmonic (X / a) : ℝ) ≤ (harmonic X : ℝ) :=
        harmonic_cast_mono_mixedProductTail (Nat.div_le_self X a)
      have hdivNonneg : 0 ≤ (harmonic (X / a) : ℝ) :=
        harmonic_cast_nonneg_mixedProductTail _
      have hXNonneg : 0 ≤ (harmonic X : ℝ) :=
        harmonic_cast_nonneg_mixedProductTail _
      have hsq :
          (harmonic (X / a) : ℝ) ^ 2 ≤ (harmonic X : ℝ) ^ 2 :=
        (sq_le_sq₀ hdivNonneg hXNonneg).2 hdivH
      have haH : (harmonic a : ℝ) ≤ (harmonic (N * X) : ℝ) :=
        harmonic_cast_mono_mixedProductTail haNX
      have hdiffNonneg :
          0 ≤ (harmonic (N * X) : ℝ) - (harmonic a : ℝ) := by
        linarith
      have hdiffLe :
          (harmonic (N * X) : ℝ) - (harmonic a : ℝ) ≤
            (harmonic (N * X) : ℝ) := by
        linarith [harmonic_cast_nonneg_mixedProductTail a]
      gcongr
    _ = ∑ a ∈ Finset.Icc 1 X,
          (a : ℝ)⁻¹ *
            ((harmonic X : ℝ) ^ 2 *
              (harmonic (N * X) : ℝ) *
              (harmonic X : ℝ) *
              (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = (∑ a ∈ Finset.Icc 1 X, (a : ℝ)⁻¹) *
          ((harmonic X : ℝ) ^ 2 *
            (harmonic (N * X) : ℝ) *
            (harmonic X : ℝ) *
            (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2)) := by
      rw [Finset.sum_mul]
    _ = (harmonic X : ℝ) *
          ((harmonic X : ℝ) ^ 2 *
            (harmonic (N * X) : ℝ) *
            (harmonic X : ℝ) *
            (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2)) := by
      rw [show (∑ a ∈ Finset.Icc 1 X, (a : ℝ)⁻¹) =
          (harmonic X : ℝ) by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]]
    _ = (harmonic X : ℝ) ^ 4 * (harmonic (N * X) : ℝ) *
          (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2) := by
      ring

/-- Replacing the harmonic factors by their standard logarithmic upper
bounds gives a completely explicit boundary-budget estimate. -/
theorem
    selbergSqrtZetaSignedRationalBoundaryTaperBudget_le_logPolynomial
    {N X : ℕ} (hX : 2 ≤ X) (hXN : X ≤ N) :
    selbergSqrtZetaSignedRationalBoundaryTaperBudget N X ≤
      (1 + Real.log X) ^ 4 * (1 + Real.log (N * X)) *
        (4 * (X : ℝ) ^ 2 / (Real.log X) ^ 2) := by
  have hPoly :=
    selbergSqrtZetaSignedRationalBoundaryTaperBudget_le_harmonicPolynomial
      (by omega) hXN
  have hHX : (harmonic X : ℝ) ≤ 1 + Real.log X :=
    harmonic_le_one_add_log X
  have hHNX : (harmonic (N * X) : ℝ) ≤ 1 + Real.log (N * X) :=
    by simpa only [Nat.cast_mul] using harmonic_le_one_add_log (N * X)
  have hHXNonneg : 0 ≤ (harmonic X : ℝ) :=
    harmonic_cast_nonneg_mixedProductTail _
  have hHNXNonneg : 0 ≤ (harmonic (N * X) : ℝ) :=
    harmonic_cast_nonneg_mixedProductTail _
  have hlogXNonneg : 0 ≤ 1 + Real.log X := by
    have : (0 : ℝ) ≤ Real.log X :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
    linarith
  have hlogNXNonneg : 0 ≤ 1 + Real.log (N * X) := by
    have hNX : 1 ≤ N * X :=
      Nat.mul_pos (by omega) (by omega)
    have : (0 : ℝ) ≤ Real.log (N * X) :=
      Real.log_nonneg (by exact_mod_cast hNX)
    linarith
  exact hPoly.trans (by
    gcongr)

/-- The unweighted boundary square sum is controlled by the explicit taper
budget.  Unlike the local-separation budget, this introduces no geometric
factor `X * min (a*N) b + 1`. -/
theorem sum_selbergSqrtZetaSignedRationalBoundaryPlain_le_boundaryTaperBudget
    {N X : ℕ} (hX : 2 ≤ X) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayBoundaryTerm
          N X p.1 p.2) ^ 2) ≤
      selbergSqrtZetaSignedRationalBoundaryTaperBudget N X := by
  unfold selbergSqrtZetaSignedRationalBoundaryTaperBudget
    selbergSqrtZetaSignedRationalBoundaryTaperSummand
  apply Finset.sum_le_sum
  intro p _hp
  exact mul_le_mul_of_nonneg_left
    (selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_four_mul_harmonicTail_sq_mul_harmonic_mul_sq_div_log_sq
      hX)
    (by positivity)

private theorem
    sum_selbergSqrtZetaSignedRationalCompletePlain_le_nineteen_fourths_add_high
    {N X : ℕ} (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayCompleteTerm
          N X p.1 p.2) ^ 2) ≤
      (19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X := by
  exact
    sum_selbergSqrtZetaSignedReducedPairCompletePlainEnergy_le_nineteen_fourths_add_high
      hNX hX hlarge

/-- Strong filtered-tail endpoint: the complete part has no `N` loss, the
boundary keeps its `1 / log(X)^2` taper saving, and the exact low-product
energy is still subtracted.  The remaining arithmetic tasks are precisely the
high complete-product energy and this explicit boundary budget. -/
theorem
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_le_completeProductHigh_add_boundaryTaper_sub_lowProduct
    {N X : ℕ} (hNX : X ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N ≤
      2 * ((19 : ℝ) / 4 + selbergSqrtZetaCompleteProductHighEnergy X) +
      2 * selbergSqrtZetaSignedRationalBoundaryTaperBudget N X -
      ∑ k ∈ Finset.Icc 1 N,
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
  have hN : 1 ≤ N := hX.le.trans hNX
  have hXone : 1 ≤ X := hX.le
  rw [
    selbergSqrtZetaSignedRationalMixedProductTailEnergy_eq_signedRationalEnergy_sub_lowProduct
      hN hXone,
    sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_reducedPairEnergy]
  apply sub_le_sub_right
  calc
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
      (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
        (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
          selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2) ≤
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (2 * ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm
            N X p.1 p.2) ^ 2) +
        2 * ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
          (selbergSqrtZetaSignedReducedRayBoundaryTerm
            N X p.1 p.2) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p _hp
        have hinv : 0 ≤ (((p.1 * p.2 : ℕ) : ℝ)⁻¹) := by positivity
        have hsplit :
            (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
              selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2 ≤
            2 * (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2 +
            2 * (selbergSqrtZetaSignedReducedRayBoundaryTerm
              N X p.1 p.2) ^ 2 := by
          nlinarith [sq_nonneg
            (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 -
              selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2)]
        calc
          (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayCompleteTerm N X p.1 p.2 +
                selbergSqrtZetaSignedReducedRayBoundaryTerm N X p.1 p.2) ^ 2 ≤
              (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
                (2 * (selbergSqrtZetaSignedReducedRayCompleteTerm
                    N X p.1 p.2) ^ 2 +
                  2 * (selbergSqrtZetaSignedReducedRayBoundaryTerm
                    N X p.1 p.2) ^ 2) :=
            mul_le_mul_of_nonneg_left hsplit hinv
          _ = _ := by ring
    _ = 2 *
          (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
            (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayCompleteTerm
                N X p.1 p.2) ^ 2) +
        2 *
          (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
            (((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayBoundaryTerm
                N X p.1 p.2) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left
        (sum_selbergSqrtZetaSignedRationalCompletePlain_le_nineteen_fourths_add_high
          hNX hX hlarge)
        (by norm_num))
      (mul_le_mul_of_nonneg_left
        (sum_selbergSqrtZetaSignedRationalBoundaryPlain_le_boundaryTaperBudget
          (by omega : 2 ≤ X))
        (by norm_num))

end HardyTheorem
