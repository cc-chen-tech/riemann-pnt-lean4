import HardyTheorem.SelbergSqrtZetaSignedCompleteDenominator
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Boundary scales on a signed Selberg coprime ray

The incomplete denominator fibers occupy a genuine harmonic tail, not an
arbitrary subset of the full scale range.  This module records the exact
product obstruction and confines every boundary scale to one explicit
interval.
-/

open scoped BigOperators

namespace HardyTheorem

/-- A boundary scale remains inside both original support products, but its
denominator key has crossed at least one of the two completeness cutoffs. -/
theorem selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_facts
    {N X a b d : ℕ}
    (hd :
      d ∈ selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b) :
    0 < d ∧
      0 < a ∧
      0 < b ∧
      a * d ≤ X ∧
      b * d ≤ N * X ∧
      (N < b * d ∨ X < b * d) := by
  rcases Finset.mem_filter.mp hd with ⟨hdScale, hdBoundary⟩
  rcases Finset.mem_filter.mp hdScale with ⟨_hdRange, hdPos, hdPair⟩
  rcases Finset.mem_product.mp hdPair with ⟨hbdSupport, hadSupport⟩
  have hbdPos :
      0 < b * d :=
    selbergSqrtZetaSignedDenominator_pos_of_mem hbdSupport
  have hbdBound :
      b * d ≤ N * X :=
    (selbergSqrtZetaSignedDenominator_bounds_of_mem hbdSupport).2
  change a * d ∈ Finset.Icc 1 X at hadSupport
  have hadBounds := Finset.mem_Icc.mp hadSupport
  have hadPos : 0 < a * d := lt_of_lt_of_le Nat.zero_lt_one hadBounds.1
  have haPos : 0 < a := Nat.pos_of_mul_pos_right hadPos
  have hbPos : 0 < b := Nat.pos_of_mul_pos_right hbdPos
  refine ⟨hdPos, haPos, hbPos, hadBounds.2, hbdBound, ?_⟩
  omega

/-- The boundary predicate has one exact lower endpoint: the denominator key
has crossed the smaller completeness cutoff. -/
theorem selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_eq_filter_min_div
    (N X a b : ℕ) (hb : 0 < b) :
    selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b =
      (selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b).filter
        (fun d => min N X / b < d) := by
  ext d
  simp only [selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport,
    Finset.mem_filter]
  constructor
  · rintro ⟨hdScale, hdBoundary⟩
    refine ⟨hdScale, (Nat.div_lt_iff_lt_mul hb).2 ?_⟩
    have hcross : min N X < b * d := by
      omega
    simpa [Nat.mul_comm] using hcross
  · rintro ⟨hdScale, hdLower⟩
    refine ⟨hdScale, ?_⟩
    have hcross : min N X < b * d := by
      have := (Nat.div_lt_iff_lt_mul hb).1 hdLower
      simpa [Nat.mul_comm] using this
    omega

/-- Every boundary scale belongs to a single explicit harmonic tail.  The
upper endpoint simultaneously retains the numerator cutoff and the full
denominator-product cutoff. -/
theorem selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_mem_Ioc
    {N X a b d : ℕ}
    (hd :
      d ∈ selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b) :
    d ∈ Finset.Ioc
      (min N X / b)
      (min (X / a) (N * X / b)) := by
  rcases selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_facts hd with
    ⟨_hdPos, haPos, hbPos, hadX, hbdNX, hcross⟩
  apply Finset.mem_Ioc.mpr
  constructor
  · apply (Nat.div_lt_iff_lt_mul hbPos).2
    have : min N X < b * d := by omega
    simpa [Nat.mul_comm] using this
  · apply le_min_iff.mpr
    constructor
    · apply (Nat.le_div_iff_mul_le haPos).2
      simpa [Nat.mul_comm] using hadX
    · apply (Nat.le_div_iff_mul_le hbPos).2
      simpa [Nat.mul_comm] using hbdNX

/-- Finset-level containment of the whole boundary support in its exact
one-dimensional tail interval. -/
theorem selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_subset_Ioc
    (N X a b : ℕ) :
    selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b ⊆
      Finset.Ioc
        (min N X / b)
        (min (X / a) (N * X / b)) := by
  intro d hd
  exact selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_mem_Ioc hd

/-- The number of boundary scales is bounded by the exact length of the same
tail interval; no ambient `N*X` or polynomial support bound is introduced. -/
theorem selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_card_le
    (N X a b : ℕ) :
    (selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b).card ≤
      min (X / a) (N * X / b) - min N X / b := by
  calc
    (selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b).card ≤
        (Finset.Ioc
          (min N X / b)
          (min (X / a) (N * X / b))).card :=
      Finset.card_le_card
        (selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_subset_Ioc
          N X a b)
    _ = min (X / a) (N * X / b) - min N X / b := by
      simp

/-- The harmonic mass of all boundary scales is dominated by the explicit
tail interval.  This retains the `1/d` weight needed for a later logarithmic
tail estimate. -/
theorem selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_sum_inv_le
    (N X a b : ℕ) :
    (∑ d ∈ selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
        (d : ℝ)⁻¹) ≤
      ∑ d ∈ Finset.Ioc
        (min N X / b)
        (min (X / a) (N * X / b)),
        (d : ℝ)⁻¹ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact
      selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_subset_Ioc
        N X a b
  · intro d _hd _hdNot
    positivity

end HardyTheorem
