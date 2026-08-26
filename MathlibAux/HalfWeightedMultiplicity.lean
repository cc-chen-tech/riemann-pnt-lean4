import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Half-weighted multiplicity counts

This file isolates the finite-counting algebra behind the last inequality in
Conrey's equation (40).  Zeros in the interior receive their full analytic
multiplicity, while zeros on the distinguished boundary receive half their
multiplicity.
-/

open scoped BigOperators

namespace MathlibAux

variable {alpha : Type*} [DecidableEq alpha]

/-- The full real-valued multiplicity mass of a finite zero set. -/
noncomputable def fullMultiplicityMass
    (zeros : Finset alpha) (multiplicity : alpha → ℕ) : ℝ :=
  ∑ x ∈ zeros, (multiplicity x : ℝ)

/-- The multiplicity mass lying on a distinguished finite boundary set. -/
noncomputable def boundaryMultiplicityMass
    (zeros boundary : Finset alpha) (multiplicity : alpha → ℕ) : ℝ :=
  ∑ x ∈ zeros, if x ∈ boundary then (multiplicity x : ℝ) else 0

/-- Full weight in the interior and half weight on the distinguished boundary. -/
noncomputable def halfWeightedMultiplicityMass
    (zeros boundary : Finset alpha) (multiplicity : alpha → ℕ) : ℝ :=
  ∑ x ∈ zeros,
    if x ∈ boundary then (multiplicity x : ℝ) / 2 else multiplicity x

/-- Twice the half-weighted count is the full count twice, minus the boundary
mass.  This is the exact identity used between the second and third lines of
Conrey's equation (40). -/
theorem two_mul_halfWeightedMultiplicityMass_eq
    (zeros boundary : Finset alpha) (multiplicity : alpha → ℕ) :
    2 * halfWeightedMultiplicityMass zeros boundary multiplicity =
      2 * fullMultiplicityMass zeros multiplicity -
        boundaryMultiplicityMass zeros boundary multiplicity := by
  unfold halfWeightedMultiplicityMass fullMultiplicityMass
    boundaryMultiplicityMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hboundary : x ∈ boundary
  · simp [hboundary]
    ring
  · simp [hboundary]

/-- Enlarging the zero set and increasing every retained multiplicity can only
increase the half-weighted count. -/
theorem halfWeightedMultiplicityMass_mono
    {zeros larger boundary : Finset alpha} {m n : alpha → ℕ}
    (hzeros : zeros ⊆ larger)
    (hm : ∀ x ∈ zeros, m x ≤ n x) :
    halfWeightedMultiplicityMass zeros boundary m ≤
      halfWeightedMultiplicityMass larger boundary n := by
  unfold halfWeightedMultiplicityMass
  calc
    (∑ x ∈ zeros, if x ∈ boundary then (m x : ℝ) / 2 else m x) ≤
        ∑ x ∈ zeros, if x ∈ boundary then (n x : ℝ) / 2 else n x := by
      apply Finset.sum_le_sum
      intro x hx
      have hmn : (m x : ℝ) ≤ n x := by exact_mod_cast hm x hx
      by_cases hboundary : x ∈ boundary
      · simp only [hboundary, if_pos]
        linarith
      · simp only [hboundary, if_false]
        exact hmn
    _ ≤ ∑ x ∈ larger,
        if x ∈ boundary then (n x : ℝ) / 2 else n x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hzeros
      intro x hx hnot
      by_cases hboundary : x ∈ boundary
      · simp only [hboundary, if_pos]
        positivity
      · simp [hboundary]

/-- If the distinguished-boundary mass of one zero family is bounded by that
of a larger/product family, then the latter half-weighted count yields exactly
the Conrey equation-(40) lower-bound direction after multiplying by `-2`. -/
theorem neg_two_mul_full_add_boundary_le_neg_two_mul_halfWeighted
    (vZeros productZeros boundary : Finset alpha)
    (vMultiplicity productMultiplicity : alpha → ℕ)
    (hboundary :
      boundaryMultiplicityMass vZeros boundary vMultiplicity ≤
        boundaryMultiplicityMass productZeros boundary productMultiplicity) :
    -2 * fullMultiplicityMass productZeros productMultiplicity +
        boundaryMultiplicityMass vZeros boundary vMultiplicity ≤
      -2 * halfWeightedMultiplicityMass
        productZeros boundary productMultiplicity := by
  have hidentity := two_mul_halfWeightedMultiplicityMass_eq
    productZeros boundary productMultiplicity
  linarith

end MathlibAux
