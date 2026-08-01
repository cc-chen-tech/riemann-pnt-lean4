import PrimeNumberTheorem.ZeroDensityLayerBudgetDyadicSquareMultiplicityCapacity
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility

/-!
# Actual cubic two-height L2 tail capacity

This module keeps the third-order explicit-formula zero coefficient at cubic
order.  It converts the actual reciprocal-square multiplicity capacity into
the coefficient-square mass carrying the four additional powers of the zero
height.  Removing a finite exceptional set uses only nonnegative-mass
monotonicity.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

/-- Square mass of the actual cubic zero coefficients in one Carlson dyadic
strip.  The factorization displays the reciprocal-square capacity already
provided by the direct-L2 interface and the four extra cubic powers. -/
noncomputable def actualCubicDyadicStripSquareCapacity
    (x sigma tau : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
    ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
      (x ^ (2 * rho.re) / ‖rho‖ ^ 4)

/-- The same actual cubic square mass after deleting an arbitrary finite set
of zeros. -/
noncomputable def actualCubicDyadicStripSquareCapacityExcluding
    (x sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
    ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
      (x ^ (2 * rho.re) / ‖rho‖ ^ 4)

/-- Deleting a finite set cannot increase the nonnegative cubic coefficient
square mass.  No density estimate is specialized to the deleted set. -/
theorem actualCubicDyadicStripSquareCapacityExcluding_le
    (x sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (hx : 0 ≤ x) :
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
      actualCubicDyadicStripSquareCapacity x sigma tau n := by
  unfold actualCubicDyadicStripSquareCapacityExcluding
    actualCubicDyadicStripSquareCapacity
  exact Finset.sum_le_sum_of_subset_of_nonneg
    Finset.sdiff_subset
    (fun _ _ _ => mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
      (div_nonneg (Real.rpow_nonneg hx _) (by positivity)))

/-- On a dyadic strip, the four extra cubic denominator powers and the real
part cap reduce the cubic square mass to the reciprocal-square capacity. -/
theorem actualCubicDyadicStripSquareCapacityExcluding_le_reciprocal
    {x sigma tau : ℝ} {n : ℕ} (S : Finset ℂ) (hx : 1 ≤ x) :
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
      (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
          sigma tau n S := by
  have hterm :
      ∀ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
        ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
            (x ^ (2 * rho.re) / ‖rho‖ ^ 4) ≤
          ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
            (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) := by
    intro rho hrho
    have hstrip : rho ∈ actualCarlsonDyadicZeroStrip sigma tau n :=
      (Finset.mem_sdiff.mp hrho).1
    have hre : rho.re ≤ tau :=
      (Finset.mem_filter.mp hstrip).2
    have hshell : rho ∈ actualCarlsonDyadicZeroShell sigma n :=
      actualCarlsonDyadicZeroStrip_subset_shell sigma tau n hstrip
    have him : (2 : ℝ) ^ n < rho.im :=
      actualCarlsonDyadicZeroShell_im_gt hshell
    have hnorm : (2 : ℝ) ^ n ≤ ‖rho‖ :=
      him.le.trans (Complex.im_le_norm rho)
    have hxpow : x ^ (2 * rho.re) ≤ x ^ (2 * tau) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hfactor :
        x ^ (2 * rho.re) / ‖rho‖ ^ 4 ≤
          x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4 := by
      gcongr
    exact mul_le_mul_of_nonneg_left hfactor
      (div_nonneg (sq_nonneg _) (sq_nonneg _))
  unfold actualCubicDyadicStripSquareCapacityExcluding
    actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
  calc
    (∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
        ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
          (x ^ (2 * rho.re) / ‖rho‖ ^ 4)) ≤
        ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
          ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
            (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) :=
      Finset.sum_le_sum hterm
    _ = (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
          ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho _
      ring

/-- Actual zeta instance: one logarithmic multiplicity loss times the Carlson
linear count, with four additional dyadic denominator powers visible. -/
theorem exists_actualCubicDyadicStripSquareCapacityExcluding_le_count :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (x sigma tau : ℝ) (n : ℕ),
        1 ≤ x →
        4 ≤ (2 : ℝ) ^ n →
        ∀ S : Finset ℂ,
          actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
            (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
              (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
                (actualCarlsonDyadicCount sigma (n + 1) /
                  ((2 : ℝ) ^ n) ^ 2)) := by
  rcases
      exists_actualCarlsonDyadicStripSquareReciprocalCapacityExcluding_le_count
    with ⟨B, hB, hbound⟩
  refine ⟨B, hB, ?_⟩
  intro x sigma tau n hx hn S
  calc
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
        (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
          actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
            sigma tau n S :=
      actualCubicDyadicStripSquareCapacityExcluding_le_reciprocal S hx
    _ ≤ (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) /
            ((2 : ℝ) ^ n) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hbound sigma tau n hn S)
        (div_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _) (by positivity))

/-- The displayed product in the actual block bound has total denominator
power six. -/
theorem cubicDyadicCountProduct_eq_sixthPower
    (B x sigma tau : ℝ) (n : ℕ) :
    (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) /
            ((2 : ℝ) ^ n) ^ 2)) =
      B * x ^ (2 * tau) *
        (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) /
            ((2 : ℝ) ^ n) ^ 6) := by
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp [htwo]

end PrimeNumberTheorem
