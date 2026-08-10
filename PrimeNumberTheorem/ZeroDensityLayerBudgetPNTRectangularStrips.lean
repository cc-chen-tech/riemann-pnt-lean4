import PrimeNumberTheorem.ZeroDensityLayerBudgetRelativeKernelBound

/-!
# Real-part and ordinate rectangles for the PNT zero kernel

The exact relative kernel of one zeta zero is

`x ^ (rho.re - 1) / ‖rho‖`.

A real-part strip alone controls the numerator but not the denominator.
This module therefore equips every positive-zero layer with both an upper
real-part endpoint `tau` and a positive lower ordinate `u`.  The resulting
pointwise kernel is `x ^ (tau - 1) / u`, while Carlson still counts the layer
at its lower real-part endpoint `sigma`.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem

/-- A finite two-dimensional classification of positive-height nontrivial
zeros.  The inherited `sigma` is the strict lower real-part endpoint used by
Carlson, `tau` is the upper real-part endpoint used by the kernel, and
`ordinateFloor` controls the denominator. -/
structure PositiveZeroRectangleInput (T : ℝ) (n : ℕ) : Type where
  toBucket : PositiveZeroBucketInput T n
  tau : Fin n → ℝ
  ordinateFloor : Fin n → ℝ
  ordinateFloor_pos : ∀ i, 0 < ordinateFloor i
  re_le_tau : ∀ i, ∀ rho ∈ toBucket.layer i, rho.re ≤ tau i
  ordinateFloor_le_im :
    ∀ i, ∀ rho ∈ toBucket.layer i, ordinateFloor i ≤ rho.im

/-- The multiplicity-weighted Carlson count times the exact rectangular
kernel majorant. -/
noncomputable def pntRelativeRectangleLayerBudget
    {T : ℝ} {n : ℕ} (input : PositiveZeroRectangleInput T n)
    (i : Fin n) (x : ℝ) : ℝ :=
  (x ^ (input.tau i - 1) / input.ordinateFloor i) *
    (ZeroDensity.zeroDensityCount (input.toBucket.sigma i) T : ℝ)

/-- Sum of all rectangular positive-zero layer budgets. -/
noncomputable def pntRelativeRectangleBudget
    {T : ℝ} {n : ℕ} (input : PositiveZeroRectangleInput T n)
    (x : ℝ) : ℝ :=
  ∑ i : Fin n, pntRelativeRectangleLayerBudget input i x

theorem pntRelativeRectangleLayerBudget_nonneg
    {T : ℝ} {n : ℕ} (input : PositiveZeroRectangleInput T n)
    (i : Fin n) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ pntRelativeRectangleLayerBudget input i x := by
  exact mul_nonneg
    (div_nonneg (Real.rpow_nonneg hx _)
      (input.ordinateFloor_pos i).le)
    (Nat.cast_nonneg _)

theorem pntRelativeRectangleBudget_nonneg
    {T : ℝ} {n : ℕ} (input : PositiveZeroRectangleInput T n)
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ pntRelativeRectangleBudget input x := by
  apply Finset.sum_nonneg
  intro i hi
  exact pntRelativeRectangleLayerBudget_nonneg input i x hx

/-- Upper real-part and lower ordinate endpoints give the exact rectangular
majorant for one simple relative PNT zero kernel. -/
theorem norm_pntRelativeSimpleZeroKernel_le_rectangle
    {x tau u : ℝ} (hx : 1 ≤ x) {rho : ℂ}
    (hu : 0 < u) (hfloor : u ≤ rho.im) (hre : rho.re ≤ tau) :
    ‖pntRelativeSimpleZeroKernel x rho‖ ≤
      x ^ (tau - 1) / u := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have himNorm : rho.im ≤ ‖rho‖ := by
    calc
      rho.im ≤ |rho.im| := le_abs_self _
      _ ≤ ‖rho‖ := Complex.abs_im_le_norm rho
  have huNorm : u ≤ ‖rho‖ := hfloor.trans himNorm
  have hnorm : 0 < ‖rho‖ := hu.trans_le huNorm
  have hrpow :
      x ^ (rho.re - 1) ≤ x ^ (tau - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx
      (sub_le_sub_right hre 1)
  have hpow0 : 0 ≤ x ^ (tau - 1) :=
    Real.rpow_nonneg hx0.le _
  rw [norm_pntRelativeSimpleZeroKernel_eq hx0 rho]
  calc
    x ^ (rho.re - 1) / ‖rho‖ ≤
        x ^ (tau - 1) / ‖rho‖ :=
      div_le_div_of_nonneg_right hrpow (norm_nonneg rho)
    _ ≤ x ^ (tau - 1) / u := by
      exact (div_le_div_iff₀ hnorm hu).2
        (mul_le_mul_of_nonneg_left huNorm hpow0)

/-- One rectangular layer is controlled by its multiplicity-weighted Carlson
count and its endpoint kernel. -/
theorem PositiveZeroRectangleInput.sum_norm_layer_le
    {T x : ℝ} {n : ℕ} (input : PositiveZeroRectangleInput T n)
    (i : Fin n) (hx : 1 ≤ x) :
    (∑ rho ∈ input.toBucket.layer i,
        ‖pntRelativeZeroContribution x rho‖) ≤
      pntRelativeRectangleLayerBudget input i x := by
  apply sum_norm_pntRelativeZeroContribution_le_kernel_mul_of_mass_le
  · exact div_nonneg
      (Real.rpow_nonneg (by positivity) _)
      (input.ordinateFloor_pos i).le
  · intro rho hrho
    exact norm_pntRelativeSimpleZeroKernel_le_rectangle hx
      (input.ordinateFloor_pos i)
      (input.ordinateFloor_le_im i rho hrho)
      (input.re_le_tau i rho hrho)
  · exact input.toBucket.layer_multiplicityMass_le_zeroDensityCount i

/-- The actual multiplicity-weighted positive-ordinate zero sum is bounded by
the complete rectangular Carlson budget. -/
theorem PositiveZeroRectangleInput.norm_positive_sum_le
    {T x : ℝ} {n : ℕ} (input : PositiveZeroRectangleInput T n)
    (hx : 1 ≤ x) :
    ‖∑ rho ∈ positiveNontrivialZerosFinset T,
        pntRelativeZeroContribution x rho‖ ≤
      pntRelativeRectangleBudget input x := by
  have hdecomp :
      (∑ rho ∈ positiveNontrivialZerosFinset T,
          pntRelativeZeroContribution x rho) =
        ∑ i : Fin n, ∑ rho ∈ input.toBucket.layer i,
          pntRelativeZeroContribution x rho :=
    input.toBucket.certificate.sum_decomposition
      (pntRelativeZeroContribution x)
  rw [hdecomp]
  calc
    ‖∑ i : Fin n, ∑ rho ∈ input.toBucket.layer i,
        pntRelativeZeroContribution x rho‖ ≤
        ∑ i : Fin n, ‖∑ rho ∈ input.toBucket.layer i,
          pntRelativeZeroContribution x rho‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ rho ∈ input.toBucket.layer i,
        ‖pntRelativeZeroContribution x rho‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ ≤ ∑ i : Fin n, pntRelativeRectangleLayerBudget input i x := by
      apply Finset.sum_le_sum
      intro i hi
      exact input.sum_norm_layer_le i hx
    _ = pntRelativeRectangleBudget input x := rfl

/-- Conjugation recovers the full finite zero sum.  The real-ordinate
contribution remains explicit because a positive ordinate floor cannot cover
it. -/
theorem PositiveZeroRectangleInput.norm_full_sum_le
    {T x : ℝ} {n : ℕ} (input : PositiveZeroRectangleInput T n)
    (hx : 1 ≤ x) :
    ‖∑ rho ∈ nontrivialZerosFinset T,
        pntRelativeZeroContribution x rho‖ ≤
      2 * pntRelativeRectangleBudget input x +
        ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
          pntRelativeZeroContribution x rho‖ := by
  let positiveSum :=
    ∑ rho ∈ positiveNontrivialZerosFinset T,
      pntRelativeZeroContribution x rho
  let negativeSum :=
    ∑ rho ∈ negativeNontrivialZerosFinset T,
      pntRelativeZeroContribution x rho
  let realSum :=
    ∑ rho ∈ realOrdinateNontrivialZerosFinset T,
      pntRelativeZeroContribution x rho
  have hdecomp :
      (∑ rho ∈ nontrivialZerosFinset T,
          pntRelativeZeroContribution x rho) =
        positiveSum + negativeSum + realSum :=
    finiteZeroSum_eq_positive_add_negative_add_real T
      (pntRelativeZeroContribution x)
  have hnegative : negativeSum = conj positiveSum := by
    apply sum_negative_eq_conj_sum_positive
    intro rho hrho
    exact pntRelativeZeroContribution_conj
      (zero_lt_one.trans_le hx)
      (mem_nontrivialZerosFinset.mp hrho).1
  have hpositive :
      ‖positiveSum‖ ≤ pntRelativeRectangleBudget input x :=
    input.norm_positive_sum_le hx
  rw [hdecomp]
  calc
    ‖positiveSum + negativeSum + realSum‖ ≤
        ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
      calc
        ‖positiveSum + negativeSum + realSum‖ ≤
            ‖positiveSum + negativeSum‖ + ‖realSum‖ := norm_add_le _ _
        _ ≤ ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
          gcongr
          exact norm_add_le _ _
    _ = 2 * ‖positiveSum‖ + ‖realSum‖ := by
      rw [hnegative, norm_conj]
      ring
    _ ≤ 2 * pntRelativeRectangleBudget input x + ‖realSum‖ := by
      gcongr

end PrimeNumberTheorem
