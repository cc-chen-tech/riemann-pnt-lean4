import PrimeNumberTheorem.HalfIsolatedZetaDyadicAdapter
import PrimeNumberTheorem.ZeroDensityLayerBudgetDyadicSquareMultiplicityCapacity

/-!
# A positive-ordinate dyadic zeta mass to Carlson-capacity bridge

This file compares the genuine multiplicity-weighted zeta mass used by the
dyadic Gaussian adapter with the square reciprocal capacity from the actual
Carlson zero strips.  Because the adapter uses the half-open absolute-height
block `[2^k, 2^(k+1))` while Carlson uses positive-height shells
`(2^n, 2^(n+1)]`, two adjacent Carlson shells are required.

Only the positive-ordinate half is treated here.  No Sharp lower bound,
repeatability statement, Carlson contradiction, or RH consequence is claimed.
-/

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

open scoped BigOperators

noncomputable section

/-- Right-strip dyadic bucket pairs of positive ordinate after deleting `S`. -/
def zetaRightDyadicPositivePairsExcluding
    (beta : ℝ) (k : ℕ) (S : Finset ℂ) : Finset (ℕ × ℂ) :=
  (zetaRightDyadicBucketPairs beta k).filter fun p =>
    0 < p.2.im ∧ p.2 ∉ S

/-- The corresponding unlabelled positive-ordinate zeros. -/
def zetaRightDyadicPositiveZerosExcluding
    (beta : ℝ) (k : ℕ) (S : Finset ℂ) : Finset ℂ :=
  (zetaRightDyadicPositivePairsExcluding beta k S).image Prod.snd

/-- The bucket-independent version of the Gaussian adapter's base mass. -/
def zetaDyadicBaseMassAt (x beta : ℝ) (rho : ℂ) : ℝ :=
  zeroReciprocalMultiplicityCoefficient rho * x ^ (rho.re - beta)

/-- Positive-ordinate square mass in one actual right dyadic block. -/
def zetaRightDyadicPositiveMassSquareExcluding
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ p ∈ zetaRightDyadicPositivePairsExcluding beta k S,
    zetaDyadicBaseMass x beta p ^ 2

/-- The union of the two Carlson shells needed to cover the adapter's
half-open dyadic block. -/
def actualCarlsonAdjacentDyadicStripExcluding
    (sigma tau : ℝ) (k : ℕ) (S : Finset ℂ) : Finset ℂ :=
  (actualCarlsonDyadicZeroStrip sigma tau (k - 1) \ S) ∪
    (actualCarlsonDyadicZeroStrip sigma tau k \ S)

/-- Square reciprocal capacity on the adjacent-shell union. -/
def actualCarlsonAdjacentDyadicStripSquareReciprocalCapacityExcluding
    (sigma tau : ℝ) (k : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ rho ∈ actualCarlsonAdjacentDyadicStripExcluding sigma tau k S,
    (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2

theorem zetaRightDyadicPositiveMassSquareExcluding_eq_sum_image
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) :
    zetaRightDyadicPositiveMassSquareExcluding x beta k S =
      ∑ rho ∈ zetaRightDyadicPositiveZerosExcluding beta k S,
        zetaDyadicBaseMassAt x beta rho ^ 2 := by
  have hinj : Set.InjOn Prod.snd
      (zetaRightDyadicPositivePairsExcluding beta k S : Set (ℕ × ℂ)) := by
    intro p hp q hq hpq
    exact zetaDyadicBucketPairs_snd_inj k
      (mem_zetaRightDyadicBucketPairs.mp (Finset.mem_filter.mp hp).1).1
      (mem_zetaRightDyadicBucketPairs.mp (Finset.mem_filter.mp hq).1).1 hpq
  rw [zetaRightDyadicPositiveMassSquareExcluding,
    zetaRightDyadicPositiveZerosExcluding]
  simpa [zetaDyadicBaseMassAt, zetaDyadicBaseMass] using
    (Finset.sum_image
      (f := fun rho : ℂ => zetaDyadicBaseMassAt x beta rho ^ 2) hinj).symm

theorem zetaDyadicBaseMassAt_sq_le_capacity_weight
    {x beta : ℝ} {rho : ℂ} (hx : 1 ≤ x) (hre : rho.re ≤ 1) :
    zetaDyadicBaseMassAt x beta rho ^ 2 ≤
      (x ^ (1 - beta)) ^ 2 *
        ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) := by
  have hcoeff : 0 ≤ zeroReciprocalMultiplicityCoefficient rho := by
    unfold zeroReciprocalMultiplicityCoefficient
    exact div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hsmall : x ^ (rho.re - beta) ≤ x ^ (1 - beta) :=
    Real.rpow_le_rpow_of_exponent_le hx (sub_le_sub_right hre beta)
  have hmul :
      zeroReciprocalMultiplicityCoefficient rho * x ^ (rho.re - beta) ≤
        zeroReciprocalMultiplicityCoefficient rho * x ^ (1 - beta) :=
    mul_le_mul_of_nonneg_left hsmall hcoeff
  have hleft :
      0 ≤ zeroReciprocalMultiplicityCoefficient rho * x ^ (rho.re - beta) :=
    mul_nonneg hcoeff (Real.rpow_nonneg hx0 _)
  have hright :
      0 ≤ zeroReciprocalMultiplicityCoefficient rho * x ^ (1 - beta) :=
    mul_nonneg hcoeff (Real.rpow_nonneg hx0 _)
  have hsq := (sq_le_sq₀ hleft hright).2 hmul
  calc
    zetaDyadicBaseMassAt x beta rho ^ 2 ≤
        (zeroReciprocalMultiplicityCoefficient rho * x ^ (1 - beta)) ^ 2 := by
      simpa [zetaDyadicBaseMassAt] using hsq
    _ = (x ^ (1 - beta)) ^ 2 *
        ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) := by
      rw [mul_pow, zeroReciprocalMultiplicityCoefficient, div_pow]
      ring

private theorem mem_actualCarlsonDyadicZeroStrip_of_bounds
    {sigma tau : ℝ} {n : ℕ} {rho : ℂ}
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (hpos : 0 < rho.im)
    (hlower : (2 : ℝ) ^ n < rho.im)
    (hupper : rho.im ≤ (2 : ℝ) ^ (n + 1))
    (hsigma : sigma < rho.re) (htau : rho.re ≤ tau) :
    rho ∈ actualCarlsonDyadicZeroStrip sigma tau n := by
  rw [actualCarlsonDyadicZeroStrip, Finset.mem_filter]
  refine ⟨?_, htau⟩
  rw [actualCarlsonDyadicZeroShell, Finset.mem_sdiff]
  refine ⟨ZeroDensity.mem_zeroDensityZerosFinset.mpr
    ⟨hzero, hpos, hupper, hsigma⟩, ?_⟩
  intro hlow
  exact (not_lt_of_ge
    (ZeroDensity.mem_zeroDensityZerosFinset.mp hlow).2.2.1) hlower

theorem zetaRightDyadicPositiveZerosExcluding_subset_adjacentCarlson
    {sigma beta : ℝ} {k : ℕ} {S : Finset ℂ}
    (hk : 1 ≤ k) (hsigma : sigma < beta) :
    zetaRightDyadicPositiveZerosExcluding beta k S ⊆
      actualCarlsonAdjacentDyadicStripExcluding sigma 1 k S := by
  intro rho hrho
  rcases Finset.mem_image.mp hrho with ⟨p, hp, rfl⟩
  have hpFilter := Finset.mem_filter.mp hp
  have hpRight := mem_zetaRightDyadicBucketPairs.mp hpFilter.1
  have hrhoMem : p.2 ∈ zetaRightDyadicZeros beta k :=
    Finset.mem_image.mpr ⟨p, hpFilter.1, rfl⟩
  have hspec := zetaRightDyadicZeros_spec hrhoMem
  have hpos := hpFilter.2.1
  have hnotS := hpFilter.2.2
  have hlower : (2 : ℝ) ^ k ≤ p.2.im := by
    simpa [abs_of_pos hpos] using hspec.2.1
  have hupper : p.2.im ≤ (2 : ℝ) ^ (k + 1) := by
    exact le_of_lt (by simpa [abs_of_pos hpos] using hspec.2.2.1)
  have hright : sigma < p.2.re := hsigma.trans_le hspec.2.2.2
  have hreOne : p.2.re ≤ 1 := hspec.1.2.2.le
  rw [actualCarlsonAdjacentDyadicStripExcluding, Finset.mem_union]
  by_cases hcurrent : (2 : ℝ) ^ k < p.2.im
  · right
    exact Finset.mem_sdiff.mpr
      ⟨mem_actualCarlsonDyadicZeroStrip_of_bounds hspec.1 hpos hcurrent
        hupper hright hreOne, hnotS⟩
  · left
    have himEq : p.2.im = (2 : ℝ) ^ k :=
      le_antisymm (le_of_not_gt hcurrent) hlower
    have hprevIndex : k - 1 < k := by omega
    have hprevLower : (2 : ℝ) ^ (k - 1) < p.2.im := by
      rw [himEq]
      exact pow_lt_pow_right₀ (by norm_num) hprevIndex
    have hprevUpper : p.2.im ≤ (2 : ℝ) ^ ((k - 1) + 1) := by
      rw [himEq, Nat.sub_add_cancel hk]
    exact Finset.mem_sdiff.mpr
      ⟨mem_actualCarlsonDyadicZeroStrip_of_bounds hspec.1 hpos hprevLower
        hprevUpper hright hreOne, hnotS⟩

theorem zetaRightDyadicPositiveMassSquareExcluding_le_adjacentCapacity
    {x sigma beta : ℝ} {k : ℕ} {S : Finset ℂ}
    (hx : 1 ≤ x) (hk : 1 ≤ k) (hsigma : sigma < beta) :
    zetaRightDyadicPositiveMassSquareExcluding x beta k S ≤
      (x ^ (1 - beta)) ^ 2 *
        actualCarlsonAdjacentDyadicStripSquareReciprocalCapacityExcluding
          sigma 1 k S := by
  rw [zetaRightDyadicPositiveMassSquareExcluding_eq_sum_image]
  calc
    (∑ rho ∈ zetaRightDyadicPositiveZerosExcluding beta k S,
        zetaDyadicBaseMassAt x beta rho ^ 2) ≤
        ∑ rho ∈ zetaRightDyadicPositiveZerosExcluding beta k S,
          (x ^ (1 - beta)) ^ 2 *
            ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hsub := zetaRightDyadicPositiveZerosExcluding_subset_adjacentCarlson
        hk hsigma hrho
      have hstrip := Finset.mem_union.mp hsub
      have hzero : RiemannHypothesis.IsNontrivialZero rho := by
        rcases hstrip with hprev | hcurrent
        · exact (ZeroDensity.mem_zeroDensityZerosFinset.mp
            (Finset.mem_sdiff.mp
              (actualCarlsonDyadicZeroStrip_subset_shell sigma 1 (k - 1)
                (Finset.mem_sdiff.mp hprev).1)).1).1
        · exact (ZeroDensity.mem_zeroDensityZerosFinset.mp
            (Finset.mem_sdiff.mp
              (actualCarlsonDyadicZeroStrip_subset_shell sigma 1 k
                (Finset.mem_sdiff.mp hcurrent).1)).1).1
      exact zetaDyadicBaseMassAt_sq_le_capacity_weight hx hzero.2.2.le
    _ ≤ ∑ rho ∈ actualCarlsonAdjacentDyadicStripExcluding sigma 1 k S,
          (x ^ (1 - beta)) ^ 2 *
            ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (zetaRightDyadicPositiveZerosExcluding_subset_adjacentCarlson hk hsigma)
      intro rho hrho hnot
      positivity
    _ = (x ^ (1 - beta)) ^ 2 *
        actualCarlsonAdjacentDyadicStripSquareReciprocalCapacityExcluding
          sigma 1 k S := by
      rw [actualCarlsonAdjacentDyadicStripSquareReciprocalCapacityExcluding,
        Finset.mul_sum]

theorem actualCarlsonAdjacentDyadicStripSquareReciprocalCapacityExcluding_le_add
    (sigma tau : ℝ) (k : ℕ) (S : Finset ℂ) :
    actualCarlsonAdjacentDyadicStripSquareReciprocalCapacityExcluding
        sigma tau k S ≤
      actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
          sigma tau (k - 1) S +
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma tau k S := by
  have hinter : 0 ≤
      ∑ rho ∈
        (actualCarlsonDyadicZeroStrip sigma tau (k - 1) \ S) ∩
          (actualCarlsonDyadicZeroStrip sigma tau k \ S),
        (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2 := by
    positivity
  have hunion := Finset.sum_union_inter
    (s₁ := actualCarlsonDyadicZeroStrip sigma tau (k - 1) \ S)
    (s₂ := actualCarlsonDyadicZeroStrip sigma tau k \ S)
    (f := fun rho : ℂ =>
      (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2)
  unfold actualCarlsonAdjacentDyadicStripSquareReciprocalCapacityExcluding
    actualCarlsonAdjacentDyadicStripExcluding
    actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
  linarith

theorem zetaRightDyadicPositiveMassSquareExcluding_le_twoCarlsonCapacities
    {x sigma beta : ℝ} {k : ℕ} {S : Finset ℂ}
    (hx : 1 ≤ x) (hk : 1 ≤ k) (hsigma : sigma < beta) :
    zetaRightDyadicPositiveMassSquareExcluding x beta k S ≤
      (x ^ (1 - beta)) ^ 2 *
        (actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
            sigma 1 (k - 1) S +
          actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma 1 k S) := by
  calc
    zetaRightDyadicPositiveMassSquareExcluding x beta k S ≤
        (x ^ (1 - beta)) ^ 2 *
          actualCarlsonAdjacentDyadicStripSquareReciprocalCapacityExcluding
            sigma 1 k S :=
      zetaRightDyadicPositiveMassSquareExcluding_le_adjacentCapacity
        hx hk hsigma
    _ ≤ (x ^ (1 - beta)) ^ 2 *
        (actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
            sigma 1 (k - 1) S +
          actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma 1 k S) :=
      mul_le_mul_of_nonneg_left
        (actualCarlsonAdjacentDyadicStripSquareReciprocalCapacityExcluding_le_add
          sigma 1 k S) (sq_nonneg _)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
