import MathlibAux.DyadicDriftingGaussianSchur
import PrimeNumberTheorem.VKEdgeHighZeroGaussianEnergy

/-!
# Actual zeta adapter for the dyadic drifting Gaussian Schur bound

This file instantiates the abstract finite Gram/Schur theorem on genuine
nontrivial zeta zeros.  A finite index stores both a unit absolute-ordinate
bucket and the zero in that bucket.  The projection to zeros is injective, so
the quantitative cluster alternative counts distinct zeros rather than
duplicated labels.

The reference mass is taken at the right endpoint `x`.  Motion back from that
endpoint has drift `beta - rho.re`, which is nonpositive on the right strip.
Low zeros are kept in a separate finite set below the dyadic block.

No Carlson capacity estimate or two-height tail transfer is used here.
-/

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Bucket-labelled zeta zeros with absolute ordinate in the `k`th dyadic block. -/
noncomputable def zetaDyadicBucketPairs (k : ℕ) : Finset (ℕ × ℂ) :=
  (Finset.Ico (2 ^ k) (2 ^ (k + 1))).biUnion fun n =>
    (zeroOrdinateUnitBucket n).image fun rho => (n, rho)

@[simp]
theorem mem_zetaDyadicBucketPairs {k : ℕ} {p : ℕ × ℂ} :
    p ∈ zetaDyadicBucketPairs k ↔
      p.1 ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) ∧
        p.2 ∈ zeroOrdinateUnitBucket p.1 := by
  rcases p with ⟨n, rho⟩
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨j, hj, hpj⟩
    rcases Finset.mem_image.mp hpj with ⟨tau, htau, hpair⟩
    cases hpair
    exact ⟨hj, htau⟩
  · rintro ⟨hn, hrho⟩
    exact Finset.mem_biUnion.mpr
      ⟨n, hn, Finset.mem_image.mpr ⟨rho, hrho, rfl⟩⟩

/-- The part of a genuine dyadic zero block lying on or right of `beta`. -/
noncomputable def zetaRightDyadicBucketPairs (beta : ℝ) (k : ℕ) :
    Finset (ℕ × ℂ) :=
  (zetaDyadicBucketPairs k).filter fun p => beta ≤ p.2.re

@[simp]
theorem mem_zetaRightDyadicBucketPairs {beta : ℝ} {k : ℕ} {p : ℕ × ℂ} :
    p ∈ zetaRightDyadicBucketPairs beta k ↔
      p ∈ zetaDyadicBucketPairs k ∧ beta ≤ p.2.re := by
  simp [zetaRightDyadicBucketPairs]

/-- Forgetting the bucket label is injective on a genuine dyadic block. -/
theorem zetaDyadicBucketPairs_snd_inj (k : ℕ) :
    Set.InjOn Prod.snd (zetaDyadicBucketPairs k : Set (ℕ × ℂ)) := by
  intro p hp q hq hsnd
  have hpBucket := (mem_zetaDyadicBucketPairs.mp hp).2
  have hqBucket := (mem_zetaDyadicBucketPairs.mp hq).2
  have hpBounds := (Finset.mem_filter.mp hpBucket).2
  have hqBounds := (Finset.mem_filter.mp hqBucket).2
  have habs : |p.2.im| = |q.2.im| :=
    congrArg (fun z : ℂ => |z.im|) hsnd
  have hfst : p.1 = q.1 := by
    by_contra hne
    have hsep : p.1 + 1 ≤ q.1 ∨ q.1 + 1 ≤ p.1 := by omega
    rcases hsep with hpq | hqp
    · have hpqReal : (p.1 : ℝ) + 1 ≤ (q.1 : ℝ) := by exact_mod_cast hpq
      linarith
    · have hqpReal : (q.1 : ℝ) + 1 ≤ (p.1 : ℝ) := by exact_mod_cast hqp
      linarith
  exact Prod.ext hfst hsnd

/-- The genuine, unlabelled right-strip zeta zeros in one dyadic block. -/
noncomputable def zetaRightDyadicZeros (beta : ℝ) (k : ℕ) : Finset ℂ :=
  (zetaRightDyadicBucketPairs beta k).image Prod.snd

theorem mem_zetaRightDyadicZeros {beta : ℝ} {k : ℕ} {rho : ℂ} :
    rho ∈ zetaRightDyadicZeros beta k ↔
      ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        rho ∈ zeroOrdinateUnitBucket n ∧ beta ≤ rho.re := by
  constructor
  · intro hrho
    rcases Finset.mem_image.mp hrho with ⟨p, hp, hprho⟩
    have hp' := mem_zetaRightDyadicBucketPairs.mp hp
    refine ⟨p.1, (mem_zetaDyadicBucketPairs.mp hp'.1).1, ?_, ?_⟩
    · simpa [hprho] using (mem_zetaDyadicBucketPairs.mp hp'.1).2
    · simpa [hprho] using hp'.2
  · rintro ⟨n, hn, hrho, hright⟩
    apply Finset.mem_image.mpr
    refine ⟨(n, rho), ?_, rfl⟩
    exact mem_zetaRightDyadicBucketPairs.mpr
      ⟨mem_zetaDyadicBucketPairs.mpr ⟨hn, hrho⟩, hright⟩

/-- Every member is a genuine right-strip zero in the claimed dyadic height block. -/
theorem zetaRightDyadicZeros_spec {beta : ℝ} {k : ℕ} {rho : ℂ}
    (hrho : rho ∈ zetaRightDyadicZeros beta k) :
    RiemannHypothesis.IsNontrivialZero rho ∧
      ((2 ^ k : ℕ) : ℝ) ≤ |rho.im| ∧
      |rho.im| < ((2 ^ (k + 1) : ℕ) : ℝ) ∧
      beta ≤ rho.re := by
  rcases mem_zetaRightDyadicZeros.mp hrho with
    ⟨n, hn, hrhoBucket, hright⟩
  have hnBounds := Finset.mem_Ico.mp hn
  have hrhoFilter := Finset.mem_filter.mp hrhoBucket
  have hzero := (mem_nontrivialZerosFinset.mp hrhoFilter.1).1
  have hnUpper : n + 1 ≤ 2 ^ (k + 1) := by omega
  have hnLowerReal : ((2 ^ k : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnBounds.1
  have hnUpperReal : (n : ℝ) + 1 ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnUpper
  exact ⟨hzero, hnLowerReal.trans hrhoFilter.2.1,
    hrhoFilter.2.2.trans_le hnUpperReal, hright⟩

/-- A finite package containing all nontrivial zeros below a fixed cutoff. -/
noncomputable def zetaLowZeroFinset (cutoff : ℕ) : Finset ℂ :=
  nontrivialZerosFinset (cutoff : ℝ)

/-- A cutoff strictly below the dyadic block separates all low zeros from it. -/
theorem zetaLowZeroFinset_disjoint_zetaRightDyadicZeros
    {cutoff k : ℕ} {beta : ℝ} (hcutoff : cutoff < 2 ^ k) :
    Disjoint (zetaLowZeroFinset cutoff) (zetaRightDyadicZeros beta k) := by
  rw [Finset.disjoint_left]
  intro rho hrhoLow hrhoBlock
  have hlow := (mem_nontrivialZerosFinset.mp hrhoLow).2
  have hblock := (zetaRightDyadicZeros_spec hrhoBlock).2.1
  have hcutoffReal : (cutoff : ℝ) < ((2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast hcutoff
  linarith

/-- One actual unit-ordinate cluster inside the right dyadic zeta block. -/
noncomputable def zetaRightDyadicUnitCluster
    (beta : ℝ) (k n : ℕ) : Finset ℂ :=
  ((zetaRightDyadicBucketPairs beta k).filter fun p => p.1 = n).image Prod.snd

theorem card_zetaRightDyadicUnitCluster (beta : ℝ) (k n : ℕ) :
    (zetaRightDyadicUnitCluster beta k n).card =
      ((zetaRightDyadicBucketPairs beta k).filter fun p => p.1 = n).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq hsnd
  exact zetaDyadicBucketPairs_snd_inj k
    (mem_zetaRightDyadicBucketPairs.mp (Finset.mem_filter.mp hp).1).1
    (mem_zetaRightDyadicBucketPairs.mp (Finset.mem_filter.mp hq).1).1 hsnd

/-- Right-end reciprocal-multiplicity mass, with the analytic multiplicity retained. -/
noncomputable def zetaDyadicBaseMass (x beta : ℝ) (p : ℕ × ℂ) : ℝ :=
  zeroReciprocalMultiplicityCoefficient p.2 * x ^ (p.2.re - beta)

/-- Backward displacement from the right endpoint has nonpositive drift. -/
def zetaDyadicBackwardDrift (beta : ℝ) (p : ℕ × ℂ) : ℝ :=
  beta - p.2.re

/-- The actual finite drifting Gaussian Gram energy on one right dyadic block. -/
noncomputable def zetaRightDyadicGaussianGram
    (x beta : ℝ) (k : ℕ) (t m : ℝ) : ℝ :=
  MathlibAux.dyadicDriftingGaussianGram
    (zetaRightDyadicBucketPairs beta k)
    (zetaDyadicBaseMass x beta)
    (zetaDyadicBackwardDrift beta)
    (fun p => p.2.im) t m

private theorem zetaDyadicBaseMass_nonneg
    {x beta : ℝ} (hx : 0 < x) (p : ℕ × ℂ) :
    0 ≤ zetaDyadicBaseMass x beta p := by
  exact mul_nonneg
    (div_nonneg (Nat.cast_nonneg _) (norm_nonneg p.2))
    (Real.rpow_nonneg hx.le _)

private theorem zetaRightDyadic_frequency_gap
    {beta : ℝ} {k : ℕ} {p q : ℕ × ℂ}
    (hp : p ∈ zetaRightDyadicBucketPairs beta k)
    (hq : q ∈ zetaRightDyadicBucketPairs beta k) :
    (((p.1).dist q.1 - 1 : ℕ) : ℝ) ≤ |p.2.im - q.2.im| := by
  have hpBucket := (mem_zetaDyadicBucketPairs.mp
    (mem_zetaRightDyadicBucketPairs.mp hp).1).2
  have hqBucket := (mem_zetaDyadicBucketPairs.mp
    (mem_zetaRightDyadicBucketPairs.mp hq).1).2
  have hpBounds := (Finset.mem_filter.mp hpBucket).2
  have hqBounds := (Finset.mem_filter.mp hqBucket).2
  exact (MathlibAux.natDist_sub_one_le_abs_sub_of_mem_unit
    hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2).trans
      (abs_abs_sub_abs_le_abs_sub p.2.im q.2.im)

/--
Actual-zeta dyadic Gram/Schur bound under a quantitative unit-bucket occupancy
cap.  The right side is a sum of squares of the analytic-multiplicity masses.
-/
theorem zetaRightDyadicGaussianGram_le_occupancy_mul_sum_sq
    {x beta t m : ℝ} (k occupancy : ℕ)
    (hx : 0 < x) (ht : 0 ≤ t) (hm : 1 ≤ m)
    (hoccupancy : ∀ n ∈ (zetaRightDyadicBucketPairs beta k).image Prod.fst,
      ((zetaRightDyadicBucketPairs beta k).filter fun p => p.1 = n).card ≤
        occupancy + 1) :
    zetaRightDyadicGaussianGram x beta k t m ≤
      MathlibAux.gaussianBucketSchurConstant * ((occupancy + 1 : ℕ) : ℝ) *
        ∑ p ∈ zetaRightDyadicBucketPairs beta k,
          zetaDyadicBaseMass x beta p ^ 2 := by
  unfold zetaRightDyadicGaussianGram
  apply MathlibAux.dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq
    (bucket := Prod.fst) (occupancy := occupancy)
  · exact ht
  · exact hm
  · intro p _hp
    exact zetaDyadicBaseMass_nonneg hx p
  · intro p hp
    exact sub_nonpos.mpr (mem_zetaRightDyadicBucketPairs.mp hp).2
  · intro p hp q hq
    exact zetaRightDyadic_frequency_gap hp hq
  · exact hoccupancy

/--
Without an occupancy input, either the actual zeta Gram bound holds or one
unit bucket contains quantitatively many distinct genuine zeta zeros.
-/
theorem zetaRightDyadicGaussianGram_le_or_quantitativeCluster
    {x beta t m : ℝ} (k occupancy : ℕ)
    (hx : 0 < x) (ht : 0 ≤ t) (hm : 1 ≤ m) :
    zetaRightDyadicGaussianGram x beta k t m ≤
        MathlibAux.gaussianBucketSchurConstant * ((occupancy + 1 : ℕ) : ℝ) *
          ∑ p ∈ zetaRightDyadicBucketPairs beta k,
            zetaDyadicBaseMass x beta p ^ 2 ∨
      ∃ n ∈ (zetaRightDyadicBucketPairs beta k).image Prod.fst,
        occupancy + 1 < (zetaRightDyadicUnitCluster beta k n).card := by
  have hresult := MathlibAux.dyadicDriftingGaussianGram_le_or_quantitativeCluster
    (zetaRightDyadicBucketPairs beta k)
    (zetaDyadicBaseMass x beta)
    (zetaDyadicBackwardDrift beta)
    (fun p => p.2.im) Prod.fst occupancy ht hm
    (fun p _hp => zetaDyadicBaseMass_nonneg hx p)
    (fun p hp => sub_nonpos.mpr (mem_zetaRightDyadicBucketPairs.mp hp).2)
    (fun p hp q hq => zetaRightDyadic_frequency_gap hp hq)
  rcases hresult with henergy | ⟨n, hn, hcard⟩
  · exact Or.inl (by simpa [zetaRightDyadicGaussianGram] using henergy)
  · right
    refine ⟨n, hn, ?_⟩
    rwa [card_zetaRightDyadicUnitCluster]

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
