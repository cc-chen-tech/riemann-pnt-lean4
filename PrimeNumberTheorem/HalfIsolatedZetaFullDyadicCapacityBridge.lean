import PrimeNumberTheorem.HalfIsolatedZetaDyadicCapacityBridge
import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition

/-!
# Full dyadic zeta mass to Carlson capacity

This module first transfers the negative-ordinate half of the actual dyadic
zeta mass to the positive half by complex conjugation.  The exceptional set
is transformed exactly; no conjugation-invariance assumption is imposed.
-/

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

open Complex
open scoped BigOperators

noncomputable section

/-- Image of an exceptional zero set under complex conjugation. -/
def conjugateFinset (S : Finset ℂ) : Finset ℂ :=
  S.image (starRingEnd ℂ)

theorem mem_conjugateFinset_iff {S : Finset ℂ} {rho : ℂ} :
    rho ∈ conjugateFinset S ↔ (starRingEnd ℂ) rho ∈ S := by
  constructor
  · intro hrho
    rcases Finset.mem_image.mp hrho with ⟨z, hz, hzr⟩
    simpa [← hzr] using hz
  · intro hrho
    exact Finset.mem_image.mpr ⟨(starRingEnd ℂ) rho, hrho, by simp⟩

theorem not_mem_conjugateFinset_iff {S : Finset ℂ} {rho : ℂ} :
    rho ∉ conjugateFinset S ↔ (starRingEnd ℂ) rho ∉ S := by
  rw [not_congr mem_conjugateFinset_iff]

/-- Conjugation preserves an absolute-ordinate unit bucket. -/
theorem mem_zeroOrdinateUnitBucket_conj_iff {n : ℕ} {rho : ℂ} :
    (starRingEnd ℂ) rho ∈ zeroOrdinateUnitBucket n ↔
      rho ∈ zeroOrdinateUnitBucket n := by
  constructor
  · intro hrho
    rcases Finset.mem_filter.mp hrho with ⟨hfinite, hbounds⟩
    have hspec := mem_nontrivialZerosFinset.mp hfinite
    have hzero : RiemannHypothesis.IsNontrivialZero rho := by
      simpa using RiemannVonMangoldt.isNontrivialZero_conj hspec.1
    apply Finset.mem_filter.mpr
    refine ⟨mem_nontrivialZerosFinset.mpr ⟨hzero, ?_⟩, ?_⟩
    · simpa using hspec.2
    · simpa using hbounds
  · intro hrho
    rcases Finset.mem_filter.mp hrho with ⟨hfinite, hbounds⟩
    have hspec := mem_nontrivialZerosFinset.mp hfinite
    have hzero := RiemannVonMangoldt.isNontrivialZero_conj hspec.1
    apply Finset.mem_filter.mpr
    refine ⟨mem_nontrivialZerosFinset.mpr ⟨hzero, ?_⟩, ?_⟩
    · simpa using hspec.2
    · simpa using hbounds

/-- Conjugation of a bucket-labelled zero retains its bucket label. -/
def conjugateBucketPair (p : ℕ × ℂ) : ℕ × ℂ :=
  (p.1, (starRingEnd ℂ) p.2)

@[simp]
theorem conjugateBucketPair_involutive (p : ℕ × ℂ) :
    conjugateBucketPair (conjugateBucketPair p) = p := by
  cases p
  simp [conjugateBucketPair]

theorem conjugateBucketPair_injective : Function.Injective conjugateBucketPair := by
  intro p q hpq
  have h := congrArg conjugateBucketPair hpq
  simpa using h

theorem mem_zetaRightDyadicBucketPairs_conjugate_iff
    {beta : ℝ} {k : ℕ} {p : ℕ × ℂ} :
    conjugateBucketPair p ∈ zetaRightDyadicBucketPairs beta k ↔
      p ∈ zetaRightDyadicBucketPairs beta k := by
  rw [mem_zetaRightDyadicBucketPairs, mem_zetaRightDyadicBucketPairs,
    mem_zetaDyadicBucketPairs, mem_zetaDyadicBucketPairs]
  simp only [conjugateBucketPair, Prod.fst, Prod.snd, Complex.conj_re]
  constructor
  · rintro ⟨⟨hbucket, hzero⟩, hright⟩
    exact ⟨⟨hbucket, mem_zeroOrdinateUnitBucket_conj_iff.mp hzero⟩, hright⟩
  · rintro ⟨⟨hbucket, hzero⟩, hright⟩
    exact ⟨⟨hbucket, mem_zeroOrdinateUnitBucket_conj_iff.mpr hzero⟩, hright⟩

/-- Negative-ordinate right-strip bucket pairs after deleting `S`. -/
def zetaRightDyadicNegativePairsExcluding
    (beta : ℝ) (k : ℕ) (S : Finset ℂ) : Finset (ℕ × ℂ) :=
  (zetaRightDyadicBucketPairs beta k).filter fun p =>
    p.2.im < 0 ∧ p.2 ∉ S

theorem conjugateBucketPair_mem_positiveExcluding_iff
    {beta : ℝ} {k : ℕ} {S : Finset ℂ} {p : ℕ × ℂ} :
    conjugateBucketPair p ∈
        zetaRightDyadicPositivePairsExcluding beta k (conjugateFinset S) ↔
      p ∈ zetaRightDyadicNegativePairsExcluding beta k S := by
  rw [zetaRightDyadicPositivePairsExcluding,
    zetaRightDyadicNegativePairsExcluding, Finset.mem_filter, Finset.mem_filter,
    mem_zetaRightDyadicBucketPairs_conjugate_iff]
  simp only [conjugateBucketPair, Prod.snd, Complex.conj_im, neg_pos,
    not_mem_conjugateFinset_iff]
  simp

/-- Square mass of the negative-ordinate half of one excluded dyadic block. -/
def zetaRightDyadicNegativeMassSquareExcluding
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ p ∈ zetaRightDyadicNegativePairsExcluding beta k S,
    zetaDyadicBaseMass x beta p ^ 2

private theorem nontrivialZero_of_mem_negativePairsExcluding
    {beta : ℝ} {k : ℕ} {S : Finset ℂ} {p : ℕ × ℂ}
    (hp : p ∈ zetaRightDyadicNegativePairsExcluding beta k S) :
    RiemannHypothesis.IsNontrivialZero p.2 := by
  have hpRight := (Finset.mem_filter.mp hp).1
  have hpZero : p.2 ∈ zetaRightDyadicZeros beta k :=
    Finset.mem_image.mpr ⟨p, hpRight, rfl⟩
  exact (zetaRightDyadicZeros_spec hpZero).1

private theorem zetaDyadicBaseMass_conjugateBucketPair
    {x beta : ℝ} {p : ℕ × ℂ}
    (hzero : RiemannHypothesis.IsNontrivialZero p.2) :
    zetaDyadicBaseMass x beta (conjugateBucketPair p) =
      zetaDyadicBaseMass x beta p := by
  unfold zetaDyadicBaseMass zeroReciprocalMultiplicityCoefficient
    conjugateBucketPair
  rw [RiemannVonMangoldt.analyticOrderNatAt_riemannZeta_conj_of_nontrivialZero
    hzero, norm_conj]
  simp

theorem zetaRightDyadicNegativeMassSquareExcluding_eq_positive_conjugateFinset
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) :
    zetaRightDyadicNegativeMassSquareExcluding x beta k S =
      zetaRightDyadicPositiveMassSquareExcluding
        x beta k (conjugateFinset S) := by
  unfold zetaRightDyadicNegativeMassSquareExcluding
    zetaRightDyadicPositiveMassSquareExcluding
  apply Finset.sum_bij (fun p _ => conjugateBucketPair p)
  · intro p hp
    exact conjugateBucketPair_mem_positiveExcluding_iff.mpr hp
  · intro p hp q hq hpq
    exact conjugateBucketPair_injective hpq
  · intro q hq
    refine ⟨conjugateBucketPair q, ?_, ?_⟩
    · have hpos : conjugateBucketPair (conjugateBucketPair q) ∈
          zetaRightDyadicPositivePairsExcluding beta k (conjugateFinset S) := by
        simpa using hq
      exact conjugateBucketPair_mem_positiveExcluding_iff.mp hpos
    · exact conjugateBucketPair_involutive q
  · intro p hp
    rw [zetaDyadicBaseMass_conjugateBucketPair
      (nontrivialZero_of_mem_negativePairsExcluding hp)]

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
