import PrimeNumberTheorem.ZeroDensityLayerBudgetPositiveZeroBucket

/-!
# Positive zero buckets after removing a finite main cluster

The ordinary `PositiveZeroBucketInput` covers every positive-height zero up to
the truncation height.  That is appropriate for an upper bound, but not for a
zero-forced lower bound whose distinguished finite cluster must remain in the
main term.  This module repeats the bucket construction on the exact finite
difference `positiveNontrivialZerosFinset T \ S`.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

/-- Positive-height nontrivial zeros up to `T`, with the distinguished finite
cluster `S` removed. -/
noncomputable def positiveNontrivialZerosOutsideClusterFinset
    (T : ℝ) (S : Finset ℂ) : Finset ℂ :=
  positiveNontrivialZerosFinset T \ S

lemma mem_positiveNontrivialZerosOutsideClusterFinset
    {ρ : ℂ} {T : ℝ} {S : Finset ℂ} :
    ρ ∈ positiveNontrivialZerosOutsideClusterFinset T S ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧
        0 < ρ.im ∧ ρ.im ≤ T ∧ ρ ∉ S := by
  simp [positiveNontrivialZerosOutsideClusterFinset,
    mem_positiveNontrivialZerosFinset, and_assoc]

/-- A finite real-part classification of the positive-height zeros remaining
after deletion of the distinguished cluster. -/
structure PositiveZeroOutsideClusterBucketInput
    (T : ℝ) (S : Finset ℂ) (n : ℕ) : Type where
  bucket : ℂ → Fin n
  sigma : Fin n → ℝ
  sigma_lt_re :
    ∀ ρ ∈ positiveNontrivialZerosOutsideClusterFinset T S,
      sigma (bucket ρ) < ρ.re

/-- The outside-cluster zeros assigned to one real-part bucket. -/
noncomputable def PositiveZeroOutsideClusterBucketInput.layer
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) : Finset ℂ :=
  (positiveNontrivialZerosOutsideClusterFinset T S).filter fun ρ =>
    input.bucket ρ = i

/-- Outside-cluster bucket fibers form a disjoint exhaustive layer
certificate for the exact finite difference. -/
noncomputable def PositiveZeroOutsideClusterBucketInput.certificate
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n) :
    LayerCertificate ℂ ℂ where
  tail := positiveNontrivialZerosOutsideClusterFinset T S
  layerCount := n
  layer := input.layer
  pairwise_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro ρ hρi hρj
    have hi := (Finset.mem_filter.mp hρi).2
    have hj := (Finset.mem_filter.mp hρj).2
    exact hij (hi.symm.trans hj)
  sum_decomposition := by
    intro term
    simpa only [PositiveZeroOutsideClusterBucketInput.layer] using
      (Finset.sum_fiberwise
        (positiveNontrivialZerosOutsideClusterFinset T S)
        input.bucket term).symm

theorem
    PositiveZeroOutsideClusterBucketInput.layer_subset_zeroDensityZerosFinset
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) :
    input.layer i ⊆
      ZeroDensity.zeroDensityZerosFinset (input.sigma i) T := by
  intro ρ hρ
  have hρLayer := Finset.mem_filter.mp hρ
  have hρOutside :=
    mem_positiveNontrivialZerosOutsideClusterFinset.mp hρLayer.1
  apply ZeroDensity.mem_zeroDensityZerosFinset.mpr
  refine ⟨hρOutside.1, hρOutside.2.1, hρOutside.2.2.1, ?_⟩
  simpa [hρLayer.2] using input.sigma_lt_re ρ hρLayer.1

/-- Deleting the main cluster can only reduce each bucket, so the ordinary
Carlson multiplicity count remains a valid upper bound. -/
theorem PositiveZeroOutsideClusterBucketInput.layer_card_le_zeroDensityCount
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) :
    ((input.layer i).card : ℝ) ≤
      (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ) := by
  have hsubset :=
    Finset.card_le_card
      (input.layer_subset_zeroDensityZerosFinset i)
  have hdensity :
      (ZeroDensity.zeroDensityZerosFinset (input.sigma i) T).card ≤
        ZeroDensity.zeroDensityCount (input.sigma i) T := by
    rw [ZeroDensity.zeroDensityCount]
    calc
      (ZeroDensity.zeroDensityZerosFinset (input.sigma i) T).card =
          ∑ ρ ∈ ZeroDensity.zeroDensityZerosFinset
            (input.sigma i) T, 1 := by
              simp
      _ ≤ ∑ ρ ∈ ZeroDensity.zeroDensityZerosFinset
          (input.sigma i) T,
          analyticOrderNatAt riemannZeta ρ := by
            apply Finset.sum_le_sum
            intro ρ hρ
            have hzero :=
              (ZeroDensity.mem_zeroDensityZerosFinset.mp hρ).1
            have hne : ρ ≠ 1 := by
              intro heq
              have hre := hzero.2.2
              rw [heq] at hre
              norm_num at hre
            exact
              ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
                hne hzero.1
  exact_mod_cast hsubset.trans hdensity

/-- The exact positive outside-cluster tail inherits the same concrete
Pintz--Carlson density budget as an ordinary bucket family. -/
theorem
    PositiveZeroOutsideClusterBucketInput.norm_sum_le_pintzCarlsonDensityBudget
    {T x : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (term : ℂ → ℂ)
    (hkernel : ∀ i, ∀ ρ ∈ input.layer i,
      ‖term ρ‖ ≤ Real.exp (-Pintz.pintzZeroEnvelope x)) :
    ‖∑ ρ ∈ positiveNontrivialZerosOutsideClusterFinset T S, term ρ‖ ≤
      pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T :=
  norm_tail_sum_le_pintzCarlsonAggregatedDensityLayerTerm
    input.certificate input.sigma T x term
    input.layer_card_le_zeroDensityCount hkernel

end PrimeNumberTheorem
