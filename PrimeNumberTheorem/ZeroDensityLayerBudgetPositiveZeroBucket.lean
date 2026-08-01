import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonExplicitFormulaBridge

/-!
# Positive-half-plane zero buckets

Carlson's density count in this project counts zeros with positive imaginary
part, with multiplicity. This module partitions that exact half of the finite
zero set into finitely many real-part buckets and proves the cardinality bound
needed by the concrete Pintz--Carlson tail transfer.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

/-- Distinct nontrivial zeros of positive imaginary part up to height `T`. -/
noncomputable def positiveNontrivialZerosFinset (T : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset T).filter fun ρ => 0 < ρ.im

lemma mem_positiveNontrivialZerosFinset {ρ : ℂ} {T : ℝ} :
    ρ ∈ positiveNontrivialZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  simp only [positiveNontrivialZerosFinset, Finset.mem_filter,
    mem_nontrivialZerosFinset]
  constructor
  · rintro ⟨⟨hzero, habs⟩, him⟩
    exact ⟨hzero, him, (le_abs_self ρ.im).trans habs⟩
  · rintro ⟨hzero, him, himT⟩
    exact ⟨⟨hzero, by simpa [abs_of_pos him] using himT⟩, him⟩

/-- A finite real-part classification of all positive-height zeros. The lower
threshold attached to a bucket is strict, matching `zeroDensityCount`. -/
structure PositiveZeroBucketInput (T : ℝ) (n : ℕ) : Type where
  bucket : ℂ → Fin n
  sigma : Fin n → ℝ
  sigma_lt_re : ∀ ρ ∈ positiveNontrivialZerosFinset T,
    sigma (bucket ρ) < ρ.re

/-- The zeros assigned to one bucket. -/
noncomputable def PositiveZeroBucketInput.layer
    {T : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (i : Fin n) : Finset ℂ :=
  (positiveNontrivialZerosFinset T).filter fun ρ => input.bucket ρ = i

/-- Bucket fibers form a disjoint exhaustive `LayerCertificate`. -/
noncomputable def PositiveZeroBucketInput.certificate
    {T : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n) :
    LayerCertificate ℂ ℂ where
  tail := positiveNontrivialZerosFinset T
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
    simpa only [PositiveZeroBucketInput.layer] using
      (Finset.sum_fiberwise
        (positiveNontrivialZerosFinset T) input.bucket term).symm

theorem PositiveZeroBucketInput.layer_subset_zeroDensityZerosFinset
    {T : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (i : Fin n) :
    input.layer i ⊆ ZeroDensity.zeroDensityZerosFinset (input.sigma i) T := by
  intro ρ hρ
  have hρ_layer := Finset.mem_filter.mp hρ
  have hρ_pos := (mem_positiveNontrivialZerosFinset.mp hρ_layer.1)
  apply ZeroDensity.mem_zeroDensityZerosFinset.mpr
  refine ⟨hρ_pos.1, hρ_pos.2.1, hρ_pos.2.2, ?_⟩
  simpa [hρ_layer.2] using input.sigma_lt_re ρ hρ_layer.1

/-- Distinct zeros in a bucket are bounded by Carlson's multiplicity count. -/
theorem PositiveZeroBucketInput.layer_card_le_zeroDensityCount
    {T : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (i : Fin n) :
    ((input.layer i).card : ℝ) ≤
      (ZeroDensity.zeroDensityCount (input.sigma i) T : ℝ) := by
  have hsubset :=
    Finset.card_le_card (input.layer_subset_zeroDensityZerosFinset i)
  have hdensity :
      (ZeroDensity.zeroDensityZerosFinset (input.sigma i) T).card ≤
        ZeroDensity.zeroDensityCount (input.sigma i) T := by
    rw [ZeroDensity.zeroDensityCount]
    calc
      (ZeroDensity.zeroDensityZerosFinset (input.sigma i) T).card =
          ∑ ρ ∈ ZeroDensity.zeroDensityZerosFinset (input.sigma i) T, 1 := by
            simp
      _ ≤ ∑ ρ ∈ ZeroDensity.zeroDensityZerosFinset (input.sigma i) T,
          analyticOrderNatAt riemannZeta ρ := by
            apply Finset.sum_le_sum
            intro ρ hρ
            have hzero := (ZeroDensity.mem_zeroDensityZerosFinset.mp hρ).1
            have hne : ρ ≠ 1 := by
              intro heq
              have hre := hzero.2.2
              rw [heq] at hre
              norm_num at hre
            exact ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
              hne hzero.1
  exact_mod_cast hsubset.trans hdensity

/-- The complete positive-half-plane finite zero tail inherits the concrete
Pintz--Carlson density budget. -/
theorem PositiveZeroBucketInput.norm_sum_le_pintzCarlsonDensityBudget
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (term : ℂ → ℂ)
    (hkernel : ∀ i, ∀ ρ ∈ input.layer i,
      ‖term ρ‖ ≤ Real.exp (-Pintz.pintzZeroEnvelope x)) :
    ‖∑ ρ ∈ positiveNontrivialZerosFinset T, term ρ‖ ≤
      pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T :=
  norm_tail_sum_le_pintzCarlsonAggregatedDensityLayerTerm
    input.certificate input.sigma T x term
    input.layer_card_le_zeroDensityCount hkernel

end PrimeNumberTheorem
