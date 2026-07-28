import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteHighSum
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualLowLayer

/-!
# Truncated explicit-formula zero split

This file splits the actual positive nontrivial zeros outside a finite cluster
at a fixed real-part boundary `sigma`.  The low part is kept as the norm of
its finite complex sum, while only the high part is enlarged to the complete
Carlson norm tail.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

/-- The actual truncated positive zeros outside `S` and strictly to the right
of `sigma`. -/
def actualHighPositiveZerosOutsideClusterFinset
    (sigma T : ℝ) (S : Finset ℂ) : Finset ℂ :=
  (positiveNontrivialZerosOutsideClusterFinset T S).filter
    (fun rho => sigma < rho.re)

theorem mem_actualHighPositiveZerosOutsideClusterFinset
    {sigma T : ℝ} {S : Finset ℂ} {rho : ℂ} :
    rho ∈ actualHighPositiveZerosOutsideClusterFinset sigma T S ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im ≤ T ∧ rho ∉ S ∧ sigma < rho.re := by
  simp [actualHighPositiveZerosOutsideClusterFinset,
    mem_positiveNontrivialZerosOutsideClusterFinset, and_assoc]

/-- Embed an attached truncated high zero into the untruncated actual
high-strip zero type. -/
def actualHighPositiveZeroSubtypeEmbedding
    (sigma T : ℝ) (S : Finset ℂ) :
    {rho : ℂ //
      rho ∈ actualHighPositiveZerosOutsideClusterFinset sigma T S} ↪
      ActualCarlsonHighPositiveZero sigma where
  toFun rho :=
    ⟨rho.1, by
      rcases mem_actualHighPositiveZerosOutsideClusterFinset.mp rho.property with
        ⟨hz, him, _, _, hre⟩
      exact ⟨hz, him, hre⟩⟩
  inj' := by
    intro rho₁ rho₂ heq
    apply Subtype.ext
    exact congrArg
      (fun rho : ActualCarlsonHighPositiveZero sigma => rho.1) heq

/-- The truncated high zeros as a finite family in the Carlson coverage
domain. -/
def actualHighPositiveZeroSubtypeFinset
    (sigma T : ℝ) (S : Finset ℂ) :
    Finset (ActualCarlsonHighPositiveZero sigma) :=
  (actualHighPositiveZerosOutsideClusterFinset sigma T S).attach.map
    (actualHighPositiveZeroSubtypeEmbedding sigma T S)

theorem sum_actualHighPositiveZeroSubtypeFinset
    {M : Type*} [AddCommMonoid M]
    (sigma T : ℝ) (S : Finset ℂ)
    (f : ℂ → M) :
    (∑ rho ∈ actualHighPositiveZeroSubtypeFinset sigma T S, f rho.1) =
      ∑ rho ∈ actualHighPositiveZerosOutsideClusterFinset sigma T S,
        f rho := by
  rw [actualHighPositiveZeroSubtypeFinset, Finset.sum_map]
  simpa [actualHighPositiveZeroSubtypeEmbedding] using
    (actualHighPositiveZerosOutsideClusterFinset sigma T S).sum_attach f

theorem actualHighPositiveZeroSubtypeFinset_outside
    {sigma T : ℝ} {S : Finset ℂ}
    {rho : ActualCarlsonHighPositiveZero sigma}
    (hrho : rho ∈ actualHighPositiveZeroSubtypeFinset sigma T S) :
    rho.1 ∉ S := by
  simp only [actualHighPositiveZeroSubtypeFinset, Finset.mem_map] at hrho
  rcases hrho with ⟨source, _, rfl⟩
  exact
    (mem_actualHighPositiveZerosOutsideClusterFinset.mp source.property).2.2.2.1

/-- The low bucket is exactly the weak-left half of the truncated positive
zeros when it has both the endpoint bound and the stated coverage property. -/
theorem lowLayer_eq_filter_re_le
    {T sigma : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n) (i : Fin n)
    (hreLow : ∀ rho ∈ input.layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        rho.re ≤ sigma → input.bucket rho = i) :
    input.layer i =
      (positiveNontrivialZerosOutsideClusterFinset T S).filter
        (fun rho => rho.re ≤ sigma) := by
  ext rho
  constructor
  · intro hrho
    have hbase :
        rho ∈ positiveNontrivialZerosOutsideClusterFinset T S :=
      (Finset.mem_filter.mp hrho).1
    exact Finset.mem_filter.mpr ⟨hbase, hreLow rho hrho⟩
  · intro hrho
    rcases Finset.mem_filter.mp hrho with ⟨hbase, hre⟩
    exact Finset.mem_filter.mpr ⟨hbase, hlowCover rho hbase hre⟩

/-- The actual truncated positive-zero sum is bounded by the low layer norm
plus the complete Carlson high-strip tail, all at target-amplitude scale. -/
theorem truncatedPositiveZeroKernelSum_div_target_le_low_add_CarlsonTail
    {T sigma beta : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n) (i : Fin n)
    (hreLow : ∀ rho ∈ input.layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        rho.re ≤ sigma → input.bucket rho = i)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index < beta)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        pntRelativeZeroContribution (m : ℝ) rho‖ /
          (m : ℝ) ^ (beta - 1) ≤
      ‖∑ rho ∈ input.layer i,
          pntRelativeZeroContribution (m : ℝ) rho‖ /
            (m : ℝ) ^ (beta - 1) +
        actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta S m := by
  let all := positiveNontrivialZerosOutsideClusterFinset T S
  let high := actualHighPositiveZerosOutsideClusterFinset sigma T S
  let contribution : ℂ → ℂ :=
    fun rho => pntRelativeZeroContribution (m : ℝ) rho
  have hlow :
      input.layer i = all.filter (fun rho => rho.re ≤ sigma) := by
    exact lowLayer_eq_filter_re_le input i hreLow hlowCover
  have hhigh :
      high = all.filter (fun rho => ¬rho.re ≤ sigma) := by
    ext rho
    simp only [high, all, actualHighPositiveZerosOutsideClusterFinset,
      Finset.mem_filter]
    constructor
    · rintro ⟨hbase, hlt⟩
      exact ⟨hbase, not_le.mpr hlt⟩
    · rintro ⟨hbase, hnle⟩
      exact ⟨hbase, lt_of_not_ge hnle⟩
  have hpartition :
      (∑ rho ∈ all, contribution rho) =
        (∑ rho ∈ input.layer i, contribution rho) +
          ∑ rho ∈ high, contribution rho := by
    rw [hlow, hhigh]
    exact
      (Finset.sum_filter_add_sum_filter_not
        all (fun rho => rho.re ≤ sigma) contribution).symm
  have hnorm :
      ‖∑ rho ∈ all, contribution rho‖ ≤
        ‖∑ rho ∈ input.layer i, contribution rho‖ +
          ∑ rho ∈ high, ‖contribution rho‖ := by
    rw [hpartition]
    exact (norm_add_le _ _).trans
      (add_le_add_right (norm_sum_le high contribution) _)
  have hamp : 0 < (m : ℝ) ^ (beta - 1) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hm)) _
  have hnormDiv :=
    (div_le_div_iff_of_pos_right hamp).mpr hnorm
  have houtside :
      ∀ rho ∈ actualHighPositiveZeroSubtypeFinset sigma T S,
        rho.1 ∉ S :=
    fun _ hrho => actualHighPositiveZeroSubtypeFinset_outside hrho
  have hfinite :=
    finite_actualHighPositiveZeroKernelSum_le_CarlsonTail
      S hhalf hone hreHigh
      (actualHighPositiveZeroSubtypeFinset sigma T S)
      houtside hm
  have hfinite' :
      (∑ rho ∈ high,
        ‖contribution rho‖ / (m : ℝ) ^ (beta - 1)) ≤
          actualCarlsonOutsideClusterNormalizedKernelTail
            (sigma := sigma) beta S m := by
    change
      (∑ rho ∈ actualHighPositiveZerosOutsideClusterFinset sigma T S,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖ /
          (m : ℝ) ^ (beta - 1)) ≤
        actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta S m
    rw [← sum_actualHighPositiveZeroSubtypeFinset sigma T S]
    exact hfinite
  rw [add_div] at hnormDiv
  have hsumDiv :
      (∑ rho ∈ high, ‖contribution rho‖) /
          (m : ℝ) ^ (beta - 1) =
        ∑ rho ∈ high,
          ‖contribution rho‖ / (m : ℝ) ^ (beta - 1) := by
    rw [Finset.sum_div]
  rw [hsumDiv] at hnormDiv
  exact hnormDiv.trans (add_le_add_right hfinite' _)

end

end PrimeNumberTheorem
