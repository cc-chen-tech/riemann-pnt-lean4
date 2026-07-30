import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridUpper

/-!
# Joint finite optimization of Pintz rates and explicit-formula truncations

At a natural point `m`, a candidate `(k, N)` determines the good-height base

`A(m,k) = pintzCarlsonHeight k m - 1`

and the explicit-formula truncation index `N`.  This module minimizes the
complete hybrid relative PNT budget over a finite product grid.  Every
candidate retains its actual good height and zero-bucket input, so the
optimization does not replace analytic terms by an abstract proxy.

The result is exact only on the supplied finite grid.  No continuous or
asymptotic optimality claim is made.
-/

namespace PrimeNumberTheorem

/-- A finite nonempty product grid of positive Pintz rates and explicit-formula
truncation indices. -/
structure PintzPNTTruncationGrid where
  rates : Finset ℝ
  truncations : Finset ℕ
  rates_nonempty : rates.Nonempty
  truncations_nonempty : truncations.Nonempty
  rates_pos : ∀ k ∈ rates, 0 < k

/-- Candidate pairs `(k,N)` in the joint optimization grid. -/
noncomputable def PintzPNTTruncationGrid.candidates
    (grid : PintzPNTTruncationGrid) : Finset (ℝ × ℕ) :=
  grid.rates.product grid.truncations

theorem PintzPNTTruncationGrid.candidates_nonempty
    (grid : PintzPNTTruncationGrid) :
    grid.candidates.Nonempty := by
  rcases grid.rates_nonempty with ⟨k, hk⟩
  rcases grid.truncations_nonempty with ⟨N, hN⟩
  exact ⟨(k, N), Finset.mem_product.mpr ⟨hk, hN⟩⟩

theorem PintzPNTTruncationGrid.rate_mem
    (grid : PintzPNTTruncationGrid) {candidate : ℝ × ℕ}
    (hcandidate : candidate ∈ grid.candidates) :
    candidate.1 ∈ grid.rates :=
  (Finset.mem_product.mp hcandidate).1

theorem PintzPNTTruncationGrid.truncation_mem
    (grid : PintzPNTTruncationGrid) {candidate : ℝ × ℕ}
    (hcandidate : candidate ∈ grid.candidates) :
    candidate.2 ∈ grid.truncations :=
  (Finset.mem_product.mp hcandidate).2

theorem PintzPNTTruncationGrid.candidate_rate_pos
    (grid : PintzPNTTruncationGrid) {candidate : ℝ × ℕ}
    (hcandidate : candidate ∈ grid.candidates) :
    0 < candidate.1 :=
  grid.rates_pos candidate.1 (grid.rate_mem hcandidate)

/-- The dynamic base `A(m,k)` associated with a rate/truncation candidate. -/
noncomputable def pintzPNTCandidateHeightBase
    (m : ℕ) (candidate : ℝ × ℕ) : ℝ :=
  pintzCarlsonGoodHeightBase candidate.1 (m : ℝ)

/-- Data certifying the complete hybrid relative PNT upper bound at every
candidate `(k,N)`. -/
structure NaturalPointPintzPNTHybridCandidateFamily
    (C : ℝ) (m : ℕ) (grid : PintzPNTTruncationGrid) (n : ℕ) where
  height : ℝ × ℕ → ℝ
  height_mem_interval :
    ∀ candidate ∈ grid.candidates,
      height candidate ∈ Set.Icc
        (pintzPNTCandidateHeightBase m candidate)
        (pintzPNTCandidateHeightBase m candidate + 1)
  heightBase_large :
    ∀ candidate ∈ grid.candidates,
      8 ≤ pintzPNTCandidateHeightBase m candidate
  goodHeight :
    ∀ candidate ∈ grid.candidates,
      ExplicitFormulaAux.goodHeight (height candidate)
  bucketInput :
    ∀ candidate, PositiveZeroBucketInput (height candidate) n
  relative_upper :
    ∀ candidate ∈ grid.candidates,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
          (pintzPNTCandidateHeightBase m candidate)
          (height candidate) candidate.1 m candidate.2
          (bucketInput candidate)

/-- Complete relative PNT cost attached to a certified candidate. -/
noncomputable def NaturalPointPintzPNTHybridCandidateFamily.relativeBudget
    {C : ℝ} {m : ℕ} {grid : PintzPNTTruncationGrid} {n : ℕ}
    (family : NaturalPointPintzPNTHybridCandidateFamily C m grid n)
    (candidate : ℝ × ℕ) : ℝ :=
  naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
    (pintzPNTCandidateHeightBase m candidate)
    (family.height candidate) candidate.1 m candidate.2
    (family.bucketInput candidate)

/-- A candidate minimizes a cost over the finite rate/truncation grid. -/
structure IsPintzPNTTruncationOptimizer
    (cost : (ℝ × ℕ) → ℝ) (grid : PintzPNTTruncationGrid)
    (candidate : ℝ × ℕ) : Prop where
  mem : candidate ∈ grid.candidates
  minimal :
    ∀ other ∈ grid.candidates, cost candidate ≤ cost other

theorem exists_pintzPNTTruncationOptimizer
    (cost : (ℝ × ℕ) → ℝ) (grid : PintzPNTTruncationGrid) :
    ∃ candidate, IsPintzPNTTruncationOptimizer cost grid candidate := by
  classical
  obtain ⟨candidate, hcandidate, hminimal⟩ :=
    Finset.exists_min_image grid.candidates cost grid.candidates_nonempty
  exact ⟨candidate, hcandidate, hminimal⟩

/-- Canonically selected joint rate/truncation optimizer. -/
noncomputable def pintzPNTOptimalTruncationCandidate
    (cost : (ℝ × ℕ) → ℝ) (grid : PintzPNTTruncationGrid) : ℝ × ℕ :=
  Classical.choose (exists_pintzPNTTruncationOptimizer cost grid)

theorem pintzPNTOptimalTruncationCandidate_spec
    (cost : (ℝ × ℕ) → ℝ) (grid : PintzPNTTruncationGrid) :
    IsPintzPNTTruncationOptimizer cost grid
      (pintzPNTOptimalTruncationCandidate cost grid) :=
  Classical.choose_spec (exists_pintzPNTTruncationOptimizer cost grid)

theorem pintzPNTOptimalTruncationCandidate_mem
    (cost : (ℝ × ℕ) → ℝ) (grid : PintzPNTTruncationGrid) :
    pintzPNTOptimalTruncationCandidate cost grid ∈ grid.candidates :=
  (pintzPNTOptimalTruncationCandidate_spec cost grid).mem

theorem pintzPNTOptimalTruncationCandidate_le_of_mem
    (cost : (ℝ × ℕ) → ℝ) (grid : PintzPNTTruncationGrid)
    {candidate : ℝ × ℕ} (hcandidate : candidate ∈ grid.candidates) :
    cost (pintzPNTOptimalTruncationCandidate cost grid) ≤ cost candidate :=
  (pintzPNTOptimalTruncationCandidate_spec cost grid).minimal
    candidate hcandidate

/-- The complete hybrid PNT budget is attained at a finite-grid minimizer and
is no larger than the budget of any other certified `(k,N)` candidate. -/
theorem exists_naturalPoint_pintzPNT_hybrid_truncation_optimal
    {C : ℝ} {m n : ℕ} {grid : PintzPNTTruncationGrid}
    (family : NaturalPointPintzPNTHybridCandidateFamily C m grid n) :
    ∃ candidate ∈ grid.candidates,
      family.height candidate ∈ Set.Icc
        (pintzPNTCandidateHeightBase m candidate)
        (pintzPNTCandidateHeightBase m candidate + 1) ∧
      ExplicitFormulaAux.goodHeight (family.height candidate) ∧
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        family.relativeBudget candidate ∧
      ∀ other ∈ grid.candidates,
        family.relativeBudget candidate ≤ family.relativeBudget other := by
  let cost : (ℝ × ℕ) → ℝ := family.relativeBudget
  let candidate := pintzPNTOptimalTruncationCandidate cost grid
  have hcandidate : candidate ∈ grid.candidates :=
    pintzPNTOptimalTruncationCandidate_mem cost grid
  refine ⟨candidate, hcandidate,
    family.height_mem_interval candidate hcandidate,
    family.goodHeight candidate hcandidate,
    family.relative_upper candidate hcandidate, ?_⟩
  intro other hother
  exact pintzPNTOptimalTruncationCandidate_le_of_mem cost grid hother

end PrimeNumberTheorem
