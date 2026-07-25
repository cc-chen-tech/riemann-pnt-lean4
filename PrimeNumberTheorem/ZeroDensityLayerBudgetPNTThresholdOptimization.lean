import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTParametricTwoStrip
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTTruncationOptimization

namespace PrimeNumberTheorem

/-!
# Joint threshold, rate, and truncation optimization

The candidate type is `(threshold, (rate, truncation))`.  A finite grid
therefore optimizes the Carlson strip boundary, the Pintz-Carlson height rate,
and the explicit-formula truncation depth in one certified comparison.

This is finite-grid optimality for the displayed, machine-checked PNT budget.
It does not assert a globally sharp Johnston/Bellotti asymptotic constant.
-/

/-- A joint candidate `(strip threshold, (height rate, truncation depth))`. -/
abbrev PintzPNTThresholdCandidate := ℝ × (ℝ × ℕ)

/-- A finite nonempty grid whose strip thresholds lie in `(1 / 2, 1)` and
whose height rates are positive. -/
structure PintzPNTThresholdGrid where
  thresholds : Finset ℝ
  rates : Finset ℝ
  truncations : Finset ℕ
  thresholds_nonempty : thresholds.Nonempty
  rates_nonempty : rates.Nonempty
  truncations_nonempty : truncations.Nonempty
  thresholds_gt_half : ∀ threshold ∈ thresholds, 1 / 2 < threshold
  thresholds_lt_one : ∀ threshold ∈ thresholds, threshold < 1
  rates_pos : ∀ rate ∈ rates, 0 < rate

/-- Cartesian product of all certified threshold/rate/truncation choices. -/
noncomputable def PintzPNTThresholdGrid.candidates
    (grid : PintzPNTThresholdGrid) :
    Finset PintzPNTThresholdCandidate :=
  grid.thresholds.product (grid.rates.product grid.truncations)

theorem PintzPNTThresholdGrid.candidates_nonempty
    (grid : PintzPNTThresholdGrid) :
    grid.candidates.Nonempty := by
  rcases grid.thresholds_nonempty with ⟨threshold, hthreshold⟩
  rcases grid.rates_nonempty with ⟨rate, hrate⟩
  rcases grid.truncations_nonempty with ⟨N, hN⟩
  exact
    ⟨(threshold, (rate, N)),
      Finset.mem_product.mpr
        ⟨hthreshold, Finset.mem_product.mpr ⟨hrate, hN⟩⟩⟩

theorem PintzPNTThresholdGrid.threshold_mem
    (grid : PintzPNTThresholdGrid) {candidate : PintzPNTThresholdCandidate}
    (hcandidate : candidate ∈ grid.candidates) :
    candidate.1 ∈ grid.thresholds :=
  (Finset.mem_product.mp hcandidate).1

theorem PintzPNTThresholdGrid.rate_mem
    (grid : PintzPNTThresholdGrid) {candidate : PintzPNTThresholdCandidate}
    (hcandidate : candidate ∈ grid.candidates) :
    candidate.2.1 ∈ grid.rates :=
  (Finset.mem_product.mp (Finset.mem_product.mp hcandidate).2).1

theorem PintzPNTThresholdGrid.truncation_mem
    (grid : PintzPNTThresholdGrid) {candidate : PintzPNTThresholdCandidate}
    (hcandidate : candidate ∈ grid.candidates) :
    candidate.2.2 ∈ grid.truncations :=
  (Finset.mem_product.mp (Finset.mem_product.mp hcandidate).2).2

theorem PintzPNTThresholdGrid.candidate_threshold_gt_half
    (grid : PintzPNTThresholdGrid) {candidate : PintzPNTThresholdCandidate}
    (hcandidate : candidate ∈ grid.candidates) :
    1 / 2 < candidate.1 :=
  grid.thresholds_gt_half candidate.1 (grid.threshold_mem hcandidate)

theorem PintzPNTThresholdGrid.candidate_threshold_lt_one
    (grid : PintzPNTThresholdGrid) {candidate : PintzPNTThresholdCandidate}
    (hcandidate : candidate ∈ grid.candidates) :
    candidate.1 < 1 :=
  grid.thresholds_lt_one candidate.1 (grid.threshold_mem hcandidate)

theorem PintzPNTThresholdGrid.candidate_rate_pos
    (grid : PintzPNTThresholdGrid) {candidate : PintzPNTThresholdCandidate}
    (hcandidate : candidate ∈ grid.candidates) :
    0 < candidate.2.1 :=
  grid.rates_pos candidate.2.1 (grid.rate_mem hcandidate)

/-- Dynamic good-height base for a joint candidate. -/
noncomputable def pintzPNTThresholdCandidateHeightBase
    (m : ℕ) (candidate : PintzPNTThresholdCandidate) : ℝ :=
  pintzPNTCandidateHeightBase m candidate.2

/-- Complete explicit-formula data for every candidate in a joint finite grid.
The upper field is the actual relative `ψ₀` error bound, not merely an
abstract cost comparison. -/
structure NaturalPointPintzPNTThresholdCandidateFamily
    (C : ℝ) (m : ℕ) (grid : PintzPNTThresholdGrid) where
  height : PintzPNTThresholdCandidate → ℝ
  height_mem_interval :
    ∀ candidate ∈ grid.candidates,
      height candidate ∈ Set.Icc
        (pintzPNTThresholdCandidateHeightBase m candidate)
        (pintzPNTThresholdCandidateHeightBase m candidate + 1)
  heightBase_large :
    ∀ candidate ∈ grid.candidates,
      8 ≤ pintzPNTThresholdCandidateHeightBase m candidate
  goodHeight :
    ∀ candidate ∈ grid.candidates,
      ExplicitFormulaAux.goodHeight (height candidate)
  relative_upper :
    ∀ candidate ∈ grid.candidates,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
          (pintzPNTThresholdCandidateHeightBase m candidate)
          (height candidate) candidate.2.1 m candidate.2.2
          (pntParametricTwoStripBucketInput
            candidate.1 (height candidate))

/-- The complete certified relative PNT budget of a joint candidate. -/
noncomputable def
    NaturalPointPintzPNTThresholdCandidateFamily.relativeBudget
    {C : ℝ} {m : ℕ} {grid : PintzPNTThresholdGrid}
    (family : NaturalPointPintzPNTThresholdCandidateFamily C m grid)
    (candidate : PintzPNTThresholdCandidate) : ℝ :=
  naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
    (pintzPNTThresholdCandidateHeightBase m candidate)
    (family.height candidate) candidate.2.1 m candidate.2.2
    (pntParametricTwoStripBucketInput candidate.1 (family.height candidate))

/-- A candidate minimizes a cost over the finite joint grid. -/
structure IsPintzPNTThresholdOptimizer
    (cost : PintzPNTThresholdCandidate → ℝ)
    (grid : PintzPNTThresholdGrid)
    (candidate : PintzPNTThresholdCandidate) : Prop where
  mem : candidate ∈ grid.candidates
  minimal :
    ∀ other ∈ grid.candidates, cost candidate ≤ cost other

theorem exists_pintzPNTThresholdOptimizer
    (cost : PintzPNTThresholdCandidate → ℝ)
    (grid : PintzPNTThresholdGrid) :
    ∃ candidate, IsPintzPNTThresholdOptimizer cost grid candidate := by
  classical
  obtain ⟨candidate, hcandidate, hminimal⟩ :=
    Finset.exists_min_image grid.candidates cost grid.candidates_nonempty
  exact ⟨candidate, hcandidate, hminimal⟩

/-- Canonical jointly optimal threshold/rate/truncation candidate. -/
noncomputable def pintzPNTOptimalThresholdCandidate
    (cost : PintzPNTThresholdCandidate → ℝ)
    (grid : PintzPNTThresholdGrid) :
    PintzPNTThresholdCandidate :=
  Classical.choose (exists_pintzPNTThresholdOptimizer cost grid)

theorem pintzPNTOptimalThresholdCandidate_spec
    (cost : PintzPNTThresholdCandidate → ℝ)
    (grid : PintzPNTThresholdGrid) :
    IsPintzPNTThresholdOptimizer cost grid
      (pintzPNTOptimalThresholdCandidate cost grid) :=
  Classical.choose_spec (exists_pintzPNTThresholdOptimizer cost grid)

theorem pintzPNTOptimalThresholdCandidate_le_of_mem
    (cost : PintzPNTThresholdCandidate → ℝ)
    (grid : PintzPNTThresholdGrid)
    {candidate : PintzPNTThresholdCandidate}
    (hcandidate : candidate ∈ grid.candidates) :
    cost (pintzPNTOptimalThresholdCandidate cost grid) ≤ cost candidate :=
  (pintzPNTOptimalThresholdCandidate_spec cost grid).minimal
    candidate hcandidate

/-- The actual hybrid PNT budget is attained at a finite-grid minimizer jointly
over the strip threshold, height rate, and truncation depth. -/
theorem exists_naturalPoint_pintzPNT_hybrid_threshold_optimal
    {C : ℝ} {m : ℕ} {grid : PintzPNTThresholdGrid}
    (family : NaturalPointPintzPNTThresholdCandidateFamily C m grid) :
    ∃ candidate ∈ grid.candidates,
      1 / 2 < candidate.1 ∧
      candidate.1 < 1 ∧
      0 < candidate.2.1 ∧
      family.height candidate ∈ Set.Icc
        (pintzPNTThresholdCandidateHeightBase m candidate)
        (pintzPNTThresholdCandidateHeightBase m candidate + 1) ∧
      ExplicitFormulaAux.goodHeight (family.height candidate) ∧
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        family.relativeBudget candidate ∧
      ∀ other ∈ grid.candidates,
        family.relativeBudget candidate ≤ family.relativeBudget other := by
  let cost : PintzPNTThresholdCandidate → ℝ := family.relativeBudget
  let candidate := pintzPNTOptimalThresholdCandidate cost grid
  have hcandidate : candidate ∈ grid.candidates :=
    (pintzPNTOptimalThresholdCandidate_spec cost grid).mem
  refine
    ⟨candidate, hcandidate,
      grid.candidate_threshold_gt_half hcandidate,
      grid.candidate_threshold_lt_one hcandidate,
      grid.candidate_rate_pos hcandidate,
      family.height_mem_interval candidate hcandidate,
      family.goodHeight candidate hcandidate, ?_, ?_⟩
  · exact family.relative_upper candidate hcandidate
  · intro other hother
    exact
      (pintzPNTOptimalThresholdCandidate_spec cost grid).minimal other hother

end PrimeNumberTheorem
