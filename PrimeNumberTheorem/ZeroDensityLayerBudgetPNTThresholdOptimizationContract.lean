import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTThresholdOptimization

namespace PrimeNumberTheorem

/-! Public contract for joint threshold/rate/truncation optimization. -/

example (grid : PintzPNTThresholdGrid) :
    grid.candidates.Nonempty :=
  grid.candidates_nonempty

example
    (cost : PintzPNTThresholdCandidate → ℝ)
    (grid : PintzPNTThresholdGrid) :
    ∃ candidate, IsPintzPNTThresholdOptimizer cost grid candidate :=
  exists_pintzPNTThresholdOptimizer cost grid

example
    (cost : PintzPNTThresholdCandidate → ℝ)
    (grid : PintzPNTThresholdGrid)
    {candidate : PintzPNTThresholdCandidate}
    (hcandidate : candidate ∈ grid.candidates) :
    cost (pintzPNTOptimalThresholdCandidate cost grid) ≤ cost candidate :=
  pintzPNTOptimalThresholdCandidate_le_of_mem cost grid hcandidate

example
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
        family.relativeBudget candidate ≤ family.relativeBudget other :=
  exists_naturalPoint_pintzPNT_hybrid_threshold_optimal family

end PrimeNumberTheorem
