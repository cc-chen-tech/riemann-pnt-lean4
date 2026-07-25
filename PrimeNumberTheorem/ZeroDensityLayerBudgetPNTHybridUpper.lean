import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridDensity

/-!
# Hybrid Pintz--Carlson upper bounds for the PNT error

This module inserts the low/global and high/Carlson density split into the
natural-point explicit-formula certificate.  It keeps the selected good
contour height, real-ordinate residual, trivial-zero contribution, and contour
remainder visible.
-/

namespace PrimeNumberTheorem

/-- Absolute PNT budget with global counting on low-threshold layers and
actual Carlson counting on high-threshold layers, both evaluated at the exact
Pintz--Carlson ceiling. -/
noncomputable def naturalPointPintzPNTHybridCeilingUpperBudget
    (C A T rate : ℝ) (m N : ℕ) {n : ℕ}
    (input : PositiveZeroBucketInput T n) : ℝ :=
  (m : ℝ) *
        (2 * pintzCarlsonHybridDensityBudget input.sigma (m : ℝ)
              (pintzCarlsonHeight rate (m : ℝ)) +
          ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
              pntRelativeZeroContribution (m : ℝ) rho‖) +
      ‖deriv riemannZeta 0 / riemannZeta 0‖ +
    ‖cofinalTrivialZeroContribution m N‖ +
    cofinalPNTFormulaRemainderBound C A T m N

/-- Relative version of `naturalPointPintzPNTHybridCeilingUpperBudget`. -/
noncomputable def naturalPointPintzPNTHybridCeilingRelativeUpperBudget
    (C A T rate : ℝ) (m N : ℕ) {n : ℕ}
    (input : PositiveZeroBucketInput T n) : ℝ :=
  2 * pintzCarlsonHybridDensityBudget input.sigma (m : ℝ)
        (pintzCarlsonHeight rate (m : ℝ)) +
    ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
        pntRelativeZeroContribution (m : ℝ) rho‖ +
    (‖deriv riemannZeta 0 / riemannZeta 0‖ +
        ‖cofinalTrivialZeroContribution m N‖ +
        cofinalPNTFormulaRemainderBound C A T m N) / (m : ℝ)

theorem naturalPointPintzPNTCeilingDensityUpperBudget_le_hybrid
    {C A T rate : ℝ} {m N n : ℕ}
    (input : PositiveZeroBucketInput T n) :
    naturalPointPintzPNTCeilingDensityUpperBudget C A T rate m N input ≤
      naturalPointPintzPNTHybridCeilingUpperBudget
        C A T rate m N input := by
  have hdensity :=
    pintzCarlsonClassicalAggregatedDensityLayerTerm_le_hybrid
      input.sigma (m : ℝ) (pintzCarlsonHeight rate (m : ℝ))
  simp only [naturalPointPintzPNTCeilingDensityUpperBudget,
    naturalPointPintzPNTHybridCeilingUpperBudget]
  gcongr

theorem naturalPointPintzPNTCeilingDensityRelativeUpperBudget_le_hybrid
    {C A T rate : ℝ} {m N n : ℕ}
    (input : PositiveZeroBucketInput T n) :
    naturalPointPintzPNTCeilingDensityRelativeUpperBudget C A T rate m N input ≤
      naturalPointPintzPNTHybridCeilingRelativeUpperBudget
        C A T rate m N input := by
  have hdensity :=
    pintzCarlsonClassicalAggregatedDensityLayerTerm_le_hybrid
      input.sigma (m : ℝ) (pintzCarlsonHeight rate (m : ℝ))
  simp only [naturalPointPintzPNTCeilingDensityRelativeUpperBudget,
    naturalPointPintzPNTHybridCeilingRelativeUpperBudget]
  gcongr

/-- Fully covering dynamic PNT transfer.  The selected contour height is a
genuine good height below the exact Pintz--Carlson ceiling, low-threshold
layers use global zero counting, and high-threshold layers use their actual
Carlson density counts. -/
theorem exists_naturalPoint_pintzCarlson_goodHeight_hybrid_PNT_upper
    (selectRate : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m N : ℕ), 3 ≤ m →
        8 ≤ pintzCarlsonGoodHeightBase
          (selectRate (m : ℝ)) (m : ℝ) →
        ∃ T ∈ Set.Icc
            (pintzCarlsonGoodHeightBase
              (selectRate (m : ℝ)) (m : ℝ))
            (pintzCarlsonGoodHeightBase
              (selectRate (m : ℝ)) (m : ℝ) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ∃ certificate : TruncatedPNTErrorCertificate (m : ℝ) T,
              certificate.trivialContribution =
                  cofinalTrivialZeroContribution m N ∧
                certificate.remainderBound =
                  cofinalPNTFormulaRemainderBound C
                    (pintzCarlsonGoodHeightBase
                      (selectRate (m : ℝ)) (m : ℝ)) T m N ∧
                ∀ {n : ℕ} (input : PositiveZeroBucketInput T n),
                  |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
                      naturalPointPintzPNTHybridCeilingUpperBudget C
                        (pintzCarlsonGoodHeightBase
                          (selectRate (m : ℝ)) (m : ℝ))
                        T (selectRate (m : ℝ)) m N input ∧
                    |relativeChebyshevPsi0Error (m : ℝ)| ≤
                      naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
                        (pintzCarlsonGoodHeightBase
                          (selectRate (m : ℝ)) (m : ℝ))
                        T (selectRate (m : ℝ)) m N input := by
  rcases exists_naturalPoint_pintzCarlson_goodHeight_ceiling_PNT_upper
      selectRate with ⟨C, hC, htransfer⟩
  refine ⟨C, hC, ?_⟩
  intro m N hm hbase
  rcases htransfer m N hm hbase with
    ⟨T, hT, hgood, certificate, htrivial, hremainder, hbounds⟩
  refine ⟨T, hT, hgood, certificate, htrivial, hremainder, ?_⟩
  intro n input
  rcases hbounds input with ⟨habsolute, hrelative⟩
  exact
    ⟨habsolute.trans
        (naturalPointPintzPNTCeilingDensityUpperBudget_le_hybrid input),
      hrelative.trans
        (naturalPointPintzPNTCeilingDensityRelativeUpperBudget_le_hybrid
          input)⟩

end PrimeNumberTheorem
