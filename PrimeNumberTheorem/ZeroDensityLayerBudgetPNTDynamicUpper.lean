import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTGoodHeightAdapter

/-!
# Dynamic-height Pintz--Carlson upper transfer for PNT error

The base height may depend on the natural evaluation point.  The existing
cofinal explicit formula then chooses an actual good height in the unit
interval above that base.  Once a positive-zero bucket input is supplied at
the chosen height, the fixed-height transfer gives both absolute and relative
PNT error bounds.

No zero-density theorem is asserted here: `PositiveZeroBucketInput` remains the
explicit interface between a concrete density argument and this transfer.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

/-- The absolute PNT error budget obtained by combining the natural-point
cofinal remainder with the Pintz--Carlson zero-layer budget. -/
noncomputable def naturalPointPintzPNTUpperBudget
    (C A T : ℝ) (m N : ℕ) {n : ℕ}
    (input : PositiveZeroBucketInput T n) : ℝ :=
  (m : ℝ) *
        (2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
              Finset.univ input.sigma () (m : ℝ) T +
          ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
              pntRelativeZeroContribution (m : ℝ) rho‖) +
      ‖deriv riemannZeta 0 / riemannZeta 0‖ +
    ‖cofinalTrivialZeroContribution m N‖ +
    cofinalPNTFormulaRemainderBound C A T m N

/-- The relative PNT error budget corresponding to
`naturalPointPintzPNTUpperBudget`. -/
noncomputable def naturalPointPintzPNTRelativeUpperBudget
    (C A T : ℝ) (m N : ℕ) {n : ℕ}
    (input : PositiveZeroBucketInput T n) : ℝ :=
  2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
        Finset.univ input.sigma () (m : ℝ) T +
    ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
        pntRelativeZeroContribution (m : ℝ) rho‖ +
    (‖deriv riemannZeta 0 / riemannZeta 0‖ +
        ‖cofinalTrivialZeroContribution m N‖ +
        cofinalPNTFormulaRemainderBound C A T m N) / (m : ℝ)

/-- Dynamic natural-point PNT upper transfer.

For each `m`, the caller may choose a different base height `heightBase m`.
The theorem selects a good height `T ∈ [heightBase m, heightBase m + 1]` and an
explicit formula certificate.  Every positive-zero layering at that actual
height then yields the displayed absolute and relative PNT error bounds. -/
theorem exists_naturalPoint_dynamic_goodHeight_pintz_PNT_upper
    (heightBase : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m N : ℕ), 3 ≤ m → 8 ≤ heightBase m →
        ∃ T ∈ Set.Icc (heightBase m) (heightBase m + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ∃ certificate : TruncatedPNTErrorCertificate (m : ℝ) T,
              certificate.trivialContribution =
                  cofinalTrivialZeroContribution m N ∧
                certificate.remainderBound =
                  cofinalPNTFormulaRemainderBound C (heightBase m) T m N ∧
                ∀ {n : ℕ} (input : PositiveZeroBucketInput T n),
                  |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
                      naturalPointPintzPNTUpperBudget
                        C (heightBase m) T m N input ∧
                    |relativeChebyshevPsi0Error (m : ℝ)| ≤
                      naturalPointPintzPNTRelativeUpperBudget
                        C (heightBase m) T m N input := by
  rcases exists_uniform_goodHeight_Icc_truncatedPNTErrorCertificate with
    ⟨C, hC, hcertificate⟩
  refine ⟨C, hC, ?_⟩
  intro m N hm hbase
  rcases hcertificate (heightBase m) hbase with
    ⟨T, hT, hgood, hcertificates⟩
  rcases hcertificates m N hm with
    ⟨certificate, htrivial, hremainder⟩
  refine ⟨T, hT, hgood, certificate, htrivial, hremainder, ?_⟩
  intro n input
  have hmNat : 1 ≤ m := le_trans (by norm_num) hm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmNat
  have habsolute :=
    certificate.abs_chebyshevPsi0_sub_id_le_pintz input hmReal
  have hrelative :=
    certificate.abs_relativeChebyshevPsi0Error_le_pintz input hmReal
  rw [htrivial, hremainder] at habsolute hrelative
  exact
    ⟨by
      simpa only [naturalPointPintzPNTUpperBudget] using habsolute,
    by
      simpa only [naturalPointPintzPNTRelativeUpperBudget] using hrelative⟩

end PrimeNumberTheorem
