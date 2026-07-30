import PrimeNumberTheorem.CofinalExplicitFormula
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTErrorBridge

/-!
# Good-height adapter for the PNT error certificate

This module packages the existing natural-point cofinal explicit formula as a
`TruncatedPNTErrorCertificate`.  It does not strengthen the contour theorem:
the evaluation point is still a natural number, and the height is still chosen
existentially in `[A, A + 1]`.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

/-- The finite trivial-zero contribution in the cofinal explicit formula. -/
noncomputable def cofinalTrivialZeroContribution (m N : ℕ) : ℂ :=
  ∑ p ∈ ExplicitFormulaAux.finiteTrivialZeroSum (2 * (N : ℝ)),
    -(((m : ℝ) : ℂ) ^ p) / p

/-- The explicit analytic remainder supplied by the natural-point cofinal
explicit formula. -/
noncomputable def cofinalPNTFormulaRemainderBound
    (C A T : ℝ) (m N : ℕ) : ℝ :=
  C * (m : ℝ) *
        ((1 + Real.log (m : ℝ)) ^ 2 + (1 + Real.log (A + 6)) ^ 2) / T +
    (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
              ‖Complex.log (Real.pi : ℂ)‖ +
            2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
              Real.log (2 * (N : ℝ) + T + 4)) +
          Real.pi) *
        (m : ℝ) ^ (-(2 * (N : ℝ) + 1)) *
        (2 * T) / (2 * Real.pi)

/-- The existing short-interval good-height theorem produces a
`TruncatedPNTErrorCertificate` at every natural evaluation point `m ≥ 3`.

The theorem deliberately retains the original quantifier order: the same
chosen height works for all `m`, `N` after `A` is fixed. -/
theorem exists_uniform_goodHeight_Icc_truncatedPNTErrorCertificate :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : ℝ, 8 ≤ A →
        ∃ T ∈ Set.Icc A (A + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ∀ (m N : ℕ), 3 ≤ m →
              ∃ certificate : TruncatedPNTErrorCertificate (m : ℝ) T,
                certificate.trivialContribution =
                    cofinalTrivialZeroContribution m N ∧
                  certificate.remainderBound =
                    cofinalPNTFormulaRemainderBound C A T m N := by
  rcases
      PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_nat_movingRight_truncatedExplicitFormula_sub_chebyshevPsi0_le
      with ⟨C, hC, hformula⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hformula A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro m N hm
  have hraw := hbound m N hm
  let certificate : TruncatedPNTErrorCertificate (m : ℝ) T :=
    { trivialContribution := cofinalTrivialZeroContribution m N
      remainderBound := cofinalPNTFormulaRemainderBound C A T m N
      remainder_nonneg := by
        simpa [cofinalPNTFormulaRemainderBound] using
          (le_trans (norm_nonneg _) hraw)
      formula_bound := by
        have hzero :
            (∑ rho ∈ nontrivialZerosFinset T,
                pntFiniteZeroContribution (m : ℝ) rho) =
              ∑ rho ∈ nontrivialZerosFinset T,
                -(analyticOrderNatAt riemannZeta rho : ℂ) *
                  (((m : ℝ) : ℂ) ^ rho) / rho := by
          apply Finset.sum_congr rfl
          intro rho _hrho
          simp only [pntFiniteZeroContribution, pntExplicitFormulaZeroTerm]
          ring
        rw [hzero]
        simpa only [cofinalTrivialZeroContribution, cofinalPNTFormulaRemainderBound]
          using hraw }
  exact ⟨certificate, rfl, rfl⟩

end PrimeNumberTheorem
