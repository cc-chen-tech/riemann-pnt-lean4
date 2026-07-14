import PrimeNumberTheorem.RHNaturalPsiError

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

example (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
        C * Real.sqrt (m : ℝ) * (1 + Real.log (m : ℝ)) ^ 2 :=
  exists_nat_abs_chebyshevPsi0_sub_id_le_sqrt_mul_one_add_log_sq_of_RH hRH

example (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
        C * Real.sqrt (m : ℝ) * (Real.log (m : ℝ)) ^ 2 :=
  exists_nat_abs_chebyshevPsi0_sub_id_le_sqrt_mul_log_sq_of_RH hRH

example (hRH : RiemannHypothesis.Statement) :
    RH_PsiErrorBound :=
  RH_PsiErrorBound_of_RiemannHypothesis hRH

example (hRH : RiemannHypothesis.Statement) :
    RH_ThetaErrorBound :=
  RH_ThetaErrorBound_of_RiemannHypothesis hRH

example (hRH : RiemannHypothesis.Statement) :
    RH_PrimeCountingLiErrorBound :=
  RH_PrimeCountingLiErrorBound_of_RiemannHypothesis hRH

example (hRH : RiemannHypothesis.Statement) :
    RH_ErrorBound :=
  RH_ErrorBound_of_RiemannHypothesis hRH

example :
    RiemannHypothesis.Statement ↔ RH_PsiErrorBound :=
  riemannHypothesis_iff_RH_PsiErrorBound

end ExplicitFormulaResidues
end PrimeNumberTheorem
