import PrimeNumberTheorem.RHPrimeCountingConverse

namespace PrimeNumberTheorem

example (hπ : RH_PrimeCountingLiErrorBound) : RH_ThetaErrorBound :=
  RH_ThetaErrorBound_of_RH_PrimeCountingLiErrorBound hπ

example (hπ : RH_PrimeCountingLiErrorBound) : RH_PsiErrorBound :=
  RH_PsiErrorBound_of_RH_PrimeCountingLiErrorBound hπ

example (hπ : RH_PrimeCountingLiErrorBound) : RiemannHypothesis.Statement :=
  riemannHypothesis_of_RH_PrimeCountingLiErrorBound hπ

example : rh_iff_optimal_error :=
  rh_iff_optimal_error_proved

end PrimeNumberTheorem
