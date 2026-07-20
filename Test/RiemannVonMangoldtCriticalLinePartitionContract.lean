import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition

open Complex

namespace PrimeNumberTheorem.RiemannVonMangoldt

#check criticalLineReflection
#check isNontrivialZero_criticalLineReflection
#check analyticOrderNatAt_riemannZeta_conj_of_nontrivialZero
#check analyticOrderNatAt_riemannZeta_criticalLineReflection_of_nontrivialZero
#check positiveCriticalLineZeroMultiplicityCount
#check riemannZeroCount_eq_positiveCriticalLine_add_two_mul_zeroDensityCount
#check riemannZeroCount_add_halfMultiplicity_eq_criticalLine_add_two_mul_zeroDensityCount
#check riemannZeroCount_eq_criticalLine_add_two_mul_zeroDensityCount

example (rho : ℂ) :
    criticalLineReflection (criticalLineReflection rho) = rho :=
  criticalLineReflection_involutive rho

example {rho : ℂ} (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    RiemannHypothesis.IsNontrivialZero (criticalLineReflection rho) ∧
      analyticOrderNatAt riemannZeta (criticalLineReflection rho) =
        analyticOrderNatAt riemannZeta rho :=
  ⟨isNontrivialZero_criticalLineReflection hrho,
    analyticOrderNatAt_riemannZeta_criticalLineReflection_of_nontrivialZero hrho⟩

example (T : ℝ) :
    riemannZeroCount T =
      positiveCriticalLineZeroMultiplicityCount T +
        2 * ZeroDensity.zeroDensityCount (1 / 2) T :=
  riemannZeroCount_eq_positiveCriticalLine_add_two_mul_zeroDensityCount T

example {T : ℝ} (hT : 0 ≤ T) :
    riemannZeroCount T + analyticOrderNatAt riemannZeta (1 / 2) =
      HardyTheorem.criticalLineZeroMultiplicityCount T +
        2 * ZeroDensity.zeroDensityCount (1 / 2) T :=
  riemannZeroCount_add_halfMultiplicity_eq_criticalLine_add_two_mul_zeroDensityCount hT

example (T : ℝ) (hhalf : riemannZeta (1 / 2) ≠ 0) :
    riemannZeroCount T =
      HardyTheorem.criticalLineZeroMultiplicityCount T +
        2 * ZeroDensity.zeroDensityCount (1 / 2) T :=
  riemannZeroCount_eq_criticalLine_add_two_mul_zeroDensityCount T hhalf

end PrimeNumberTheorem.RiemannVonMangoldt
