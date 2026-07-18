import PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem.RiemannVonMangoldt

example {rho : ℂ} {T : ℝ} :
    rho ∈ positiveNontrivialZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧ 0 < rho.im ∧ rho.im ≤ T :=
  mem_positiveNontrivialZerosFinset

example (T : ℝ) :
    riemannZeroCount T =
      ∑ rho ∈ positiveNontrivialZerosFinset T,
        analyticOrderNatAt riemannZeta rho :=
  rfl

example {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount U +
        ∑ rho ∈ positiveNontrivialZerosBetween U T,
          analyticOrderNatAt riemannZeta rho =
      riemannZeroCount T :=
  riemannZeroCount_add_between hUT

example {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount T - riemannZeroCount U =
      ∑ rho ∈ positiveNontrivialZerosBetween U T,
        analyticOrderNatAt riemannZeta rho :=
  riemannZeroCount_sub_eq_between hUT

end PrimeNumberTheorem.RiemannVonMangoldt
