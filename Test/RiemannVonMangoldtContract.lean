import PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount
import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta

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

example : Differentiable ℂ RiemannHypothesis.completedZeta :=
  differentiable_completedZeta

example {s : ℂ} (hsre : 0 < s.re) (hsre' : s.re < 1) :
    RiemannHypothesis.completedZeta s = 0 ↔ riemannZeta s = 0 :=
  completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
    hsre hsre'

example {s : ℂ} (hsre : 0 < s.re) (hsre' : s.re < 1) :
    analyticOrderNatAt RiemannHypothesis.completedZeta s =
      analyticOrderNatAt riemannZeta s :=
  analyticOrderNatAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
    hsre hsre'

example {s : ℂ} (hsre : s.re = 1) (hsim : s.im ≠ 0) :
    RiemannHypothesis.completedZeta s ≠ 0 :=
  completedZeta_ne_zero_of_re_eq_one_of_im_ne_zero hsre hsim

example {s : ℂ} (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    RiemannHypothesis.completedZeta s ≠ 0 :=
  completedZeta_ne_zero_of_re_eq_zero_of_im_ne_zero hsre hsim

end PrimeNumberTheorem.RiemannVonMangoldt
