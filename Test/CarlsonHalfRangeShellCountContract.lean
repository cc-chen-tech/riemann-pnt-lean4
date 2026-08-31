import PrimeNumberTheorem.CarlsonHalfRangeShellCount

set_option autoImplicit false

open Complex Filter
open scoped BigOperators
open PrimeNumberTheorem.CarlsonZeroDensity

/-- Real zeta multiplicity, closed real threshold, and the whole closed
height shell.  There is no analytic estimate among the premises. -/
example : ∃ K > (0 : ℝ), ∀ᶠ U : ℝ in atTop,
    ∀ S : Finset ℂ,
      (∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho ∧
        (2 / 3 : ℝ) ≤ rho.re ∧ U ≤ rho.im ∧ rho.im ≤ 9 * U / 8) →
      (∑ rho ∈ S, (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
        K * U ^ (8 / 9 - 1 / 400 : ℝ) * (1 + Real.log U) ^ 6 :=
  exists_eventually_halfRange_shellFamilyCount_le

#print axioms exists_eventually_halfRange_shellFamilyCount_le
