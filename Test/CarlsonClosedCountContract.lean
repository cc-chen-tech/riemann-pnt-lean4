import PrimeNumberTheorem.CarlsonClosedCount

set_option autoImplicit false

open Complex Filter
open scoped BigOperators
open PrimeNumberTheorem PrimeNumberTheorem.ZeroDensity

example {rho : ℂ} {sigma T : ℝ} :
    rho ∈ zeroDensityClosedZerosFinset sigma T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧ 0 < rho.im ∧ rho.im ≤ T ∧ sigma ≤ rho.re :=
  mem_zeroDensityClosedZerosFinset

example {sigma U T : ℝ} (hUT : U ≤ T) :
    zeroDensityClosedCount sigma U ≤ zeroDensityClosedCount sigma T :=
  zeroDensityClosedCount_mono_height hUT

example (sigma T : ℝ) : zeroDensityCount sigma T ≤ zeroDensityClosedCount sigma T :=
  zeroDensityCount_le_closedCount sigma T

example (sigma T : ℝ) :
    (zeroDensityClosedCount sigma T : ℝ) ≤ ExplicitFormulaAux.globalZeroMultiplicity T :=
  zeroDensityClosedCount_le_globalZeroMultiplicity sigma T

example {sigma U T : ℝ} (hUT : U ≤ T) :
    zeroDensityClosedCount sigma T = zeroDensityClosedCount sigma U +
      ∑ rho ∈ (zeroDensityClosedZerosFinset sigma T).filter (fun rho => U < rho.im),
        analyticOrderNatAt riemannZeta rho :=
  zeroDensityClosedCount_step_eq hUT

example : ∃ K > (0 : ℝ), ∀ᶠ U : ℝ in atTop,
    (zeroDensityClosedCount (2 / 3) (9 * U / 8) : ℝ) ≤
      (zeroDensityClosedCount (2 / 3) U : ℝ) +
        K * U ^ (8 / 9 - 1 / 400 : ℝ) * (1 + Real.log U) ^ 6 :=
  exists_eventually_closedCount_twoThirds_step_le

#print axioms mem_zeroDensityClosedZerosFinset
#print axioms zeroDensityClosedCount_mono_height
#print axioms zeroDensityCount_le_closedCount
#print axioms zeroDensityClosedCount_le_globalZeroMultiplicity
#print axioms zeroDensityClosedCount_step_eq
#print axioms exists_eventually_closedCount_twoThirds_step_le
