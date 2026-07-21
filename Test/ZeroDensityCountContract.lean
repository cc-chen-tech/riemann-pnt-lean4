import PrimeNumberTheorem.ZeroDensityCount

open Complex

namespace PrimeNumberTheorem
namespace ZeroDensity

example {rho : ℂ} {sigma T : ℝ} :
    rho ∈ zeroDensityZerosFinset sigma T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im ≤ T ∧ sigma < rho.re :=
  mem_zeroDensityZerosFinset

example (sigma T : ℝ) :
    zeroDensityCount sigma T =
      ∑ rho ∈ zeroDensityZerosFinset sigma T,
        analyticOrderNatAt riemannZeta rho :=
  rfl

example {sigma T U : ℝ} (hTU : T ≤ U) :
    zeroDensityCount sigma T ≤ zeroDensityCount sigma U :=
  zeroDensityCount_mono_height hTU

example {sigma tau T : ℝ} (hst : sigma ≤ tau) :
    zeroDensityCount tau T ≤ zeroDensityCount sigma T :=
  zeroDensityCount_antitone_re hst

example (sigma T : ℝ) :
    (zeroDensityCount sigma T : ℝ) ≤
      ExplicitFormulaAux.globalZeroMultiplicity T :=
  zeroDensityCount_le_globalZeroMultiplicity sigma T

example {sigma T : ℝ} (hT : T ≤ 0) :
    zeroDensityCount sigma T = 0 :=
  zeroDensityCount_eq_zero_of_nonpos_height hT

#print axioms zeroDensityCount_mono_height
#print axioms zeroDensityCount_antitone_re
#print axioms zeroDensityCount_le_globalZeroMultiplicity
#print axioms zeroDensityCount_eq_zero_of_nonpos_height

end ZeroDensity
end PrimeNumberTheorem
