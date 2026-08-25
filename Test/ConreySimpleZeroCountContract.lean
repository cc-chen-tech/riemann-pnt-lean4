import HardyTheorem.ConreySimpleZeroCount

open Complex Filter Topology

namespace HardyTheorem

example {T : ℝ} {ρ : ℂ} :
    ρ ∈ positiveCriticalLineSimpleZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero ρ ∧
        0 < ρ.im ∧ ρ.im ≤ T ∧ ρ.re = 1 / 2 ∧
        analyticOrderNatAt riemannZeta ρ = 1 :=
  mem_positiveCriticalLineSimpleZerosFinset

example {U T : ℝ} (hUT : U ≤ T) :
    positiveCriticalLineSimpleZeroCount U ≤
      positiveCriticalLineSimpleZeroCount T :=
  positiveCriticalLineSimpleZeroCount_mono hUT

example (T : ℝ) :
    positiveCriticalLineSimpleZeroCount T ≤
      PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount T :=
  positiveCriticalLineSimpleZeroCount_le_riemannZeroCount T

example : Prop := conreyTwoFifthsSimpleZerosTarget

example (h : conreyTwoFifthsSimpleZerosTarget) :
    ∃ c : ℝ, 2 / 5 < c ∧
      ∀ᶠ T in atTop,
        c * (PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount T : ℝ) ≤
          (positiveCriticalLineSimpleZeroCount T : ℝ) :=
  h

#print axioms mem_positiveCriticalLineSimpleZerosFinset
#print axioms positiveCriticalLineSimpleZeroCount_mono
#print axioms positiveCriticalLineSimpleZeroCount_le_riemannZeroCount

end HardyTheorem
