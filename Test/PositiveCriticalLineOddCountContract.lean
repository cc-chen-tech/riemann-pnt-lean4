import HardyTheorem.PositiveCriticalLineOddCount

namespace HardyTheorem

example (T : ℝ) : positiveCriticalLineOddZerosFinset T =
    (criticalLineOddZerosFinset T).filter fun ρ => 0 < ρ.im := rfl

example {T : ℝ} {ρ : ℂ} :
    ρ ∈ positiveCriticalLineOddZerosFinset T ↔
      ρ ∈ criticalLineOddZerosFinset T ∧ 0 < ρ.im :=
  mem_positiveCriticalLineOddZerosFinset

example (T : ℝ) : positiveCriticalLineOddZeroCount T =
    (positiveCriticalLineOddZerosFinset T).card := rfl

end HardyTheorem
