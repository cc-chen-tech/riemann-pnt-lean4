import HardyTheorem.CriticalLineMultiplicity

namespace HardyTheorem

/-- Positive-ordinate critical-line zeros of odd analytic multiplicity,
each counted once. -/
noncomputable def positiveCriticalLineOddZerosFinset (T : ℝ) : Finset ℂ :=
  (criticalLineOddZerosFinset T).filter fun ρ => 0 < ρ.im

lemma mem_positiveCriticalLineOddZerosFinset {T : ℝ} {ρ : ℂ} :
    ρ ∈ positiveCriticalLineOddZerosFinset T ↔
      ρ ∈ criticalLineOddZerosFinset T ∧ 0 < ρ.im := by
  simp [positiveCriticalLineOddZerosFinset]

/-- The number of positive-ordinate critical-line zeros of odd analytic
multiplicity, each counted once. -/
noncomputable def positiveCriticalLineOddZeroCount (T : ℝ) : ℕ :=
  (positiveCriticalLineOddZerosFinset T).card

end HardyTheorem
