import HardyTheorem.HardyLittlewoodLiteratureCount

open Complex

namespace HardyTheorem

example (T : ℝ) :
    positiveCriticalLineOddZerosFinset T ⊆
      PrimeNumberTheorem.RiemannVonMangoldt.positiveCriticalLineZerosFinset T :=
  positiveCriticalLineOddZerosFinset_subset_positiveCriticalLineZerosFinset T

example (T : ℝ) :
    positiveCriticalLineOddZeroCount T ≤
      PrimeNumberTheorem.RiemannVonMangoldt.positiveCriticalLineZeroMultiplicityCount T :=
  positiveCriticalLineOddZeroCount_le_positiveCriticalLineZeroMultiplicityCount T

example (T : ℝ) :
    criticalLineOddZeroCount T ≤ positiveCriticalLineOddZeroCount T + 1 :=
  criticalLineOddZeroCount_le_positiveCriticalLineOddZeroCount_add_one T

example : hardy_littlewood_positive_odd_lower_bound_target =
    (∃ C > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (positiveCriticalLineOddZeroCount T : ℝ) ≥ C * T) := rfl

example (h : hardy_littlewood_odd_lower_bound_target) :
    hardy_littlewood_positive_odd_lower_bound_target :=
  hardy_littlewood_positive_odd_lower_bound_target_of_nonnegative h

example : hardy_littlewood_positive_odd_lower_bound_target :=
  hardy_littlewood_positive_odd_lower_bound_target_proved

example : hardy_littlewood_positive_multiplicity_lower_bound_target =
    (∃ C > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (PrimeNumberTheorem.RiemannVonMangoldt.positiveCriticalLineZeroMultiplicityCount T : ℝ) ≥
        C * T) := rfl

example (h : hardy_littlewood_positive_odd_lower_bound_target) :
    hardy_littlewood_positive_multiplicity_lower_bound_target :=
  hardy_littlewood_positive_multiplicity_lower_bound_target_of_odd h

example : hardy_littlewood_positive_multiplicity_lower_bound_target :=
  hardy_littlewood_positive_multiplicity_lower_bound_target_proved

end HardyTheorem
