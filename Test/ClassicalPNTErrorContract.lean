import RiemannPNT

open PrimeNumberTheorem

example :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |chebyshevPsi x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
  exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log

example :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |chebyshevPsi x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
  RiemannPNT.API.exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log
