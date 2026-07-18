import RiemannPNT

open PrimeNumberTheorem

example :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
  exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log

example :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
  RiemannPNT.API.exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log
