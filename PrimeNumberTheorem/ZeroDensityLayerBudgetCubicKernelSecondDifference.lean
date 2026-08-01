import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderPerronKernel

open Complex

namespace PrimeNumberTheorem

/-- The second forward difference in the logarithmic variable. -/
noncomputable def secondLogForwardDifference
    (F : ℂ → ℂ) (u h : ℂ) : ℂ :=
  F (u + 2 * h) - 2 * F (u + h) + F u

/-- The normalized local factor introduced when two logarithmic differences
are applied to a cubic Perron zero term. -/
noncomputable def cubicKernelSecondDifferenceFactor (rho h : ℂ) : ℂ :=
  ((exp (rho * h) - 1) / (rho * h)) ^ 2

/-- Exact second-difference identity for a cubic Perron zero term. -/
lemma secondLogForwardDifference_exp_div_cube
    (rho u h : ℂ) :
    secondLogForwardDifference (fun v => exp (rho * v) / rho ^ 3) u h =
      exp (rho * u) * (exp (rho * h) - 1) ^ 2 / rho ^ 3 := by
  have h_one : exp (rho * (u + h)) = exp (rho * u) * exp (rho * h) := by
    rw [mul_add, exp_add]
  have h_two :
      exp (rho * (u + 2 * h)) = exp (rho * u) * (exp (rho * h)) ^ 2 := by
    calc
      exp (rho * (u + 2 * h)) =
          exp (rho * u + (rho * h + rho * h)) := by
            congr 1
            ring
      _ = exp (rho * u) * (exp (rho * h) * exp (rho * h)) := by
            rw [exp_add, exp_add]
      _ = exp (rho * u) * (exp (rho * h)) ^ 2 := by ring
  rw [secondLogForwardDifference, h_one, h_two]
  ring

/-- After division by the square step, two logarithmic differences recover
the ordinary explicit-formula amplitude `exp (rho * u) / rho`, multiplied by
one explicit local factor. -/
lemma secondLogForwardDifference_exp_div_cube_normalized
    {rho h : ℂ} (u : ℂ) (hrho : rho ≠ 0) (hh : h ≠ 0) :
    secondLogForwardDifference (fun v => exp (rho * v) / rho ^ 3) u h / h ^ 2 =
      exp (rho * u) / rho * cubicKernelSecondDifferenceFactor rho h := by
  rw [secondLogForwardDifference_exp_div_cube]
  unfold cubicKernelSecondDifferenceFactor
  field_simp [hrho, hh]

/-- The same recovery identity with an arbitrary zero coefficient, such as
analytic multiplicity and the explicit-formula sign. -/
lemma secondLogForwardDifference_const_mul_exp_div_cube_normalized
    (a : ℂ) {rho h : ℂ} (u : ℂ) (hrho : rho ≠ 0) (hh : h ≠ 0) :
    secondLogForwardDifference
          (fun v => a * (exp (rho * v) / rho ^ 3)) u h / h ^ 2 =
      a * (exp (rho * u) / rho) * cubicKernelSecondDifferenceFactor rho h := by
  have hlinear :
      secondLogForwardDifference
          (fun v => a * (exp (rho * v) / rho ^ 3)) u h =
        a * secondLogForwardDifference
          (fun v => exp (rho * v) / rho ^ 3) u h := by
    unfold secondLogForwardDifference
    ring
  rw [hlinear, mul_div_assoc,
    secondLogForwardDifference_exp_div_cube_normalized u hrho hh]
  ring

end PrimeNumberTheorem
