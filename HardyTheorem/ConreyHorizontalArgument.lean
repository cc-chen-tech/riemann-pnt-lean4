import HardyTheorem.ConreyHorizontalJensenAsymptotic

/-! Unweighted horizontal argument estimates without reselecting heights. -/

open Complex Set MeasureTheory MeromorphicOn
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

/-- The cutoff-two mollifier is exactly one. This auxiliary identity does
not replace the long mollifier in the mean-square integral. -/
theorem conreyMollifier_two {P : ℝ → ℝ} (hP0 : P 0 = 0) (hP1 : P 1 = 1)
    (sigma0 : ℝ) (s : ℂ) : conreyMollifier 2 sigma0 P s = 1 := by
  have hcoeff := conreyMollifierCoefficient_one (by norm_num : 2 ≤ (2 : ℕ)) hP1 sigma0
  have htwo : conreyMollifierCoefficient 2 sigma0 P 2 = 0 := by
    simp [conreyMollifierCoefficient, hP0]
  have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
  simp [conreyMollifier, selbergMollifier, hIcc, hcoeff, htwo]

private theorem im_inv_horizontal_sub_eq_zero {t : ℝ} {rho : ℂ}
    (ht : t = rho.im) (x : ℝ) : (((x : ℂ) + I * t - rho)⁻¹).im = 0 := by
  apply abs_eq_zero.mp
  rw [abs_im_inv_horizontal_sub_eq_poissonKernel, ht]
  simp

private theorem continuous_im_inv_horizontal_sub (t : ℝ) (rho : ℂ) :
    Continuous (fun x : ℝ => (((x : ℂ) + I * t - rho)⁻¹).im) := by
  by_cases ht : t = rho.im
  · simpa only [im_inv_horizontal_sub_eq_zero ht] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · have hne : ∀ x : ℝ, (x : ℂ) + I * t - rho ≠ 0 := by
      intro x hx
      have him := congrArg Complex.im hx
      simp at him
      exact ht (sub_eq_zero.mp him)
    exact Complex.continuous_im.comp
      ((by fun_prop : Continuous (fun x : ℝ => (x : ℂ) + I * t - rho)).inv₀ hne)

/-- Only the scalar imaginary kernel is asserted integrable, even when
the horizontal line passes through the pole of the full complex kernel. -/
theorem intervalIntegrable_im_inv_horizontal_sub {a b t : ℝ} {rho : ℂ} :
    IntervalIntegrable (fun x : ℝ => (((x : ℂ) + I * t - rho)⁻¹).im) volume a b :=
  (continuous_im_inv_horizontal_sub t rho).intervalIntegrable _ _

/-- The one-zero Poisson bound needs no separation of zero ordinates. -/
theorem integral_abs_im_inv_horizontal_sub_le_pi_all_heights
    {a b t : ℝ} {rho : ℂ} :
    (∫ x in a..b, |(((x : ℂ) + I * t - rho)⁻¹).im|) ≤ Real.pi := by
  by_cases ht : t = rho.im
  · simp only [im_inv_horizontal_sub_eq_zero ht, abs_zero, intervalIntegral.integral_zero]
    exact Real.pi_pos.le
  · exact integral_abs_im_inv_horizontal_sub_le_pi ht

/-- Full nonnegative multiplicities cost at most `pi` per zero, at every
height; the finite interchange is justified by scalar integrability. -/
theorem abs_integral_finset_principalParts_le (P : Finset ℂ) (m : ℂ → ℝ)
    {a b t : ℝ} (hab : a ≤ b) (hm : ∀ rho ∈ P, 0 ≤ m rho) :
    |∫ x in a..b, ∑ rho ∈ P, m rho *
      (((x : ℂ) + I * t - rho)⁻¹).im| ≤ Real.pi * ∑ rho ∈ P, m rho := by
  have hint : ∀ rho ∈ P, IntervalIntegrable
      (fun x : ℝ => m rho * (((x : ℂ) + I * t - rho)⁻¹).im) volume a b := by
    intro rho _
    exact intervalIntegrable_im_inv_horizontal_sub.const_mul _
  rw [intervalIntegral.integral_finsetSum hint]
  calc
    _ ≤ ∑ rho ∈ P, |∫ x in a..b, m rho * (((x : ℂ) + I * t - rho)⁻¹).im| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ rho ∈ P, m rho * Real.pi := by
      apply Finset.sum_le_sum
      intro rho hrho
      rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (hm rho hrho)]
      exact mul_le_mul_of_nonneg_left
        ((intervalIntegral.abs_integral_le_integral_abs hab).trans
          integral_abs_im_inv_horizontal_sub_le_pi_all_heights) (hm rho hrho)
    _ = _ := by rw [← Finset.sum_mul]; ring

end HardyTheorem
