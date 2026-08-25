import HardyTheorem.SelbergSArithmeticFiniteConvolution

open scoped BigOperators

namespace HardyTheorem

/-!
# Selberg S-arith: the logarithmic Euler-weight tail

This combines the divisor majorant, the summable squarefree coefficient,
the finite Dirichlet-convolution injection, and the harmonic bound.  It is
the precise statement that the final arithmetic sum loses only one logarithm.
-/

private theorem selberg_divisorSum_recip_eq_convolution
    {r : ℕ} :
    (r : ℝ)⁻¹ *
        (∑ d ∈ r.divisors, selbergNineSquarefreeDivisorCoeff d) =
      ∑ p ∈ r.divisorsAntidiagonal,
        (selbergNineSquarefreeDivisorCoeff p.1 / (p.1 : ℝ)) *
          (p.2 : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  rw [← Nat.sum_divisorsAntidiagonal
    (fun d _ => (r : ℝ)⁻¹ * selbergNineSquarefreeDivisorCoeff d)]
  apply Finset.sum_congr rfl
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← hprod]
  push_cast
  simp only [mul_inv, div_eq_mul_inv]
  ring

/-- Uniform logarithmic bound for the arithmetic Euler-weight tail. -/
theorem exists_selbergNineProduct_logTail_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℕ,
      (∑ r ∈ Finset.Icc 1 Y,
        (r : ℝ)⁻¹ *
          ∏ p ∈ r.primeFactors, (1 + 9 * (p : ℝ)⁻¹)) ≤
        C * (1 + Real.log (Y : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_selbergNineSquarefreeDivisorCoeff_partialSum_le
  refine ⟨C, hC0, fun Y => ?_⟩
  let b : ℕ → ℝ := fun d =>
    selbergNineSquarefreeDivisorCoeff d / (d : ℝ)
  let c : ℕ → ℝ := fun m => (m : ℝ)⁻¹
  have hb (d : ℕ) : 0 ≤ b d :=
    div_nonneg (selbergNineSquarefreeDivisorCoeff_nonneg d)
      (Nat.cast_nonneg d)
  have hc (m : ℕ) : 0 ≤ c m := inv_nonneg.mpr (Nat.cast_nonneg m)
  calc
    (∑ r ∈ Finset.Icc 1 Y,
        (r : ℝ)⁻¹ *
          ∏ p ∈ r.primeFactors, (1 + 9 * (p : ℝ)⁻¹)) ≤
        ∑ r ∈ Finset.Icc 1 Y,
          (r : ℝ)⁻¹ *
            ∑ d ∈ r.divisors,
              selbergNineSquarefreeDivisorCoeff d := by
      apply Finset.sum_le_sum
      intro r hr
      have hr0 : r ≠ 0 := by
        have hrange : 1 ≤ r ∧ r ≤ Y := Finset.mem_Icc.mp hr
        exact Nat.one_le_iff_ne_zero.mp hrange.1
      exact mul_le_mul_of_nonneg_left
        (selbergNineProduct_le_divisorSum hr0)
        (inv_nonneg.mpr (Nat.cast_nonneg r))
    _ = ∑ r ∈ Finset.Icc 1 Y,
          ∑ p ∈ r.divisorsAntidiagonal, b p.1 * c p.2 := by
      apply Finset.sum_congr rfl
      intro r _
      exact selberg_divisorSum_recip_eq_convolution
    _ ≤ (∑ d ∈ Finset.Icc 1 Y, b d) *
          ∑ m ∈ Finset.Icc 1 Y, c m :=
      selberg_finite_dirichlet_sum_le_product Y hb hc
    _ ≤ C * (1 + Real.log (Y : ℝ)) := by
      apply mul_le_mul
      · exact hC (Finset.Icc 1 Y)
      · exact selberg_sum_Icc_inv_le_one_add_log Y
      · exact Finset.sum_nonneg fun m _ => hc m
      · exact hC0

end HardyTheorem
