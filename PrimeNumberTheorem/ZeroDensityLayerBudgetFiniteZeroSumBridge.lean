import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzKernelAutomatic

/-!
# Bridge to the existing finite PNT zero sum

The multiplicity-weighted contributions used by the Pintz--Carlson layer
machine are identified with the project's existing
`finiteNontrivialZeroSumWithMultiplicity`.  This removes an abstract-kernel
boundary without claiming control of the still-explicit real-ordinate
residual or of the truncated explicit-formula remainder.
-/

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem

/-- Summing the signed per-zero PNT contributions recovers the negative of the
existing multiplicity-weighted finite zero sum. -/
theorem sum_pntFiniteZeroContribution_eq_neg_finiteNontrivialZeroSumWithMultiplicity
    (x T : ℝ) :
    (∑ rho ∈ nontrivialZerosFinset T,
        pntFiniteZeroContribution x rho) =
      -finiteNontrivialZeroSumWithMultiplicity x T := by
  unfold finiteNontrivialZeroSumWithMultiplicity
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  simp [pntFiniteZeroContribution, pntExplicitFormulaZeroTerm]

/-- The normalized per-zero sum is exactly `x⁻¹` times the negative existing
finite zero sum. -/
theorem sum_pntRelativeZeroContribution_eq_inv_mul_neg_finiteNontrivialZeroSumWithMultiplicity
    (x T : ℝ) :
    (∑ rho ∈ nontrivialZerosFinset T,
        pntRelativeZeroContribution x rho) =
      ((x : ℂ)⁻¹) *
        (-finiteNontrivialZeroSumWithMultiplicity x T) := by
  simp only [pntRelativeZeroContribution]
  rw [← Finset.mul_sum]
  exact congrArg (fun z : ℂ => ((x : ℂ)⁻¹) * z)
    (sum_pntFiniteZeroContribution_eq_neg_finiteNontrivialZeroSumWithMultiplicity
      x T)

/-- For positive `x`, the normalized contribution norm is the existing finite
zero-sum norm divided by `x`. -/
theorem norm_sum_pntRelativeZeroContribution_eq_norm_finiteNontrivialZeroSumWithMultiplicity_div
    {x : ℝ} (hx : 0 < x) (T : ℝ) :
    ‖∑ rho ∈ nontrivialZerosFinset T,
        pntRelativeZeroContribution x rho‖ =
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ / x := by
  rw [
    sum_pntRelativeZeroContribution_eq_inv_mul_neg_finiteNontrivialZeroSumWithMultiplicity,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
    norm_neg]
  ring

/-- The automatic Pintz--Carlson layer estimate now bounds the project's
actual multiplicity-weighted finite PNT zero sum.  The real-ordinate residual
is retained explicitly and is scaled back by `x`. -/
theorem PositiveZeroBucketInput.norm_finiteNontrivialZeroSumWithMultiplicity_le_pintz
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (hx : 1 ≤ x) :
    ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
      x *
        (2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
            (Finset.univ : Finset (Fin n)) input.sigma () x T +
          ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
            pntRelativeZeroContribution x rho‖) := by
  have hxpos : 0 < x :=
    lt_of_lt_of_le zero_lt_one hx
  have hrelative :=
    input.norm_full_pntRelativeZeroContribution_sum_le_pintz hx
  rw [
    norm_sum_pntRelativeZeroContribution_eq_norm_finiteNontrivialZeroSumWithMultiplicity_div
      hxpos T] at hrelative
  have hscaled := (div_le_iff₀ hxpos).mp hrelative
  simpa [mul_comm] using hscaled

end PrimeNumberTheorem
