import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonDyadicReciprocalCount

/-!
# Actual Carlson dyadic shell mass

This module partitions the actual Carlson zero finsets into dyadic ordinate
shells and transfers reciprocal-count summability to the genuine analytic
multiplicity-over-norm mass used by explicit-formula coefficients.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

/-- Zeta zeros counted by Carlson above `sigma` with ordinate in
`(2^n, 2^(n+1)]`. -/
noncomputable def actualCarlsonDyadicZeroShell
    (sigma : ℝ) (n : ℕ) : Finset ℂ :=
  ZeroDensity.zeroDensityZerosFinset sigma ((2 : ℝ) ^ (n + 1)) \
    ZeroDensity.zeroDensityZerosFinset sigma ((2 : ℝ) ^ n)

theorem actualCarlsonDyadicZeroShell_im_gt
    {sigma : ℝ} {n : ℕ} {rho : ℂ}
    (hrho : rho ∈ actualCarlsonDyadicZeroShell sigma n) :
    (2 : ℝ) ^ n < rho.im := by
  have hdiff := Finset.mem_sdiff.mp hrho
  have hup := ZeroDensity.mem_zeroDensityZerosFinset.mp hdiff.1
  by_contra hle
  apply hdiff.2
  exact ZeroDensity.mem_zeroDensityZerosFinset.mpr
    ⟨hup.1, hup.2.1, le_of_not_gt hle, hup.2.2.2⟩

/-- Reciprocal-norm analytic multiplicity mass of one dyadic shell. -/
noncomputable def actualCarlsonDyadicShellMultiplicityMass
    (sigma : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroShell sigma n,
    (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖

theorem actualCarlsonDyadicShellMultiplicityMass_nonneg
    (sigma : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicShellMultiplicityMass sigma n := by
  unfold actualCarlsonDyadicShellMultiplicityMass
  positivity

theorem actualCarlsonDyadicShellMultiplicityMass_le_count_div
    (sigma : ℝ) (n : ℕ) :
    actualCarlsonDyadicShellMultiplicityMass sigma n ≤
      actualCarlsonDyadicCount sigma (n + 1) / (2 : ℝ) ^ n := by
  have hterm :
      ∀ rho ∈ actualCarlsonDyadicZeroShell sigma n,
        (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ≤
          (analyticOrderNatAt riemannZeta rho : ℝ) / (2 : ℝ) ^ n := by
    intro rho hrho
    exact div_le_div_of_nonneg_left
      (Nat.cast_nonneg _)
      (by positivity)
      ((actualCarlsonDyadicZeroShell_im_gt hrho).le.trans
        (Complex.im_le_norm rho))
  have hmass :
      (∑ rho ∈ actualCarlsonDyadicZeroShell sigma n,
          (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
        actualCarlsonDyadicCount sigma (n + 1) := by
    unfold actualCarlsonDyadicCount actualCarlsonDyadicZeroShell
      ZeroDensity.zeroDensityCount
    exact_mod_cast
      Finset.sum_le_sum_of_subset_of_nonneg
        Finset.sdiff_subset
        (fun _ _ _ => Nat.zero_le _)
  unfold actualCarlsonDyadicShellMultiplicityMass
  calc
    (∑ rho ∈ actualCarlsonDyadicZeroShell sigma n,
        (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖) ≤
        ∑ rho ∈ actualCarlsonDyadicZeroShell sigma n,
          (analyticOrderNatAt riemannZeta rho : ℝ) / (2 : ℝ) ^ n :=
      Finset.sum_le_sum hterm
    _ =
        (∑ rho ∈ actualCarlsonDyadicZeroShell sigma n,
          (analyticOrderNatAt riemannZeta rho : ℝ)) / (2 : ℝ) ^ n := by
      rw [Finset.sum_div]
    _ ≤ actualCarlsonDyadicCount sigma (n + 1) / (2 : ℝ) ^ n :=
      div_le_div_of_nonneg_right hmass (by positivity)

theorem actualCarlsonDyadicCount_div_lower_eq_two_mul_weighted_succ
    (sigma : ℝ) (n : ℕ) :
    actualCarlsonDyadicCount sigma (n + 1) / (2 : ℝ) ^ n =
      2 * pntDyadicReciprocalWeightedCount
        (actualCarlsonDyadicCount sigma) (n + 1) := by
  unfold pntDyadicReciprocalWeightedCount
  rw [pow_succ]
  ring

/-- The genuine multiplicity-over-norm masses of all strict Carlson dyadic
shells are summable. -/
theorem summable_actualCarlsonDyadicShellMultiplicityMass
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable (actualCarlsonDyadicShellMultiplicityMass sigma) := by
  have hcount :
      Summable
        (pntDyadicReciprocalWeightedCount
          (actualCarlsonDyadicCount sigma)) :=
    exists_summable_actualCarlsonDyadicReciprocalCount hhalf hone
  have hshift :
      Summable (fun n =>
        pntDyadicReciprocalWeightedCount
          (actualCarlsonDyadicCount sigma) (n + 1)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff 1).mpr hcount
  apply Summable.of_nonneg_of_le
    (actualCarlsonDyadicShellMultiplicityMass_nonneg sigma)
    (fun n => ?_)
    (hshift.mul_left 2)
  rw [← actualCarlsonDyadicCount_div_lower_eq_two_mul_weighted_succ]
  exact actualCarlsonDyadicShellMultiplicityMass_le_count_div sigma n

end PrimeNumberTheorem
