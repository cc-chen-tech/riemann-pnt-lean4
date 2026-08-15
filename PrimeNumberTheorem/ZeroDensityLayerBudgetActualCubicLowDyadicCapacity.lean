import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicSmoothedHighToLowTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonCertificateSummability

/-!
# Actual cubic low-layer dyadic capacity

This module packages the remaining low-height part of the actual cubic zeta-zero
energy into the interface needed by a later Gram/Schur argument.

For a uniform threshold `N`, blocks below `N` retain their full, undeleted
analytic-multiplicity capacity. Blocks at or above `N` use the Carlson
majorant with the explicit fifth logarithmic power: four logarithms from the
density input and one from the local multiplicity bound. Removing any finite
set of zeros only decreases the nonnegative block mass, so the same bound is
uniform in the deleted set.

No decay of the complete low layer, Gram/Schur estimate, or oscillation theorem
is asserted here.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem

noncomputable section

/-- A low-layer block majorant: retain finitely many initial actual capacities,
then use the explicit Carlson `log^5` dyadic majorant. -/
def actualCubicLowDyadicL2BlockCapacityMajorant {sigma : ℝ}
    (certificate : CarlsonEventualMajorant sigma)
    (B x tau : ℝ) (N n : ℕ) : ℝ :=
  if n < N then
    actualCubicDyadicStripSquareCapacity x sigma tau n
  else
    actualCubicCarlsonDyadicLogFifthMajorant
      (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
      sigma n

/-- The target-scale normalized sum of the low-layer block majorants. -/
def actualCubicNormalizedLowDyadicL2CapacityMajorant {sigma : ℝ}
    (certificate : CarlsonEventualMajorant sigma)
    (B beta tau gamma : ℝ) (N : ℕ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ (-2 * beta) *
    ∑ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
      actualCubicLowDyadicL2BlockCapacityMajorant
        certificate B (m : ℝ) tau N n

@[simp]
theorem actualCubicLowDyadicL2BlockCapacityMajorant_eq_capacity_of_lt
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (B x tau : ℝ) (N n : ℕ) (hn : n < N) :
    actualCubicLowDyadicL2BlockCapacityMajorant certificate B x tau N n =
      actualCubicDyadicStripSquareCapacity x sigma tau n := by
  simp [actualCubicLowDyadicL2BlockCapacityMajorant, hn]

@[simp]
theorem actualCubicLowDyadicL2BlockCapacityMajorant_eq_logFifth_of_ge
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (B x tau : ℝ) (N n : ℕ) (hn : N ≤ n) :
    actualCubicLowDyadicL2BlockCapacityMajorant certificate B x tau N n =
      actualCubicCarlsonDyadicLogFifthMajorant
        (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
        sigma n := by
  simp [actualCubicLowDyadicL2BlockCapacityMajorant, Nat.not_lt_of_ge hn]

/-- The actual low-height cubic energy, after deleting an arbitrary finite set
of zeros, is bounded by finitely many undeleted block capacities followed by a
uniform Carlson `log^5` tail. -/
theorem exists_actualCubicNormalizedSmoothedStripEnergyUpTo_le_lowDyadicL2CapacityMajorant
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N : ℕ,
      ∀ (beta tau gamma : ℝ) (S : Finset ℂ) (m : ℕ),
        1 ≤ m →
        actualCubicNormalizedSmoothedStripEnergyUpTo
            beta sigma tau gamma S m ≤
          actualCubicNormalizedLowDyadicL2CapacityMajorant
            certificate B beta tau gamma N m := by
  obtain ⟨B, hB, hcapacity⟩ :=
    exists_actualCubicDyadicStripSquareCapacityExcluding_le_count
  have hcount :=
    certificate.eventually_forall_actualCubicDyadicCountMajorant_le hB
  have hlog :=
    certificate.eventually_forall_actualCubicCertificateBlock_le_logFifth hB
  have htwo : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  have htail : ∀ᶠ n : ℕ in atTop,
      ∀ (x tau : ℝ), 1 ≤ x → ∀ S : Finset ℂ,
        actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
          actualCubicCarlsonDyadicLogFifthMajorant
            (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
            sigma n := by
    filter_upwards [hcount, hlog, htwo] with n hcountn hlogn hn
    intro x tau hx S
    have hfour : (4 : ℝ) ≤ (2 : ℝ) ^ n := by
      calc
        (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    calc
      actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
          actualCubicDyadicCountMajorant B x sigma tau n := by
        simpa [actualCubicDyadicCountMajorant] using
          hcapacity x sigma tau n hx hfour S
      _ ≤ actualCubicCarlsonCertificateBlockMajorant certificate B x tau n :=
        hcountn x tau hx
      _ ≤ actualCubicCarlsonDyadicLogFifthMajorant
            (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
            sigma n := hlogn x tau hx
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  refine ⟨B, hB, N, ?_⟩
  intro beta tau gamma S m hm
  unfold actualCubicNormalizedSmoothedStripEnergyUpTo
  unfold actualCubicNormalizedLowDyadicL2CapacityMajorant
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro n hn
    by_cases hnN : n < N
    · rw [actualCubicLowDyadicL2BlockCapacityMajorant_eq_capacity_of_lt
          certificate B (m : ℝ) tau N n hnN]
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      exact actualCubicDyadicStripSquareCapacityExcluding_le
        (m : ℝ) sigma tau n S hm0
    · have hNn : N ≤ n := Nat.le_of_not_gt hnN
      rw [actualCubicLowDyadicL2BlockCapacityMajorant_eq_logFifth_of_ge
          certificate B (m : ℝ) tau N n hNn]
      exact hN n hNn (m : ℝ) tau (by exact_mod_cast hm) S
  · exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le m) _

end

end PrimeNumberTheorem
