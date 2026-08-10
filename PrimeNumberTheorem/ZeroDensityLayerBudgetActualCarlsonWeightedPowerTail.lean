import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonDyadicShellMass

/-!
# Actual Carlson weighted power tail

Dyadic shell summability can be unfolded into a summable family indexed by
the actual zeta zeros in those shells.  Dominated convergence then removes the
need for a uniform real-part gap: pointwise strict separation from the target
exponent is enough.
-/

namespace PrimeNumberTheorem

/-- A shell number together with an actual zeta zero in that shell. -/
abbrev ActualCarlsonDyadicZeroIndex (sigma : ℝ) :=
  Σ n : ℕ, {rho : ℂ // rho ∈ actualCarlsonDyadicZeroShell sigma n}

/-- The genuine explicit-formula coefficient norm attached to a dyadic zero
index, including analytic multiplicity exactly once. -/
noncomputable def actualCarlsonDyadicZeroWeight
    {sigma : ℝ} (index : ActualCarlsonDyadicZeroIndex sigma) : ℝ :=
  (analyticOrderNatAt riemannZeta index.2.1 : ℝ) / ‖index.2.1‖

/-- Real part of the zeta zero represented by a dyadic zero index. -/
def actualCarlsonDyadicZeroRealPart
    {sigma : ℝ} (index : ActualCarlsonDyadicZeroIndex sigma) : ℝ :=
  index.2.1.re

theorem actualCarlsonDyadicZeroWeight_nonneg
    {sigma : ℝ} (index : ActualCarlsonDyadicZeroIndex sigma) :
    0 ≤ actualCarlsonDyadicZeroWeight index := by
  unfold actualCarlsonDyadicZeroWeight
  positivity

/-- Summing the indexed zero weights in one shell recovers the previously
defined shell multiplicity mass. -/
theorem tsum_actualCarlsonDyadicZeroWeight_fiber
    (sigma : ℝ) (n : ℕ) :
    (∑' rho : {rho : ℂ // rho ∈ actualCarlsonDyadicZeroShell sigma n},
        actualCarlsonDyadicZeroWeight ⟨n, rho⟩) =
      actualCarlsonDyadicShellMultiplicityMass sigma n := by
  rw [tsum_fintype]
  unfold actualCarlsonDyadicZeroWeight
    actualCarlsonDyadicShellMultiplicityMass
  simpa using
    (actualCarlsonDyadicZeroShell sigma n).sum_attach
      (fun rho =>
        (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖)

/-- The coefficient norms of the actual dyadic Carlson zero family are
summable. -/
theorem summable_actualCarlsonDyadicZeroWeight
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable
      (actualCarlsonDyadicZeroWeight :
        ActualCarlsonDyadicZeroIndex sigma → ℝ) := by
  rw [summable_sigma_of_nonneg
    (fun index => actualCarlsonDyadicZeroWeight_nonneg index)]
  constructor
  · intro n
    exact (hasSum_fintype _).summable
  · simpa only [tsum_actualCarlsonDyadicZeroWeight_fiber] using
      summable_actualCarlsonDyadicShellMultiplicityMass hhalf hone

/--
Actual high-strip zeta zero power layers are negligible relative to the
target `beta` power under only pointwise strict real-part separation.

There is no uniform positive lower bound on
`beta - actualCarlsonDyadicZeroRealPart index`.  Zeros with real part equal to
`beta` are intentionally excluded by the hypothesis and must instead be put
into the visible main cluster or handled by a separate anti-cancellation
argument.
-/
theorem actualCarlsonWeightedPowerTail_tendsto_zero
    {sigma beta : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hre :
      ∀ index : ActualCarlsonDyadicZeroIndex sigma,
        actualCarlsonDyadicZeroRealPart index < beta) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∑' index : ActualCarlsonDyadicZeroIndex sigma,
          actualCarlsonDyadicZeroWeight index *
            pntPowerLayerToTargetRatio beta
              (actualCarlsonDyadicZeroRealPart index) m)
      Filter.atTop (nhds 0) := by
  exact weightedPowerLayers_tendsto_zero_of_summable
    (summable_actualCarlsonDyadicZeroWeight hhalf hone)
    actualCarlsonDyadicZeroWeight_nonneg
    hre

end PrimeNumberTheorem
