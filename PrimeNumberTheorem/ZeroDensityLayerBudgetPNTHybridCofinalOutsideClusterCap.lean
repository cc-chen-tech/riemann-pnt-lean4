import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCanonicalBetaThresholdTransfer

/-!
# Cofinal height caps are global caps

A real-part cap imposed at every point of a cofinal dynamic-height schedule is
not a weaker finite-height hypothesis: every fixed zeta zero eventually lies
below the schedule. This module records the exact equivalence.
-/

open Filter

namespace PrimeNumberTheorem

/-- Every outside-cluster nontrivial zero visible at `height x` has real part
at most `upper`. -/
def HeightwiseOutsideClusterRealPartCap
    (height : ℝ → ℝ) (S : Finset ℂ) (upper : ℝ) : Prop :=
  ∀ x : ℝ, ∀ rho : ℂ,
    RiemannHypothesis.IsNontrivialZero rho →
      |rho.im| ≤ height x →
        rho ∉ S →
          rho.re ≤ upper

/--
Along a cofinal height schedule, a heightwise outside-cluster real-part cap
is equivalent to the global cap.

Thus replacing the global hypothesis by the same fixed cap at every selected
height does not remove any mathematical input.
-/
theorem heightwiseOutsideClusterRealPartCap_iff_global
    {height : ℝ → ℝ} {S : Finset ℂ} {upper : ℝ}
    (hheight : Tendsto height atTop atTop) :
    HeightwiseOutsideClusterRealPartCap height S upper ↔
      OutsideClusterRealPartCap S upper := by
  constructor
  · intro hlocal rho hzero hout
    have heventually :
        ∀ᶠ x in atTop, |rho.im| ≤ height x :=
      (tendsto_atTop.1 hheight) |rho.im|
    rcases heventually.exists with ⟨x, hx⟩
    exact hlocal x rho hzero hx hout
  · intro hglobal x rho hzero _ hout
    exact hglobal rho hzero hout

/-- The optimized hybrid selected height has the same local/global cap
equivalence whenever its mixed density budget is feasible. -/
theorem hybridSelectedHeightOutsideClusterRealPartCap_iff_global
    {n : ℕ} {beta upper : ℝ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
            pntHybridAffineDensityFloor beta <
          pntHybridAffineDensityCeiling beta tau i)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ) :
    HeightwiseOutsideClusterRealPartCap
        (pntHybridAffineSelectedGoodHeight beta sigma tau selection)
        S upper ↔
      OutsideClusterRealPartCap S upper := by
  exact heightwiseOutsideClusterRealPartCap_iff_global
    (pntHybridAffineSelectedGoodHeight_tendsto_atTop
      sigma tau hbetaOne hsigmaOneHigh hbudget selection)

end PrimeNumberTheorem
