import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonCanonicalTwoStripAutomaticNorm
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualLowLayerDecay

/-!
# Actual decay of the positive critical half

The canonical low layer at threshold `1 / 2` contains the positive-ordinate
zeros with real part at most the critical line.  Global zero multiplicity,
the automatic uniform norm lower bound, and a polynomial height
`x ^ alpha` make its relative PNT contribution tend to zero whenever
`alpha < 1 / 2` with a strict logarithmic margin.
-/

open Filter
open scoped Topology

namespace PrimeNumberTheorem

/-- Canonical empty-cluster input split at the critical line. -/
noncomputable def actualCriticalHalfCanonicalInput
    (alpha x : ℝ) :
    PositiveZeroOutsideClusterBucketInput
      (carlsonPolynomialHeight alpha x) ∅ 2 :=
  pntHybridCanonicalTwoStripOutsideClusterBucketInput
    (1 / 2) (carlsonPolynomialHeight alpha x) ∅

theorem actualCriticalHalfCanonicalInput_low_re_le
    {alpha x : ℝ} {rho : ℂ}
    (hrho : rho ∈ (actualCriticalHalfCanonicalInput alpha x).layer
      (0 : Fin 2)) :
    rho.re ≤ 1 / 2 := by
  exact pntHybridCanonicalTwoStripOutsideCluster_low_re_le hrho

/-- The actual signed positive-ordinate contribution from the critical half
tends to zero at ordinary relative-PNT scale. -/
theorem tendsto_actualCriticalHalfCanonicalPNTLayerNorm
    {alpha epsilon : ℝ}
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : alpha + epsilon < 1 / 2) :
    Tendsto
      (fun x =>
        dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) ∅
          (actualCriticalHalfCanonicalInput alpha)
          (0 : Fin 2) x)
      atTop (nhds 0) := by
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        (carlsonPolynomialHeight alpha) (1 / 2) ∅ with
    ⟨kappa, hkappa, hnorm⟩
  have hraw :=
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_of_hybrid
      (input := actualCriticalHalfCanonicalInput alpha)
      (i := (0 : Fin 2))
      (beta := 1) (tau := (1 / 2 : ℝ))
      (kappa := kappa) (epsilon := epsilon)
      hkappa
      (by
        intro x rho hrho
        exact hnorm x rho hrho)
      (by
        intro x rho hrho
        exact actualCriticalHalfCanonicalInput_low_re_le hrho)
      halpha hepsilon (by linarith)
  convert hraw using 1
  funext x
  simp [dynamicPositiveOutsideClusterPNTLayerNorm,
    targetZeroPowerAmplitude]

end PrimeNumberTheorem
