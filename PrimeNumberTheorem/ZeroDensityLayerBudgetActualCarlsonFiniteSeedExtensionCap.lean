import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapTransferCluster

/-!
# Real-part cap for the finite-seed extension

The finite-seed Carlson selector already reports that every newly adjoined
member outside the real-ordinate slice lies on `Re rho = beta`.  Members in
the real-ordinate slice are nontrivial zeta zeros, so the original
outside-seed zeta cap applies to them.  Combining these two cases gives the
uniform cap required by the explicit finite coefficient-mass estimate.
-/

namespace PrimeNumberTheorem

open Complex

/-- Boundary support plus the original outside-seed zeta cap controls every
member of the finite extension `S \ S₀`. -/
theorem finiteSeedExtension_realPart_le_of_boundarySupport
    {S₀ S : Finset ℂ} {beta : ℝ}
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hsupport :
      ∀ rho ∈ S,
        rho ∉ S₀ →
          rho ∉ realOrdinateNontrivialZerosFinset 0 →
            rho.re = beta) :
    ∀ rho ∈ S \ S₀, rho.re ≤ beta := by
  intro rho hrho
  have hmemS : rho ∈ S := (Finset.mem_sdiff.mp hrho).1
  have houtSeed : rho ∉ S₀ := (Finset.mem_sdiff.mp hrho).2
  by_cases hreal : rho ∈ realOrdinateNontrivialZerosFinset 0
  · exact
      hcap rho
        (mem_nontrivialZerosFinset.mp
          (mem_realOrdinateNontrivialZerosFinset.mp hreal).1).1
        houtSeed
  · exact (hsupport rho hmemS houtSeed hreal).le

end PrimeNumberTheorem
