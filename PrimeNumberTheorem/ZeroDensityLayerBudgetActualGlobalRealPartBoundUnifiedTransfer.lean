import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticGoodHeightNaturalUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteGapTransferCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightPrescribedCapFeasibility

/-!
# Global real-part bound to unified PNT transfer

A prescribed global bound on the real parts of positive nontrivial zeta zeros
now determines a Carlson endpoint above that bound.  The selected-height strip
cap and real-ordinate residual can therefore be closed automatically, leaving
only the visible finite-cluster witness in the lower-transfer direction.
-/

namespace PrimeNumberTheorem

open Filter

/-- A global positive nontrivial-zero real-part bound below the canonical
two-height threshold closes every outside-cluster remainder input in the
automatic-good-height unified transfer.

The sole remaining lower-bound input is the natural-point target-amplitude
witness for the enlarged visible cluster. -/
theorem exists_automaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
    {S : Finset ℂ} {beta theta : ℝ}
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (htheta : theta < (3 * beta - 1) / 2)
    (hS : IsConjugationInvariantCluster S)
    (hzeroBound :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        0 < rho.im →
        rho.re ≤ theta) :
    ∃ sigma tau alpha : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      theta < tau ∧
      tau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        HasFarNaturalPointTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection)
                (actualCarlsonAdjoinRealOrdinateZeros S) (m : ℝ))
            (fun m => targetZeroPowerAmplitude beta (m : ℝ)) →
        (∃ rate : ℝ,
            0 < rate ∧
            rate ≤ 1 ∧
            Tendsto
              (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (nhds 0)) ∧
          HasFarTargetAmplitudeWitness
            relativeChebyshevPsi0Error
            (fun x => targetZeroPowerAmplitude beta x / 2) := by
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters_above_cap
        hbeta hbetaOne htheta with
    ⟨sigma, tau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  have hSAdjoined :
      IsConjugationInvariantCluster
        (actualCarlsonAdjoinRealOrdinateZeros S) := by
    intro rho
    exact
      (actualCarlsonAdjoinRealOrdinateZeros_conjugationStable
        S (fun z => (hS z).symm) rho).symm
  have hreal :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0
          (actualCarlsonAdjoinRealOrdinateZeros S),
        rho.re < beta := by
    intro rho hrho
    have hempty :=
      realOrdinateNontrivialZerosOutsideClusterFinset_adjoin_eq_empty S
    rw [hempty] at hrho
    simp at hrho
  have hbetaPos : 0 < beta := by
    linarith
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hmain
  have hcap :
      ∀ (x : ℝ),
        ∀ rho ∈
          positiveNontrivialZerosOutsideClusterFinset
            (selectedUniformGoodHeight alpha selection x)
            (actualCarlsonAdjoinRealOrdinateZeros S),
          sigma < rho.re → rho.re ≤ tau := by
    intro x rho hrho _hright
    rcases
        mem_positiveNontrivialZerosOutsideClusterFinset.mp hrho with
      ⟨hzero, him, _hheight, _houtside⟩
    exact
      (hzeroBound rho hzero him).trans hthetaTau.le
  exact
    unified_automaticGoodHeight_twoHeight_naturalTargetTransfer
      (S := actualCarlsonAdjoinRealOrdinateZeros S)
      (beta := beta) (sigma := sigma) (tau := tau) (alpha := alpha)
      (gammaLow := gammaLow) (epsilonLow := epsilonLow)
      (gammaHigh := gammaHigh) (epsilonHigh := epsilonHigh)
      hbetaPos halphaOne hcontour selection hSAdjoined
      hsigmaHalf hsigmaOne halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le hepsilonHigh
      hstripLow hstripHigh hcap hreal hmain

end PrimeNumberTheorem

