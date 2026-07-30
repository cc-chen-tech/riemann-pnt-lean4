import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticGoodHeightNaturalUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteGapTransferCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightNearOptimalTruncationParameters

/-!
# Near-optimal actual unified transfer

The actual automatic-good-height explicit-formula transfer is run at a common
outer exponent exactly `eta` below the optimized prescribed-cap ceiling.
-/

namespace PrimeNumberTheorem

open Filter

/-- Under a global positive-zero real-part bound, every allowable loss `eta`
below the optimized ceiling produces an actual unified PNT transfer at
`alpha = ceiling - eta`.

All numerical margins and outside-cluster remainder inputs are automatic. The
sole lower-direction input is the natural-point witness for the enlarged
visible cluster. -/
theorem
    exists_nearOptimalAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
    {S : Finset ℂ} {beta sigma theta eta : ℝ}
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hetaPos : 0 < eta)
    (hetaGap :
      eta <
        jointTwoHeightPrescribedCapOuterExponentCeiling
            beta sigma theta -
          (1 - beta))
    (hS : IsConjugationInvariantCluster S)
    (hzeroBound :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        0 < rho.im →
        rho.re ≤ theta) :
    ∃ tau alpha : ℝ,
      alpha =
        jointTwoHeightPrescribedCapOuterExponentCeiling
            beta sigma theta -
          eta ∧
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
      exists_jointTwoHeightNearOptimalTruncationParameters
        hbetaOne hsigmaHalf hsigmaOne hetaPos hetaGap with
    ⟨tau, alpha, gammaLow, gammaHigh, epsilonLow, epsilonHigh,
      halphaEq, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne,
      _hgammaLowEq, hgammaLow, _hgammaLowAlpha,
      _hgammaHighEq, hgammaHigh, hgammaHighAlpha,
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
    exact (by norm_num : (0 : ℝ) < 2 / 3).trans hbeta
  refine
    ⟨tau, alpha, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
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
