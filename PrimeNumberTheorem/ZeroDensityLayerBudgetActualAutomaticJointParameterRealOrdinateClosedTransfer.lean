import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticJointParameterUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteGapTransferCluster

/-!
# Real-ordinate-closed automatic joint-parameter transfer

The finite-cluster API can canonically adjoin every real-ordinate nontrivial
zero.  This preserves conjugation invariance and makes the real-ordinate
outside-cluster residual empty.  Applying the automatic joint-parameter
transfer to that enlarged cluster removes one analytic hypothesis.
-/

namespace PrimeNumberTheorem

open Filter

/-- After adjoining the fixed real-ordinate zero set to a
conjugation-invariant cluster, the automatic joint-parameter transfer needs
only the selected-height strip cap and the visible-cluster witness.

Both remaining hypotheses intentionally refer to the enlarged cluster. -/
theorem exists_automaticGoodHeight_jointParameterRealOrdinateClosedTransfer
    {S : Finset ℂ} {beta : ℝ}
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (hS : IsConjugationInvariantCluster S) :
    ∃ sigma tau alpha : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      tau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        (∀ (x : ℝ),
          ∀ rho ∈
            positiveNontrivialZerosOutsideClusterFinset
              (selectedUniformGoodHeight alpha selection x)
              (actualCarlsonAdjoinRealOrdinateZeros S),
            sigma < rho.re → rho.re ≤ tau) →
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
      exists_automaticGoodHeight_jointParameterNaturalTargetTransfer
        (S := actualCarlsonAdjoinRealOrdinateZeros S)
        hbeta hbetaOne with
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, htauBeta,
      hcontour, halpha, halphaOne, htransfer⟩
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
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hcap hmain
  exact
    htransfer selection hSAdjoined hcap hreal hmain

end PrimeNumberTheorem
