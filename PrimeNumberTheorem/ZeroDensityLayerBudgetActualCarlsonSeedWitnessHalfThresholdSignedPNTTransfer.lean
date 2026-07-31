import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonTargetLineCaptureBudgetSufficiency
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTSignedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedBidirectionalPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterSeedExtension

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter

noncomputable section

 theorem exists_seedWitness_actualCarlsonHalfThresholdSignedPNTTransfer
    {S₀ : Finset ℂ} {sigma beta c : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hrealStrict :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.im = 0 → rho.re < beta)
    (hseedOutside :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S₀ < c / 2)
    (hseedPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S₀ (m : ℝ))
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hseedNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S₀ (m : ℝ))
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    ∃ rate loss : ℝ, ∃ S : Finset ℂ,
      0 < rate ∧
      rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) ∧
      0 < loss ∧
      0 < c - loss ∧
      (∀ rho ∈ S₀, rho ∈ S) ∧
      IsTargetRealPartNontrivialZeroSeed beta S ∧
      finiteVisibleClusterCoefficientMass (S \ S₀) < loss ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2 ∧
      HasFarSignedTargetAmplitudeWitnesses
        relativeChebyshevPsi0Error
        (fun x =>
          ((c - loss) / 2) * targetZeroPowerAmplitude beta x) := by
  have hsigmaBeta : sigma < beta := by linarith
  rcases
      exists_targetLine_actualCarlsonFiniteSeedCanonicalBudgets_of_seedOutside_lt_half
        hS₀ hseed hhalf hone hsigmaBeta hcap hrealStrict hseedOutside with
    ⟨loss, S, hloss, hnet, hS₀S, hS, htarget, _hcapS,
      hreHigh, hreReal, hmass, hgap⟩
  let T := selectedUniformGoodHeight
    (actualCarlsonBalancedHeightExponent sigma) selection
  have hreExtension : ∀ rho ∈ S \ S₀, rho.re ≤ beta := by
    intro rho hrho
    exact (htarget rho (Finset.mem_sdiff.mp hrho).1).2.le
  have hnew :=
    eventually_abs_dynamicVisibleClusterPNTMain_lt_loss_mul_targetAmplitude
      T (S \ S₀) hreExtension hmass
  have hmainPos :=
    hasFarNaturalPointPositiveTargetAmplitudeWitness_visibleCluster_of_seed
      T hS₀S hseedPos hnew
  have hmainNeg :=
    hasFarNaturalPointNegativeTargetAmplitudeWitness_visibleCluster_of_seed
      T hS₀S hseedNeg hnew
  have hq : 0 ≤ (c - loss) / 2 := by linarith
  have hqNet :
      (c - loss) / 2 <
        (c - loss) -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S := by
    linarith
  have hsigned :=
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedTransfer_automatic
      (S := S) (c := c - loss) (q := (c - loss) / 2)
      selection hS hhalf hone hbalance hreHigh hreReal
      hq hqNet
      (by simpa [T] using hmainPos)
      (by simpa [T] using hmainNeg)
  rcases
      exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
        sigma hhalf hone with
    ⟨rate, hrate, hrateOne, hupper⟩
  refine
    ⟨rate, loss, S, hrate, hrateOne, hupper,
      hloss, hnet, hS₀S, htarget, hmass, hgap, ?_⟩
  exact hasFarSignedTargetAmplitudeWitnesses_of_naturalPoint
    hsigned.1 hsigned.2

end
end PrimeNumberTheorem
