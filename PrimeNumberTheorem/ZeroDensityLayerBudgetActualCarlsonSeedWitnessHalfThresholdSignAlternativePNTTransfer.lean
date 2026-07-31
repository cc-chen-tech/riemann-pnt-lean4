import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSeedWitnessHalfThresholdSignedPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalSignAlternative

/-!
# Half-threshold transfer from one persistent seed sign

The existing half-threshold theorem assumes independent positive and negative
seed witnesses.  This file splits its final Carlson-boundary transfer into
one-sided forms and then accepts a disjunction of seed signs.  Consequently an
unsigned seed witness gives an actual PNT witness with one persistent sign.

The conclusion is `Omega+ OR Omega-`, not simultaneous `Omega+-`.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter

noncomputable section

/-- The positive half of the automatic Carlson-boundary signed transfer. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpPositiveTransfer_automatic
    {S : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hqNet :
      q <
        c -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarNaturalPointPositiveTargetAmplitudeWitness
      (fun m => relativeChebyshevPsi0Error (m : ℝ))
      (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  let boundary :=
    actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S
  let delta := c - q - 2 * boundary
  have hdelta : 0 < delta := by
    dsimp [delta, boundary]
    linarith
  have hresidual :=
    eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
      selection hS hhalf hone hbalance hreHigh hreReal hdelta
  have happrox :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ)| <
          (c - q) * targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards [hresidual] with m hm
    convert hm using 1 <;> dsimp [delta, boundary] <;> ring
  have htransfer :=
    hmainPos.transfer_eventually_sub_lt
      (f := fun m => relativeChebyshevPsi0Error (m : ℝ))
      (loss := c - q) happrox
  convert htransfer using 1 <;> funext m <;> ring

/-- The negative half of the automatic Carlson-boundary signed transfer. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpNegativeTransfer_automatic
    {S : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hqNet :
      q <
        c -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S)
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarNaturalPointNegativeTargetAmplitudeWitness
      (fun m => relativeChebyshevPsi0Error (m : ℝ))
      (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  let boundary :=
    actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S
  let delta := c - q - 2 * boundary
  have hdelta : 0 < delta := by
    dsimp [delta, boundary]
    linarith
  have hresidual :=
    eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
      selection hS hhalf hone hbalance hreHigh hreReal hdelta
  have happrox :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ)| <
          (c - q) * targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards [hresidual] with m hm
    convert hm using 1 <;> dsimp [delta, boundary] <;> ring
  have htransfer :=
    hmainNeg.transfer_eventually_sub_lt
      (f := fun m => relativeChebyshevPsi0Error (m : ℝ))
      (loss := c - q) happrox
  convert htransfer using 1 <;> funext m <;> ring

/--
A prescribed finite seed carrying one persistent sign survives target-line
capture and the Carlson boundary budget.  The same certificate also returns
fixed-rate relative PNT convergence.
-/
theorem exists_seedWitness_actualCarlsonHalfThresholdSignAlternativePNTTransfer
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
    (hseedSign :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S₀ (m : ℝ))
          (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)) ∨
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
      (HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            ((c - loss) / 2) * targetZeroPowerAmplitude beta (m : ℝ)) ∨
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            ((c - loss) / 2) * targetZeroPowerAmplitude beta (m : ℝ))) := by
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
  have hqNet :
      (c - loss) / 2 <
        (c - loss) -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S := by
    linarith
  have hactualSign :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            ((c - loss) / 2) * targetZeroPowerAmplitude beta (m : ℝ)) ∨
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            ((c - loss) / 2) * targetZeroPowerAmplitude beta (m : ℝ)) := by
    rcases hseedSign with hseedPos | hseedNeg
    · have hmainPos :=
        hasFarNaturalPointPositiveTargetAmplitudeWitness_visibleCluster_of_seed
          T hS₀S hseedPos hnew
      exact Or.inl
        (selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpPositiveTransfer_automatic
          (S := S) (c := c - loss) (q := (c - loss) / 2)
          selection hS hhalf hone hbalance hreHigh hreReal hqNet
          (by simpa [T] using hmainPos))
    · have hmainNeg :=
        hasFarNaturalPointNegativeTargetAmplitudeWitness_visibleCluster_of_seed
          T hS₀S hseedNeg hnew
      exact Or.inr
        (selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpNegativeTransfer_automatic
          (S := S) (c := c - loss) (q := (c - loss) / 2)
          selection hS hhalf hone hbalance hreHigh hreReal hqNet
          (by simpa [T] using hmainNeg))
  rcases
      exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
        sigma hhalf hone with
    ⟨rate, hrate, hrateOne, hupper⟩
  exact
    ⟨rate, loss, S, hrate, hrateOne, hupper,
      hloss, hnet, hS₀S, htarget, hmass, hgap, hactualSign⟩

/-- An unsigned seed witness automatically supplies the sign disjunction. -/
theorem exists_seedWitness_actualCarlsonHalfThresholdUnsignedPNTSignAlternativeTransfer
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
    (hseedUnsigned :
      HasFarNaturalPointTargetAmplitudeWitness
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
      (HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            ((c - loss) / 2) * targetZeroPowerAmplitude beta (m : ℝ)) ∨
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            ((c - loss) / 2) * targetZeroPowerAmplitude beta (m : ℝ))) := by
  exact
    exists_seedWitness_actualCarlsonHalfThresholdSignAlternativePNTTransfer
      selection hS₀ hseed hhalf hone hbalance hcap hrealStrict hseedOutside
      hseedUnsigned.signAlternative

end
end PrimeNumberTheorem
