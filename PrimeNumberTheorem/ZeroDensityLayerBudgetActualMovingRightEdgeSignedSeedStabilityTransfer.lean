import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetSignedTargetAmplitudeRealTransfer

/-!
# Signed actual PNT transfer from a fixed seed in a moving right-edge cluster

Positive and negative natural-point witnesses for a fixed finite target-line
seed survive an eventually containing moving right-edge cluster with the same
coefficient loss.  One common Carlson and explicit-formula residual bound then
transfers both signs to the actual relative Chebyshev error.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A positive fixed-seed witness survives an eventually containing moving
extension with the exact assigned coefficient loss. -/
theorem
    hasFarNaturalPointPositiveTargetAmplitudeWitness_movingVisibleCluster_of_seed
    (T : ℝ → ℝ) {S₀ : Finset ℂ} (S : ℕ → Finset ℂ)
    {amplitude : ℕ → ℝ} {c loss : ℝ}
    (hsub : ∀ᶠ m : ℕ in atTop, ∀ rho ∈ S₀, rho ∈ S m)
    (hseed :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain T S₀ (m : ℝ))
        (fun m => c * amplitude m))
    (hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain
            T (S m \ S₀) (m : ℝ)| <
          loss * amplitude m) :
    HasFarNaturalPointPositiveTargetAmplitudeWitness
      (fun m =>
        dynamicVisibleClusterPNTMain T (S m) (m : ℝ))
      (fun m => (c - loss) * amplitude m) := by
  apply hseed.transfer_eventually_sub_lt
  filter_upwards [hsub, hnew] with m hsubM hnewM
  rw [dynamicVisibleClusterPNTMain_sub_seed_eq_extension
    T hsubM (m : ℝ)]
  exact hnewM

/-- A negative fixed-seed witness survives the same moving extension and
coefficient loss. -/
theorem
    hasFarNaturalPointNegativeTargetAmplitudeWitness_movingVisibleCluster_of_seed
    (T : ℝ → ℝ) {S₀ : Finset ℂ} (S : ℕ → Finset ℂ)
    {amplitude : ℕ → ℝ} {c loss : ℝ}
    (hsub : ∀ᶠ m : ℕ in atTop, ∀ rho ∈ S₀, rho ∈ S m)
    (hseed :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain T S₀ (m : ℝ))
        (fun m => c * amplitude m))
    (hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain
            T (S m \ S₀) (m : ℝ)| <
          loss * amplitude m) :
    HasFarNaturalPointNegativeTargetAmplitudeWitness
      (fun m =>
        dynamicVisibleClusterPNTMain T (S m) (m : ℝ))
      (fun m => (c - loss) * amplitude m) := by
  apply hseed.transfer_eventually_sub_lt
  filter_upwards [hsub, hnew] with m hsubM hnewM
  rw [dynamicVisibleClusterPNTMain_sub_seed_eq_extension
    T hsubM (m : ℝ)]
  exact hnewM

/-- Fixed-parameter signed lower transfer from a finite target-line seed
through the moving right-edge cluster to the actual PNT error. -/
theorem
    automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalPointLowerTransfer
    {S₀ : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh c loss : ℝ}
    (hbeta : 0 < beta)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (htau : tau < beta)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh :
      alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHigh : 0 < gammaHigh)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hepsilonHigh : 0 < epsilonHigh)
    (hstripLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0)
    (hstripHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0)
    (hnet : 0 < c - loss)
    (hS₀ : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hseedPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection)
            S₀ (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hseedNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection)
            S₀ (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection)
            (movingRightEdgeExceptionalCluster
                (selectedUniformGoodHeight alpha selection)
                tau (m : ℝ) \ S₀)
            (m : ℝ)| <
          loss * targetZeroPowerAmplitude beta (m : ℝ)) :
    HasFarSignedTargetAmplitudeWitnesses
      relativeChebyshevPsi0Error
      (fun x =>
        ((c - loss) * targetZeroPowerAmplitude beta x) / 2) := by
  let H := selectedUniformGoodHeight alpha selection
  have hheight :=
    eventually_selectedUniformGoodHeight_nonneg_le_polynomial
      halpha selection
  have hHnonneg :
      ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hheight.mono fun _ hx => hx.1
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x :=
    hheight.mono fun _ hx => hx.2
  have hcomplement :=
    selectedMovingRightEdgeOutsideClusterComplement_targetAmplitudeNegligible
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hHnonneg hHle
  have hremainder :=
    selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hcontourMargin selection
  have hsub :
      ∀ᶠ m : ℕ in atTop,
        ∀ rho ∈ S₀,
          rho ∈ movingRightEdgeExceptionalCluster H tau (m : ℝ) := by
    simpa [H] using
      eventually_targetSeed_subset_selectedMovingRightEdgeExceptionalCluster
        halpha selection htau hS₀
  have hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          movingRightEdgeVisibleClusterPNTMain H tau (m : ℝ))
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ)) := by
    simpa [movingRightEdgeVisibleClusterPNTMain, H] using
      hasFarNaturalPointPositiveTargetAmplitudeWitness_movingVisibleCluster_of_seed
        H
        (fun m : ℕ =>
          movingRightEdgeExceptionalCluster H tau (m : ℝ))
        hsub
        (by simpa [H] using hseedPos)
        (by simpa [H] using hnew)
  have hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          movingRightEdgeVisibleClusterPNTMain H tau (m : ℝ))
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ)) := by
    simpa [movingRightEdgeVisibleClusterPNTMain, H] using
      hasFarNaturalPointNegativeTargetAmplitudeWitness_movingVisibleCluster_of_seed
        H
        (fun m : ℕ =>
          movingRightEdgeExceptionalCluster H tau (m : ℝ))
        hsub
        (by simpa [H] using hseedNeg)
        (by simpa [H] using hnew)
  have hamplitude :
      ∀ᶠ m : ℕ in atTop,
        0 <
          (c - loss) *
            targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards
        [eventually_naturalPoint_pos_of_eventually_pos
          (targetZeroPowerAmplitude_eventually_pos beta)] with m hm
    exact mul_pos hnet hm
  have hclosed :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTClosedRealAxisRelativeTerm (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.const_mul_amplitude
      (c - loss)
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
        hbeta).naturalPoint
  have hcontour :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)) := by
    exact
      NaturalPointTargetAmplitudeNegligible.const_mul_amplitude
        (c - loss) (by simpa [H] using hremainder.negligible)
  have houtside :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          movingRightEdgeOutsideClusterPNTComplement
            H tau (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.const_mul_amplitude
      (c - loss) hcomplement.naturalPoint
  have hsmall :=
    eventually_abs_naturalPoint_three_remainders_lt_half
      hamplitude hclosed hcontour houtside
  have happrox :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            movingRightEdgeVisibleClusterPNTMain H tau (m : ℝ)| <
          ((c - loss) / 2) *
            targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards [hsmall] with m hm
    rw [
      relativeChebyshevPsi0Error_eq_movingRightEdgeCluster_add_actualResiduals
        H tau (m : ℝ)]
    convert hm using 1 <;> ring
  have hpositive :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        (fun m : ℕ =>
          ((c - loss) * targetZeroPowerAmplitude beta (m : ℝ)) / 2) := by
    have htransfer :=
      hmainPos.transfer_eventually_sub_lt
        (f := fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        (loss := (c - loss) / 2) happrox
    convert htransfer using 1 <;> funext m <;> ring
  have hnegative :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        (fun m : ℕ =>
          ((c - loss) * targetZeroPowerAmplitude beta (m : ℝ)) / 2) := by
    have htransfer :=
      hmainNeg.transfer_eventually_sub_lt
        (f := fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        (loss := (c - loss) / 2) happrox
    convert htransfer using 1 <;> funext m <;> ring
  exact
    hasFarSignedTargetAmplitudeWitnesses_of_naturalPoint
      hpositive hnegative

/-- Fixed-parameter unified output: actual PNT convergence and the signed
coefficient-preserving moving-seed lower transfer. -/
theorem
    unified_automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalTargetTransfer
    {S₀ : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh c loss : ℝ}
    (hbeta : 0 < beta)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (htau : tau < beta)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh :
      alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHigh : 0 < gammaHigh)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hepsilonHigh : 0 < epsilonHigh)
    (hstripLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0)
    (hstripHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0)
    (hnet : 0 < c - loss)
    (hS₀ : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hseedPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection)
            S₀ (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hseedNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection)
            S₀ (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection)
            (movingRightEdgeExceptionalCluster
                (selectedUniformGoodHeight alpha selection)
                tau (m : ℝ) \ S₀)
            (m : ℝ)| <
          loss * targetZeroPowerAmplitude beta (m : ℝ)) :
    (∃ rate : ℝ,
        0 < rate ∧
        rate ≤ 1 ∧
        Tendsto
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          atTop (nhds 0)) ∧
      HasFarSignedTargetAmplitudeWitnesses
        relativeChebyshevPsi0Error
        (fun x =>
          ((c - loss) * targetZeroPowerAmplitude beta x) / 2) := by
  exact
    ⟨exists_fixedRate_relativeChebyshevPsi0Error_tendsto,
      automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalPointLowerTransfer
        hbeta halphaOne hcontourMargin selection
        hsigma hsigmaOne htau halpha hgammaLow hepsilonLow
        hlowLow hlowHigh hgammaHigh hgammaHighAlpha
        hepsilonHigh hstripLow hstripHigh
        hnet hS₀ hseedPos hseedNeg hnew⟩

/-- From `2 / 3 < beta < 1`, automatically select all two-height parameters
for the signed coefficient-preserving finite-seed transfer. -/
theorem
    exists_automaticGoodHeight_movingRightEdgeSignedSeedNaturalTargetTransfer
    {S₀ : Finset ℂ} {beta c loss : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hnet : 0 < c - loss)
    (hS₀ : IsTargetRealPartNontrivialZeroSeed beta S₀) :
    ∃ sigma tau alpha : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      1 / 2 < tau ∧
      tau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        HasFarNaturalPointPositiveTargetAmplitudeWitness
            (fun m : ℕ =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection)
                S₀ (m : ℝ))
            (fun m : ℕ =>
              c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
            (fun m : ℕ =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection)
                S₀ (m : ℝ))
            (fun m : ℕ =>
              c * targetZeroPowerAmplitude beta (m : ℝ)) →
        (∀ᶠ m : ℕ in atTop,
          |dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight alpha selection)
              (movingRightEdgeExceptionalCluster
                  (selectedUniformGoodHeight alpha selection)
                  tau (m : ℝ) \ S₀)
              (m : ℝ)| <
            loss * targetZeroPowerAmplitude beta (m : ℝ)) →
        (∃ rate : ℝ,
            0 < rate ∧
            rate ≤ 1 ∧
            Tendsto
              (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (nhds 0)) ∧
          HasFarSignedTargetAmplitudeWitnesses
            relativeChebyshevPsi0Error
            (fun x =>
              ((c - loss) *
                targetZeroPowerAmplitude beta x) / 2) := by
  have hanchor :
      (1 / 2 : ℝ) < (3 * beta - 1) / 2 := by
    linarith
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters_above_cap
        hbeta hbetaOne hanchor with
    ⟨sigma, tau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, hanchorTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  have hbetaPos : 0 < beta := by
    linarith
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hanchorTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hseedPos hseedNeg hnew
  exact
    unified_automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalTargetTransfer
      hbetaPos halphaOne hcontour selection
      hsigmaHalf hsigmaOne htauBeta halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le
      hepsilonHigh hstripLow hstripHigh
      hnet hS₀ hseedPos hseedNeg hnew

end PrimeNumberTheorem
