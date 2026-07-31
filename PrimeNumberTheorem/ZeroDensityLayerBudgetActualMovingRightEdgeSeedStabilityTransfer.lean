import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingRightEdgeUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterSeedExtension
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalPNTLowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicReverseZeroFree

/-!
# Actual PNT transfer from a fixed seed inside a moving right-edge cluster

A fixed finite target-line seed is eventually visible in every cofinal moving
right-edge cluster.  If the newly visible members cost at most `loss` on the
target scale, a seed witness with coefficient `c` therefore gives a moving
cluster witness with coefficient `c - loss`.  The Carlson and explicit-formula
transfer retains half of that coefficient in the actual PNT error.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A finite seed consisting of actual nontrivial zeros on the target
real-part line. -/
def IsTargetRealPartNontrivialZeroSeed
    (beta : ℝ) (S₀ : Finset ℂ) : Prop :=
  ∀ rho ∈ S₀,
    RiemannHypothesis.IsNontrivialZero rho ∧ rho.re = beta

/-- Pointwise visible-main decomposition for a natural-indexed moving finite
cluster family. -/
theorem dynamicVisibleClusterPNTMain_eq_seed_add_movingExtension
    (T : ℝ → ℝ) {S₀ : Finset ℂ} (S : ℕ → Finset ℂ)
    {m : ℕ}
    (hsub : ∀ rho ∈ S₀, rho ∈ S m) :
    dynamicVisibleClusterPNTMain T (S m) (m : ℝ) =
      dynamicVisibleClusterPNTMain T S₀ (m : ℝ) +
        dynamicVisibleClusterPNTMain T (S m \ S₀) (m : ℝ) :=
  dynamicVisibleClusterPNTMain_eq_seed_add_extension
    T hsub (m : ℝ)

/-- A fixed seed witness survives an eventually containing moving extension
with the exact coefficient loss assigned to the newly visible members. -/
theorem
    hasFarNaturalPointTargetAmplitudeWitness_movingVisibleCluster_of_seed
    (T : ℝ → ℝ) {S₀ : Finset ℂ} (S : ℕ → Finset ℂ)
    {amplitude : ℕ → ℝ} {c loss : ℝ}
    (hsub : ∀ᶠ m : ℕ in atTop, ∀ rho ∈ S₀, rho ∈ S m)
    (hseed :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain T S₀ (m : ℝ))
        (fun m => c * amplitude m))
    (hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain
            T (S m \ S₀) (m : ℝ)| <
          loss * amplitude m) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m =>
        dynamicVisibleClusterPNTMain T (S m) (m : ℝ))
      (fun m => (c - loss) * amplitude m) := by
  apply hseed.transfer_eventually_sub_lt
  filter_upwards [hsub, hnew] with m hsubM hnewM
  rw [dynamicVisibleClusterPNTMain_sub_seed_eq_extension
    T hsubM (m : ℝ)]
  exact hnewM

/-- A finite target-line seed is eventually contained in the moving
right-edge exceptional cluster along every cofinal height schedule. -/
theorem eventually_targetSeed_subset_movingRightEdgeExceptionalCluster
    {H : ℝ → ℝ} {beta tau : ℝ} {S₀ : Finset ℂ}
    (hH : Tendsto H atTop atTop)
    (htau : tau < beta)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀) :
    ∀ᶠ x : ℝ in atTop,
      ∀ rho ∈ S₀,
        rho ∈ movingRightEdgeExceptionalCluster H tau x := by
  classical
  induction S₀ using Finset.induction_on with
  | empty =>
      simp
  | @insert rho S hrho ih =>
      have hrhoData :
          RiemannHypothesis.IsNontrivialZero rho ∧ rho.re = beta :=
        hseed rho (by simp)
      have hseedS : IsTargetRealPartNontrivialZeroSeed beta S := by
        intro z hz
        exact hseed z (by simp [hz])
      have ihS := ih hseedS
      have hheight :
          ∀ᶠ x : ℝ in atTop, |rho.im| ≤ H x :=
        hH.eventually (eventually_ge_atTop |rho.im|)
      filter_upwards [ihS, hheight] with x hxS hxrho
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · unfold movingRightEdgeExceptionalCluster
        unfold actualCarlsonAdjoinRealOrdinateZeros
        apply Finset.mem_union_left
        apply mem_rightEdgeNontrivialZerosFinset.mpr
        exact
          ⟨hrhoData.1, hxrho,
            by rw [hrhoData.2]; exact htau.le⟩
      · exact hxS z hz

/-- Selected uniform good heights automatically make every finite target-line
seed eventually visible in the moving right-edge cluster. -/
theorem
    eventually_targetSeed_subset_selectedMovingRightEdgeExceptionalCluster
    {alpha beta tau : ℝ} {S₀ : Finset ℂ}
    (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (htau : tau < beta)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀) :
    ∀ᶠ m : ℕ in atTop,
      ∀ rho ∈ S₀,
        rho ∈
          movingRightEdgeExceptionalCluster
            (selectedUniformGoodHeight alpha selection)
            tau (m : ℝ) := by
  have hreal :=
    eventually_targetSeed_subset_movingRightEdgeExceptionalCluster
      (selectedUniformGoodHeight_tendsto_atTop halpha selection)
      htau hseed
  exact tendsto_natCast_atTop_atTop.eventually hreal

/-- Fixed-parameter coefficient-preserving lower transfer from a finite
target-line seed through the moving right-edge cluster to the actual PNT
error. -/
theorem
    automaticGoodHeight_twoHeight_movingRightEdgeSeedNaturalPointLowerTransfer
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
    (hseed :
      HasFarNaturalPointTargetAmplitudeWitness
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
    HasFarTargetAmplitudeWitness
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
  have hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          movingRightEdgeVisibleClusterPNTMain H tau (m : ℝ))
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ)) := by
    simpa [movingRightEdgeVisibleClusterPNTMain, H] using
      hasFarNaturalPointTargetAmplitudeWitness_movingVisibleCluster_of_seed
        H
        (fun m : ℕ =>
          movingRightEdgeExceptionalCluster H tau (m : ℝ))
        hsub
        (by simpa [H] using hseed)
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
  apply HasFarNaturalPointTargetAmplitudeWitness.toReal
  apply
    hasFarNaturalPointTargetAmplitudeWitness_of_three_remainders
      hamplitude hclosed hcontour houtside hmain
  intro m
  exact
    relativeChebyshevPsi0Error_eq_movingRightEdgeCluster_add_actualResiduals
      H tau (m : ℝ)

/-- Fixed-parameter unified output: actual PNT convergence and the
coefficient-preserving moving-seed lower transfer. -/
theorem
    unified_automaticGoodHeight_twoHeight_movingRightEdgeSeedNaturalTargetTransfer
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
    (hseed :
      HasFarNaturalPointTargetAmplitudeWitness
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
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x =>
          ((c - loss) * targetZeroPowerAmplitude beta x) / 2) := by
  exact
    ⟨exists_fixedRate_relativeChebyshevPsi0Error_tendsto,
      automaticGoodHeight_twoHeight_movingRightEdgeSeedNaturalPointLowerTransfer
        hbeta halphaOne hcontourMargin selection
        hsigma hsigmaOne htau halpha hgammaLow hepsilonLow
        hlowLow hlowHigh hgammaHigh hgammaHighAlpha
        hepsilonHigh hstripLow hstripHigh
        hnet hS₀ hseed hnew⟩

/-- From `2 / 3 < beta < 1`, automatically select all two-height parameters
for the coefficient-preserving transfer from a finite target-line seed. -/
theorem exists_automaticGoodHeight_movingRightEdgeSeedNaturalTargetTransfer
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
        HasFarNaturalPointTargetAmplitudeWitness
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
          HasFarTargetAmplitudeWitness
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
  intro selection hseed hnew
  exact
    unified_automaticGoodHeight_twoHeight_movingRightEdgeSeedNaturalTargetTransfer
      hbetaPos halphaOne hcontour selection
      hsigmaHalf hsigmaOne htauBeta halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le
      hepsilonHigh hstripLow hstripHigh
      hnet hS₀ hseed hnew

end PrimeNumberTheorem
