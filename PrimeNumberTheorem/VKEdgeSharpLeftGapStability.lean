import PrimeNumberTheorem.VKEdgeSharpLowHeightEnergy
import PrimeNumberTheorem.VKEdgeSharpLeftGapDecay

open Complex Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Cofinal Sharp energy after strictly-left finite deletions

The genuine `S = empty` low-height energy lower bound remains positive after
deleting a fixed finite family separated by a positive real-part gap from the
target zero.  The family and gap affect only the eventual starting point, not
the retained fraction of the original energy constant.
-/

private theorem tendsto_exp_gamma_mul_log_atTop
    {gamma : ℝ} (hgamma : 0 < gamma) :
    Tendsto (fun Y : ℝ => Real.exp (gamma * Real.log Y))
      atTop atTop := by
  exact Real.tendsto_exp_atTop.comp
    (Real.tendsto_log_atTop.const_mul_atTop hgamma)

private theorem eventually_fixedNontrivialZeroSet_subset_powerHeight
    (S : Finset ℂ)
    {gamma : ℝ}
    (hgamma : 0 < gamma)
    (hSzero : ∀ z ∈ S, RiemannHypothesis.IsNontrivialZero z) :
    ∀ᶠ Y : ℝ in atTop,
      ∀ T : ℝ, Real.exp (gamma * Real.log Y) ≤ T →
        S ⊆ nontrivialZerosFinset T := by
  have hheight :
      ∀ᶠ Y : ℝ in atTop,
        ∀ z ∈ S, |z.im| ≤ Real.exp (gamma * Real.log Y) :=
    S.eventually_all.mpr fun z hz =>
      (tendsto_atTop.1 (tendsto_exp_gamma_mul_log_atTop hgamma) |z.im|)
  filter_upwards [hheight] with Y hheightY
  intro T hT z hz
  apply mem_nontrivialZerosFinset.mpr
  exact ⟨hSzero z hz, (hheightY z hz).trans hT⟩

private theorem tendsto_leftGapSelectedEnergyEnvelope
    (S : Finset ℂ) {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto
      (fun Y : ℝ =>
        (Real.exp (-delta * Real.log Y) *
          finiteZeroClusterReciprocalMultiplicityMass
            S (analyticOrderNatAt riemannZeta)) ^ 2)
      atTop (nhds 0) := by
  have hlinear :
      Tendsto (fun Y : ℝ => delta * Real.log Y) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hdelta
  have hexp :
      Tendsto (fun Y : ℝ => Real.exp (-delta * Real.log Y))
        atTop (nhds 0) := by
    simpa only [neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
  have hmul :
      Tendsto
        (fun Y : ℝ =>
          Real.exp (-delta * Real.log Y) *
            finiteZeroClusterReciprocalMultiplicityMass
              S (analyticOrderNatAt riemannZeta))
        atTop (nhds 0) := by
    simpa using
      hexp.mul_const
        (finiteZeroClusterReciprocalMultiplicityMass
          S (analyticOrderNatAt riemannZeta))
  simpa using hmul.pow 2

/-- A genuine off-line zero with real part greater than `2 / 3` retains a
cofinal positive low-height Gaussian energy after deleting any fixed finite
family of actual nontrivial zeros lying at least `delta > 0` to its left.

The retained constant is one quarter of the original true-zeta `S = empty`
constant and is independent of the deleted set.  The eventual threshold may
depend on the set and the gap.  This theorem does not delete the anchor pair
or any zero on the same real-part layer. -/
theorem
    exists_eventually_leftGapFiniteSetLowHeightNormalizedComplementSecondMoment_gt
    {ε : ℝ} {rho : ℂ} {sigma gammaLow alpha delta : ℝ}
    (S : Finset ℂ)
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoTwoThirds : 2 / 3 < rho.re)
    (hrhoRe1 : rho.re < 1)
    (hgammaLow : 0 < gammaLow)
    (hgammaLowBeta : gammaLow < rho.re)
    (hdecay : (1 - rho.re) * (1 + ε) < gammaLow)
    (hgammaLowAlpha : gammaLow < alpha)
    (halpha1 : alpha ≤ 1)
    (hdelta : 0 < delta)
    (hSzero : ∀ z ∈ S, RiemannHypothesis.IsNontrivialZero z)
    (hSgap : ∀ z ∈ S, z.re ≤ rho.re - delta) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < initialEmptyClusterFullMovingGaussianL2Constant ε rho k ∧
      ∀ᶠ Y : ℝ in atTop,
        ∃ Tlow ∈
            Set.Icc
              (Real.exp (gammaLow * Real.log Y))
              (Real.exp (gammaLow * Real.log Y) + 1),
          ExplicitFormulaAux.goodHeight Tlow ∧
            Tlow ≤ Real.exp (alpha * Real.log Y) ∧
            initialEmptyClusterFullMovingGaussianL2Constant ε rho k / 4 <
              ∫ t : ℝ in Set.Icc 0 (ε * Real.log Y),
                normalizedGaussian ((ε * Real.log Y) ^ 2) t *
                  ‖normalizedFiniteZeroClusterComplementContribution
                    S Tlow rho.re (Real.log Y + t)‖ ^ 2 := by
  rcases
      exists_eventually_emptyClusterLowHeightNormalizedComplementSecondMoment_gt
        hε hgamma hzero hσ hσrho hrhoTwoThirds hrhoRe1 hgammaLow
          hgammaLowBeta hdecay hgammaLowAlpha halpha1 with
    ⟨k, hmissing, hconstant, hempty⟩
  let C : ℝ := initialEmptyClusterFullMovingGaussianL2Constant ε rho k
  have hC : 0 < C := by
    dsimp [C]
    exact hconstant
  have hsmallLt :
      ∀ᶠ Y : ℝ in atTop,
        (Real.exp (-delta * Real.log Y) *
          finiteZeroClusterReciprocalMultiplicityMass
            S (analyticOrderNatAt riemannZeta)) ^ 2 < C / 4 :=
    (tendsto_order.1
      (tendsto_leftGapSelectedEnergyEnvelope S hdelta)).2
        (C / 4) (div_pos hC (by norm_num))
  have hsmall :
      ∀ᶠ Y : ℝ in atTop,
        (Real.exp (-delta * Real.log Y) *
          finiteZeroClusterReciprocalMultiplicityMass
            S (analyticOrderNatAt riemannZeta)) ^ 2 ≤ C / 4 :=
    hsmallLt.mono fun _ h => h.le
  have hsubset :=
    eventually_fixedNontrivialZeroSet_subset_powerHeight
      S hgammaLow hSzero
  have hYtwo : ∀ᶠ Y : ℝ in atTop, 2 ≤ Y := eventually_ge_atTop 2
  refine ⟨k, hmissing, hconstant, ?_⟩
  filter_upwards [hempty, hsmall, hsubset, hYtwo] with
      Y hemptyY hsmallY hsubsetY hY
  rcases hemptyY with ⟨Tlow, hTlow, hgood, houter, hfull⟩
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have ha : 0 ≤ Real.log Y := hlogY.le
  have hL : 0 ≤ ε * Real.log Y := (mul_pos hε hlogY).le
  have hm : 0 < (ε * Real.log Y) ^ 2 :=
    sq_pos_of_pos (mul_pos hε hlogY)
  have hSTlow : S ⊆ nontrivialZerosFinset Tlow :=
    hsubsetY Tlow hTlow.1
  refine ⟨Tlow, hTlow, hgood, houter, ?_⟩
  exact
    normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment_gt_quarter_of_leftGap
      hSTlow hdelta.le ha hm hL hSgap hfull
        (by simpa [C] using hsmallY)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
