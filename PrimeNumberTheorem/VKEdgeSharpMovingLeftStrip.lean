import PrimeNumberTheorem.VKEdgeSharpLowHeightEnergy
import PrimeNumberTheorem.VKEdgeSharpLeftGapDecay

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Sharp energy after deleting the moving left strip

At detector height `T`, remove every actual nontrivial zeta zero with real
part at most `sigma`.  Their reciprocal multiplicity mass is bounded by the
global `O(log^2 T)` zero mass.  After normalization at an off-line zero with
real part `beta > sigma`, the resulting Gaussian energy decays exponentially
in the logarithmic center, uniformly for the low power-height detector.

This module does not remove the anchor layer or any zero to its right.  It is
therefore a genuine moving-package extension of the fixed left-gap theorem,
not an arbitrary-exclusion or repeatable-growth result.
-/

/-- Actual nontrivial zeta zeros up to height `T` lying in the closed left
half-strip `Re rho <= sigma`. -/
noncomputable def leftStripNontrivialZerosFinset
    (sigma T : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset T).filter fun rho : ℂ => rho.re ≤ sigma

private theorem leftStripNontrivialZerosFinset_subset
    (sigma T : ℝ) :
    leftStripNontrivialZerosFinset sigma T ⊆ nontrivialZerosFinset T := by
  intro rho hrho
  exact (Finset.mem_filter.mp hrho).1

private theorem leftStripNontrivialZerosFinset_re_le
    {sigma T : ℝ} {rho : ℂ}
    (hrho : rho ∈ leftStripNontrivialZerosFinset sigma T) :
    rho.re ≤ sigma :=
  (Finset.mem_filter.mp hrho).2

private theorem leftStripReciprocalMultiplicityMass_le_global
    (sigma T : ℝ) :
    finiteZeroClusterReciprocalMultiplicityMass
        (leftStripNontrivialZerosFinset sigma T)
        (analyticOrderNatAt riemannZeta) ≤
      ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  unfold finiteZeroClusterReciprocalMultiplicityMass
    ExplicitFormulaAux.globalReciprocalZeroMultiplicity
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (leftStripNontrivialZerosFinset_subset sigma T)
    (fun rho _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg rho))

private theorem tendsto_exp_neg_mul_const_mul_affine_sq_sq
    {delta A B gamma : ℝ} (hdelta : 0 < delta) :
    Tendsto
      (fun a : ℝ =>
        (Real.exp (-delta * a) * (A * (B + gamma * a) ^ 2)) ^ 2)
      atTop (nhds 0) := by
  have hpow (k : ℕ) :
      Tendsto (fun a : ℝ => Real.exp (-delta * a) * a ^ k)
        atTop (nhds 0) := by
    have hsmall :=
      isLittleO_exp_mul_rpow_of_lt (k : ℝ)
        (a := -delta) (b := 0) (by linarith)
    have hratio := hsmall.tendsto_div_nhds_zero
    simpa [Real.rpow_natCast] using hratio
  have h2 :
      Tendsto
        (fun a : ℝ =>
          (A * gamma ^ 2) * (Real.exp (-delta * a) * a ^ 2))
        atTop (nhds 0) := by
    simpa using (hpow 2).const_mul (A * gamma ^ 2)
  have h1 :
      Tendsto
        (fun a : ℝ =>
          (2 * A * B * gamma) * (Real.exp (-delta * a) * a))
        atTop (nhds 0) := by
    simpa using (hpow 1).const_mul (2 * A * B * gamma)
  have h0 :
      Tendsto
        (fun a : ℝ =>
          (A * B ^ 2) * Real.exp (-delta * a))
        atTop (nhds 0) := by
    simpa using (hpow 0).const_mul (A * B ^ 2)
  have hinner :
      Tendsto
        (fun a : ℝ =>
          Real.exp (-delta * a) * (A * (B + gamma * a) ^ 2))
        atTop (nhds 0) := by
    have hsum := (h2.add h1).add h0
    simp only [add_zero] at hsum
    convert hsum using 1
    funext a
    ring
  simpa using hinner.pow 2

private theorem eventually_powerHeight_leftStripEnergyEnvelope_lt
    {beta sigma gammaLow C0 : ℝ}
    (hgap : sigma < beta)
    (hgamma : 0 < gammaLow)
    (hC0 : 0 < C0) :
    ∀ᶠ a : ℝ in atTop,
      ∀ T ∈ Set.Icc
          (Real.exp (gammaLow * a))
          (Real.exp (gammaLow * a) + 1),
        (Real.exp (-(beta - sigma) * a) *
          finiteZeroClusterReciprocalMultiplicityMass
            (leftStripNontrivialZerosFinset sigma T)
            (analyticOrderNatAt riemannZeta)) ^ 2 < C0 / 4 := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq
      with ⟨C, hC, hglobal⟩
  let B : ℝ := 1 + Real.log 8
  have hdelta : 0 < beta - sigma := sub_pos.mpr hgap
  have hlimit :
      Tendsto
        (fun a : ℝ =>
          (Real.exp (-(beta - sigma) * a) *
            (C * (B + gammaLow * a) ^ 2)) ^ 2)
        atTop (nhds 0) :=
    tendsto_exp_neg_mul_const_mul_affine_sq_sq
      (delta := beta - sigma) hdelta
  have hsmall :
      ∀ᶠ a : ℝ in atTop,
        (Real.exp (-(beta - sigma) * a) *
          (C * (B + gammaLow * a) ^ 2)) ^ 2 < C0 / 4 :=
    (tendsto_order.1 hlimit).2 (C0 / 4) (div_pos hC0 (by norm_num))
  have ha : ∀ᶠ a : ℝ in atTop, 0 ≤ a := eventually_ge_atTop 0
  have hheight :
      ∀ᶠ a : ℝ in atTop, 4 ≤ Real.exp (gammaLow * a) := by
    have htend : Tendsto (fun a : ℝ => Real.exp (gammaLow * a)) atTop atTop :=
      Real.tendsto_exp_atTop.comp
        (by simpa [mul_comm] using tendsto_id.atTop_mul_const hgamma)
    exact (tendsto_atTop.1 htend 4)
  filter_upwards [hsmall, ha, hheight] with a hsmallA haA hheightA
  intro T hT
  have hTfour : 4 ≤ T := hheightA.trans hT.1
  have hexpOne : 1 ≤ Real.exp (gammaLow * a) :=
    Real.one_le_exp (mul_nonneg hgamma.le haA)
  have hTplus : T + 6 ≤ 8 * Real.exp (gammaLow * a) := by
    calc
      T + 6 ≤ Real.exp (gammaLow * a) + 7 := by linarith [hT.2]
      _ ≤ 8 * Real.exp (gammaLow * a) := by linarith
  have hTplusPos : 0 < T + 6 := by linarith
  have hrightPos : 0 < 8 * Real.exp (gammaLow * a) := by positivity
  have hlog :
      Real.log (T + 6) ≤ Real.log 8 + gammaLow * a := by
    calc
      Real.log (T + 6) ≤
          Real.log (8 * Real.exp (gammaLow * a)) :=
        Real.strictMonoOn_log.monotoneOn hTplusPos hrightPos hTplus
      _ = Real.log 8 + gammaLow * a := by
        rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
          (Real.exp_ne_zero _), Real.log_exp]
  have hleftNonneg : 0 ≤ 1 + Real.log (T + 6) := by
    have hlogNonneg : 0 ≤ Real.log (T + 6) :=
      Real.log_nonneg (by linarith)
    linarith
  have hrightNonneg : 0 ≤ B + gammaLow * a := by
    dsimp [B]
    have hlogEight : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    positivity
  have hlogSq :
      (1 + Real.log (T + 6)) ^ 2 ≤ (B + gammaLow * a) ^ 2 := by
    apply pow_le_pow_left₀ hleftNonneg
    dsimp [B]
    linarith
  have hmass :
      finiteZeroClusterReciprocalMultiplicityMass
          (leftStripNontrivialZerosFinset sigma T)
          (analyticOrderNatAt riemannZeta) ≤
        C * (B + gammaLow * a) ^ 2 := by
    calc
      finiteZeroClusterReciprocalMultiplicityMass
          (leftStripNontrivialZerosFinset sigma T)
          (analyticOrderNatAt riemannZeta) ≤
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
        leftStripReciprocalMultiplicityMass_le_global sigma T
      _ ≤ C * (1 + Real.log (T + 6)) ^ 2 := hglobal T hTfour
      _ ≤ C * (B + gammaLow * a) ^ 2 :=
        mul_le_mul_of_nonneg_left hlogSq hC
  have hscaled :
      Real.exp (-(beta - sigma) * a) *
          finiteZeroClusterReciprocalMultiplicityMass
            (leftStripNontrivialZerosFinset sigma T)
            (analyticOrderNatAt riemannZeta) ≤
        Real.exp (-(beta - sigma) * a) *
          (C * (B + gammaLow * a) ^ 2) :=
    mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)
  exact (pow_le_pow_left₀
    (mul_nonneg (Real.exp_nonneg _)
      (finiteZeroClusterReciprocalMultiplicityMass_nonneg _ _))
    hscaled 2).trans_lt hsmallA

/-- A genuine off-line zero with real part greater than `2 / 3` retains a
cofinal positive low-height Gaussian energy after deleting every actual zero
up to the selected height whose real part is at most `sigma`.

Unlike the fixed-finset theorem, the deleted package grows with `Tlow`.  The
retained one-quarter constant is still independent of the package because the
global reciprocal zero mass grows only logarithmically while the fixed
real-part gap `rho.re - sigma` supplies exponential decay.  Zeros on the
anchor layer and to its right are not deleted. -/
theorem
    exists_eventually_leftStripLowHeightNormalizedComplementSecondMoment_gt
    {ε : ℝ} {rho : ℂ} {sigma gammaLow alpha : ℝ}
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
    (halpha1 : alpha ≤ 1) :
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
                    (leftStripNontrivialZerosFinset sigma Tlow)
                    Tlow rho.re (Real.log Y + t)‖ ^ 2 := by
  rcases
      exists_eventually_emptyClusterLowHeightNormalizedComplementSecondMoment_gt
        hε hgamma hzero hσ hσrho hrhoTwoThirds hrhoRe1 hgammaLow
          hgammaLowBeta hdecay hgammaLowAlpha halpha1 with
    ⟨k, hmissing, hconstant, hempty⟩
  let C0 : ℝ := initialEmptyClusterFullMovingGaussianL2Constant ε rho k
  have hC0 : 0 < C0 := by
    dsimp [C0]
    exact hconstant
  have hsmallA :=
    eventually_powerHeight_leftStripEnergyEnvelope_lt
      (beta := rho.re) (sigma := sigma) (gammaLow := gammaLow)
      (C0 := C0) hσrho hgammaLow hC0
  have hsmallY :
      ∀ᶠ Y : ℝ in atTop,
        ∀ T ∈ Set.Icc
            (Real.exp (gammaLow * Real.log Y))
            (Real.exp (gammaLow * Real.log Y) + 1),
          (Real.exp (-(rho.re - sigma) * Real.log Y) *
            finiteZeroClusterReciprocalMultiplicityMass
              (leftStripNontrivialZerosFinset sigma T)
              (analyticOrderNatAt riemannZeta)) ^ 2 < C0 / 4 :=
    Real.tendsto_log_atTop.eventually hsmallA
  have hYtwo : ∀ᶠ Y : ℝ in atTop, 2 ≤ Y := eventually_ge_atTop 2
  refine ⟨k, hmissing, hconstant, ?_⟩
  filter_upwards [hempty, hsmallY, hYtwo] with Y hemptyY hsmallY' hY
  rcases hemptyY with ⟨Tlow, hTlow, hgood, houter, hfull⟩
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have ha : 0 ≤ Real.log Y := hlogY.le
  have hL : 0 ≤ ε * Real.log Y := (mul_pos hε hlogY).le
  have hm : 0 < (ε * Real.log Y) ^ 2 :=
    sq_pos_of_pos (mul_pos hε hlogY)
  let S : Finset ℂ := leftStripNontrivialZerosFinset sigma Tlow
  have hsubset : S ⊆ nontrivialZerosFinset Tlow := by
    exact leftStripNontrivialZerosFinset_subset sigma Tlow
  have hgap : ∀ z ∈ S, z.re ≤ rho.re - (rho.re - sigma) := by
    intro z hz
    have hzSigma := leftStripNontrivialZerosFinset_re_le hz
    simpa only [sub_sub_cancel] using hzSigma
  have hsmall :
      (Real.exp (-(rho.re - sigma) * Real.log Y) *
          finiteZeroClusterReciprocalMultiplicityMass
            S (analyticOrderNatAt riemannZeta)) ^ 2 ≤ C0 / 4 := by
    exact (hsmallY' Tlow hTlow).le
  refine ⟨Tlow, hTlow, hgood, houter, ?_⟩
  exact
    normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment_gt_quarter_of_leftGap
      hsubset (sub_nonneg.mpr hσrho.le) ha hm hL hgap hfull
        (by simpa [C0, S] using hsmall)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
