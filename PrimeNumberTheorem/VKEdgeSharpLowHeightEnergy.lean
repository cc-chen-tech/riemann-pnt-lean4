import PrimeNumberTheorem.ExplicitFormulaNormalizedPowerHeightWindowRemainder
import PrimeNumberTheorem.VKEdgeProportionalWindowTransfer

open Complex Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Genuine low-height Sharp energy

The detector height `Tlow` is selected at exponent `gammaLow`.  The separate
outer exponent `alpha` appears only in the eventual containment
`Tlow <= exp (alpha * a)`; it is not substituted for `gammaLow` in the
explicit-formula remainder estimate.
-/

/-- A selected unit interval at the lower power height eventually lies below
the independently specified outer power height. -/
theorem eventually_exp_gammaLow_mul_add_one_le_exp_alpha_mul
    {gammaLow alpha : ℝ}
    (hgamma : 0 < gammaLow)
    (hgammaAlpha : gammaLow < alpha) :
    ∀ᶠ a : ℝ in atTop,
      Real.exp (gammaLow * a) + 1 ≤ Real.exp (alpha * a) := by
  let gap : ℝ := alpha - gammaLow
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have ha0 : ∀ᶠ a : ℝ in atTop, 0 ≤ a := eventually_ge_atTop 0
  have haLog :
      ∀ᶠ a : ℝ in atTop, Real.log 2 / gap ≤ a :=
    eventually_ge_atTop (Real.log 2 / gap)
  filter_upwards [ha0, haLog] with a ha0A haLogA
  have hgammaA : 0 ≤ gammaLow * a := mul_nonneg hgamma.le ha0A
  have hone : 1 ≤ Real.exp (gammaLow * a) := Real.one_le_exp hgammaA
  have hlogTwo : Real.log 2 ≤ gap * a := by
    simpa [mul_comm] using (div_le_iff₀ hgap).mp haLogA
  have htwo : 2 ≤ Real.exp (gap * a) := by
    calc
      2 = Real.exp (Real.log 2) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
      _ ≤ Real.exp (gap * a) := Real.exp_le_exp.mpr hlogTwo
  calc
    Real.exp (gammaLow * a) + 1 ≤
        2 * Real.exp (gammaLow * a) := by linarith
    _ ≤ Real.exp (gammaLow * a) * Real.exp (gap * a) := by
      have hmul :=
        mul_le_mul_of_nonneg_left htwo (Real.exp_pos (gammaLow * a)).le
      simpa [mul_comm] using hmul
    _ = Real.exp (alpha * a) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [gap]
      ring

/-- The generalized genuine good-height remainder estimate transfers any
concrete residual lower bound to the full actual finite-zeta-zero complement
at the independently chosen low detector height. -/
theorem
    eventually_exists_goodHeight_normalizedRemainder_to_fullMovingGaussianEnergy_powerHeight_proportional
    {S : Finset ℂ} {beta gammaLow ε eta : ℝ}
    (hbeta : 1 / 2 < beta)
    (hbeta1 : beta < 1)
    (hgamma : 0 < gammaLow)
    (hgammaBeta : gammaLow < beta)
    (hdecay : (1 - beta) * (1 + ε) < gammaLow)
    (hε : 0 < ε)
    (heta : 0 < eta) :
    ∀ᶠ a : ℝ in atTop,
      ∃ Tlow ∈
          Set.Icc
            (Real.exp (gammaLow * a))
            (Real.exp (gammaLow * a) + 1),
        ExplicitFormulaAux.goodHeight Tlow ∧
          (1 / 3 : ℝ) *
                normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                  S Tlow beta a ((ε * a) ^ 2) (ε * a) -
              (eta ^ 2 +
                (Real.exp (-beta * a) *
                  zeroPackageClosedTermsUniformBound) ^ 2) ≤
            dynamicComplementForwardMovingGaussianSecondMoment
              S Tlow beta a (dynamicComplementFullBucketSet S Tlow)
                ((ε * a) ^ 2) (ε * a) := by
  have hselect :=
    ExplicitFormulaResidues.eventually_exists_uniform_goodHeight_normalized_powerHeight_proportional_window_remainder_lt
      hbeta hbeta1 hgamma hgammaBeta hdecay hε heta
  have haOne : ∀ᶠ a : ℝ in atTop, 1 ≤ a := eventually_ge_atTop 1
  filter_upwards [hselect, haOne] with a hselectA ha
  rcases hselectA with ⟨Tlow, hTmem, hgood, hpoint⟩
  refine ⟨Tlow, hTmem, hgood, ?_⟩
  apply
    dynamicComplementFullMovingGaussianSecondMoment_ge_of_normalizedRemainder
      (sq_pos_of_pos (mul_pos hε (zero_lt_one.trans_le ha)))
      (by linarith) ha heta.le
  · intro y hy
    rw [normalizedFiniteZeroClusterApproximationError, norm_mul]
    have hscalar :
        ‖((Real.exp (-beta * y) : ℝ) : ℂ)‖ =
          Real.exp (-beta * y) := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    rw [hscalar]
    have hy' : y ∈ Set.Icc a ((1 + ε) * a) := by
      constructor
      · exact hy.1
      · calc
          y ≤ a + ε * a := hy.2
          _ = (1 + ε) * a := by ring
    exact (hpoint y hy').le
  · exact le_rfl

private theorem tendsto_exp_neg_mul_lowHeightEnergy
    {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto (fun a : ℝ => Real.exp (-beta * a))
      atTop (nhds 0) := by
  have hlinear : Tendsto (fun a : ℝ => beta * a) atTop atTop := by
    simpa [mul_comm] using tendsto_id.atTop_mul_const hbeta
  simpa only [neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear

/-- One fixed off-line zeta zero with real part greater than `2 / 3` forces a
cofinal positive Gaussian energy lower bound in the genuine finite-zero
complement at a low detector height.  The low height is eventually below the
independent outer height `exp (alpha * log Y)`.

This is the first `S = empty` Sharp milestone.  It does not assert that the
same lower bound survives after the anchor zero pair is put into an exclusion
set. -/
theorem
    exists_eventually_emptyClusterLowHeightFullMovingGaussianSecondMoment_gt
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
    (_halpha1 : alpha ≤ 1) :
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
            initialEmptyClusterFullMovingGaussianL2Constant ε rho k <
              dynamicComplementForwardMovingGaussianSecondMoment
                ∅ Tlow rho.re (Real.log Y)
                  (dynamicComplementFullBucketSet ∅ Tlow)
                  ((ε * Real.log Y) ^ 2) (ε * Real.log Y) := by
  rcases
      exists_eventually_emptyClusterResidualForwardGaussianSecondMoment_gt
        hε hgamma hzero hσ hσrho hrhoRe1 with
    ⟨k, hmissing, hRpos, hresidual⟩
  let R : ℝ := initialEmptyClusterResidualGaussianL2Constant ε rho k
  let eta : ℝ := min 1 (R / 12)
  have hR : 0 < R := by
    dsimp [R]
    exact hRpos
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min zero_lt_one (div_pos hR (by norm_num))
  have hetaSq : eta ^ 2 ≤ R / 12 := by
    have hetaOne : eta ≤ 1 := min_le_left _ _
    have hetaR : eta ≤ R / 12 := min_le_right _ _
    nlinarith [heta.le]
  have hhalfTwoThirds : (1 / 2 : ℝ) < 2 / 3 := by norm_num
  have hbeta : 1 / 2 < rho.re :=
    hhalfTwoThirds.trans hrhoTwoThirds
  have htransferA :=
    eventually_exists_goodHeight_normalizedRemainder_to_fullMovingGaussianEnergy_powerHeight_proportional
      (S := (∅ : Finset ℂ)) hbeta hrhoRe1 hgammaLow hgammaLowBeta
      hdecay hε heta
  have htransferY :
      ∀ᶠ Y : ℝ in atTop,
        ∃ Tlow ∈
            Set.Icc
              (Real.exp (gammaLow * Real.log Y))
              (Real.exp (gammaLow * Real.log Y) + 1),
          ExplicitFormulaAux.goodHeight Tlow ∧
            (1 / 3 : ℝ) *
                  normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                    ∅ Tlow rho.re (Real.log Y)
                      ((ε * Real.log Y) ^ 2) (ε * Real.log Y) -
                (eta ^ 2 +
                  (Real.exp (-rho.re * Real.log Y) *
                    zeroPackageClosedTermsUniformBound) ^ 2) ≤
              dynamicComplementForwardMovingGaussianSecondMoment
                ∅ Tlow rho.re (Real.log Y)
                  (dynamicComplementFullBucketSet ∅ Tlow)
                  ((ε * Real.log Y) ^ 2) (ε * Real.log Y) :=
    Real.tendsto_log_atTop.eventually htransferA
  have houterA :=
    eventually_exp_gammaLow_mul_add_one_le_exp_alpha_mul
      hgammaLow hgammaLowAlpha
  have houterY :
      ∀ᶠ Y : ℝ in atTop,
        Real.exp (gammaLow * Real.log Y) + 1 ≤
          Real.exp (alpha * Real.log Y) :=
    Real.tendsto_log_atTop.eventually houterA
  have hclosed0 :
      Tendsto
        (fun a : ℝ =>
          (Real.exp (-rho.re * a) *
            zeroPackageClosedTermsUniformBound) ^ 2)
        atTop (nhds 0) := by
    have hexp :=
      tendsto_exp_neg_mul_lowHeightEnergy (show 0 < rho.re by linarith)
    have hmul :
        Tendsto
          (fun a : ℝ =>
            Real.exp (-rho.re * a) *
              zeroPackageClosedTermsUniformBound)
          atTop (nhds 0) := by
      simpa [mul_comm] using
        hexp.const_mul zeroPackageClosedTermsUniformBound
    simpa using hmul.pow 2
  have hclosedA :
      ∀ᶠ a : ℝ in atTop,
        (Real.exp (-rho.re * a) *
          zeroPackageClosedTermsUniformBound) ^ 2 < R / 12 :=
    (tendsto_order.1 hclosed0).2
      (R / 12) (div_pos hR (by norm_num))
  have hclosedY :
      ∀ᶠ Y : ℝ in atTop,
        (Real.exp (-rho.re * Real.log Y) *
          zeroPackageClosedTermsUniformBound) ^ 2 < R / 12 :=
    Real.tendsto_log_atTop.eventually hclosedA
  have hfullPos :
      0 < initialEmptyClusterFullMovingGaussianL2Constant ε rho k := by
    unfold initialEmptyClusterFullMovingGaussianL2Constant
    positivity
  refine ⟨k, hmissing, hfullPos, ?_⟩
  filter_upwards [hresidual, htransferY, houterY, hclosedY] with
      Y hresidualY htransferY' houterY' hclosedY'
  rcases htransferY' with ⟨Tlow, hTmem, hgood, henergy⟩
  refine ⟨Tlow, hTmem, hgood, hTmem.2.trans houterY', ?_⟩
  have hRlower :
      R <
        normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          ∅ Tlow rho.re (Real.log Y)
            ((ε * Real.log Y) ^ 2) (ε * Real.log Y) := by
    dsimp [R]
    exact hresidualY Tlow
  have hbudget :
      R / 6 <
        (1 / 3 : ℝ) *
              normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                ∅ Tlow rho.re (Real.log Y)
                  ((ε * Real.log Y) ^ 2) (ε * Real.log Y) -
            (eta ^ 2 +
              (Real.exp (-rho.re * Real.log Y) *
                zeroPackageClosedTermsUniformBound) ^ 2) := by
    nlinarith
  unfold initialEmptyClusterFullMovingGaussianL2Constant
  exact hbudget.trans_le henergy

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
