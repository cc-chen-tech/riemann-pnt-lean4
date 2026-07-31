import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap

/-!
# Fixed Carlson geometry cannot close a genuine shrinking gap

This module concerns the standard power envelope used to prove a Carlson mass
upper bound.  Non-decay of that envelope is not a lower bound for the actual
zero mass.
-/

namespace PrimeNumberTheorem

open Filter Real
open scoped Topology

/-- The power envelope left after a fixed density penalty `p` is compared with
a target line `beta` and a moving outside cap. -/
noncomputable def shrinkingGapPowerEnvelope
    (p beta : ℝ) (capTau : ℝ → ℝ) (x : ℝ) : ℝ :=
  x ^ (p + capTau x - beta)

/-- A shrinking gap beats a density penalty exactly when its excess logarithmic
margin diverges. -/
theorem tendsto_shrinkingGapPowerEnvelope_zero_of_logMargin
    {p beta : ℝ} {capTau : ℝ → ℝ}
    (hmargin :
      Tendsto
        (fun x => ((beta - capTau x) - p) * Real.log x)
        atTop atTop) :
    Tendsto
      (shrinkingGapPowerEnvelope p beta capTau)
      atTop (nhds 0) := by
  have hneg :
      Tendsto
        (fun x => -(((beta - capTau x) - p) * Real.log x))
        atTop atBot :=
    tendsto_neg_atBot_iff.mpr hmargin
  have hexp :
      Tendsto
        (fun x => Real.exp
          (-(((beta - capTau x) - p) * Real.log x)))
        atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg
  apply hexp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [shrinkingGapPowerEnvelope, Real.rpow_def_of_pos hx]
  congr 1
  ring_nf

/-- If the density penalty is fixed and positive while the cap converges to
the target line, the associated power envelope cannot tend to zero. -/
theorem not_tendsto_shrinkingGapPowerEnvelope_zero_of_fixedPositivePenalty
    {p beta : ℝ} {capTau : ℝ → ℝ}
    (hp : 0 < p)
    (hcap : Tendsto capTau atTop (nhds beta)) :
    ¬ Tendsto
      (shrinkingGapPowerEnvelope p beta capTau)
      atTop (nhds 0) := by
  intro hzero
  have hexponent :
      Tendsto (fun x => p + capTau x - beta) atTop (nhds p) := by
    convert (tendsto_const_nhds.add hcap).sub tendsto_const_nhds using 1 <;>
      ring
  have hexponentNonneg :
      ∀ᶠ x in atTop, 0 ≤ p + capTau x - beta := by
    exact ((tendsto_order.1 hexponent).1 0 hp).mono fun _ hx => hx.le
  have hltOne :
      ∀ᶠ x in atTop, shrinkingGapPowerEnvelope p beta capTau x < 1 :=
    (tendsto_order.1 hzero).2 1 zero_lt_one
  have hgeOne :
      ∀ᶠ x in atTop, 1 ≤ shrinkingGapPowerEnvelope p beta capTau x := by
    filter_upwards
        [eventually_ge_atTop (1 : ℝ), hexponentNonneg] with
        x hx hpower
    exact Real.one_le_rpow hx hpower
  rcases (hgeOne.and hltOne).exists with ⟨x, hge, hlt⟩
  exact (not_lt_of_ge hge) hlt

/-- The low two-height Carlson density penalty is strictly positive for fixed
`1/2 < sigma < 1` and fixed positive inner-height exponent. -/
theorem fixedCarlsonLowPenalty_pos
    {sigma gamma : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hgamma : 0 < gamma) :
    0 < carlsonTwoHeightDensityExponent sigma * gamma := by
  unfold carlsonTwoHeightDensityExponent
  have hsigmaPos : 0 < sigma := by linarith
  have honeMinus : 0 < 1 - sigma := by linarith
  positivity

/-- The standard fixed-geometry Carlson low-budget power envelope cannot
certify decay for a cap converging to the target line. -/
theorem
    not_tendsto_fixedCarlsonLowPowerEnvelope_zero_of_cap_tendsto_target
    {beta sigma gamma : ℝ} {capTau : ℝ → ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hgamma : 0 < gamma)
    (hcap : Tendsto capTau atTop (nhds beta)) :
    ¬ Tendsto
      (shrinkingGapPowerEnvelope
        (carlsonTwoHeightDensityExponent sigma * gamma)
        beta capTau)
      atTop (nhds 0) :=
  not_tendsto_shrinkingGapPowerEnvelope_zero_of_fixedPositivePenalty
    (fixedCarlsonLowPenalty_pos hsigma hsigmaOne hgamma) hcap

end PrimeNumberTheorem
