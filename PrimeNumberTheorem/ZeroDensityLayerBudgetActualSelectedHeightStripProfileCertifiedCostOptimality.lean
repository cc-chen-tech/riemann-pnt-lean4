import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileCertifiedFiniteGridTransfer

/-!
# Certified strip-profile cost optimality

The certified finite-grid optimizer maximizes `optimalRobustMargin`.  This
module records the exact extra hypothesis needed to interpret that order as
optimality for an explicit analytic cost: the cost must be antitone in the
robust margin.

The concrete cost `x ^ (-δ)` satisfies this condition for `1 ≤ x`.  Thus a
profile selected by the existing certificate-aware optimizer minimizes the
corresponding pointwise robust-decay factor among every certified competitor.
This is an optimality statement for the certified comparison class, not a
claim that the full explicit-formula cost is automatically antitone.
-/

namespace PrimeNumberTheorem

open scoped Real

namespace ActualSelectedHeightFiniteStripProfile

/-- A profile cost is antitone in the robust margin when a larger certified
margin never increases the cost. -/
def RobustMarginAntitoneCost
    (beta : ℝ)
    (cost : ActualSelectedHeightFiniteStripProfile → ℝ) : Prop :=
  ∀ profile candidate,
    profile.optimalRobustMargin beta ≤ candidate.optimalRobustMargin beta →
      cost candidate ≤ cost profile

/-- The pointwise decay factor associated with a profile's robust margin. -/
noncomputable def robustDecayFactor
    (profile : ActualSelectedHeightFiniteStripProfile)
    (beta x : ℝ) : ℝ :=
  x ^ (-profile.optimalRobustMargin beta)

theorem robustDecayFactor_le_of_optimalRobustMargin_le
    {beta x : ℝ}
    {profile candidate : ActualSelectedHeightFiniteStripProfile}
    (hx : 1 ≤ x)
    (hmargin :
      profile.optimalRobustMargin beta ≤ candidate.optimalRobustMargin beta) :
    candidate.robustDecayFactor beta x ≤ profile.robustDecayFactor beta x := by
  unfold robustDecayFactor
  exact Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hmargin)

theorem robustDecayFactor_robustMarginAntitoneCost
    {beta x : ℝ}
    (hx : 1 ≤ x) :
    RobustMarginAntitoneCost beta (fun profile => profile.robustDecayFactor beta x) := by
  intro profile candidate hmargin
  exact robustDecayFactor_le_of_optimalRobustMargin_le hx hmargin

theorem RobustMarginAntitoneCost.const
    {beta constant : ℝ} :
    RobustMarginAntitoneCost beta (fun _ => constant) := by
  intro profile candidate hmargin
  exact le_rfl

theorem RobustMarginAntitoneCost.nonneg_const_mul
    {beta weight : ℝ}
    {cost : ActualSelectedHeightFiniteStripProfile → ℝ}
    (hweight : 0 ≤ weight)
    (hcost : RobustMarginAntitoneCost beta cost) :
    RobustMarginAntitoneCost beta (fun profile => weight * cost profile) := by
  intro profile candidate hmargin
  exact mul_le_mul_of_nonneg_left (hcost profile candidate hmargin) hweight

theorem RobustMarginAntitoneCost.add
    {beta : ℝ}
    {cost₁ cost₂ : ActualSelectedHeightFiniteStripProfile → ℝ}
    (hcost₁ : RobustMarginAntitoneCost beta cost₁)
    (hcost₂ : RobustMarginAntitoneCost beta cost₂) :
    RobustMarginAntitoneCost beta (fun profile => cost₁ profile + cost₂ profile) := by
  intro profile candidate hmargin
  exact add_le_add
    (hcost₁ profile candidate hmargin)
    (hcost₂ profile candidate hmargin)

/-- A two-part explicit-formula envelope: a profile-dependent robust decay
factor with a nonnegative coefficient, plus a profile-independent residual. -/
noncomputable def weightedRobustDecayEnvelope
    (profile : ActualSelectedHeightFiniteStripProfile)
    (beta x weight residual : ℝ) : ℝ :=
  weight * profile.robustDecayFactor beta x + residual

theorem weightedRobustDecayEnvelope_robustMarginAntitoneCost
    {beta x weight residual : ℝ}
    (hx : 1 ≤ x)
    (hweight : 0 ≤ weight) :
    RobustMarginAntitoneCost beta
      (fun profile =>
        profile.weightedRobustDecayEnvelope beta x weight residual) := by
  exact
    (robustDecayFactor_robustMarginAntitoneCost hx).nonneg_const_mul hweight
      |>.add RobustMarginAntitoneCost.const

/-- Any certified-family optimizer for the robust margin minimizes every cost
whose dependence on that margin is antitone. -/
theorem optimalRobustMargin_minimizes_antitoneCost
    {beta : ℝ}
    {selection : UniformNaturalPointGoodHeightSelection}
    {S : Finset ℂ}
    {candidates : Finset ActualSelectedHeightFiniteStripProfile}
    {chosen : ActualSelectedHeightFiniteStripProfile}
    {cost : ActualSelectedHeightFiniteStripProfile → ℝ}
    (hoptimal :
      ∀ profile ∈ candidates,
        profile.HasAnalyticTransferCertificate beta selection S →
          profile.optimalRobustMargin beta ≤ chosen.optimalRobustMargin beta)
    (hcost : RobustMarginAntitoneCost beta cost) :
    ∀ profile ∈ candidates,
      profile.HasAnalyticTransferCertificate beta selection S →
        cost chosen ≤ cost profile := by
  intro profile hprofile hcertificate
  exact hcost profile chosen (hoptimal profile hprofile hcertificate)

/-- In particular, the certified robust-margin optimizer minimizes the
pointwise factor `x ^ (-δ)` for every `x ≥ 1`. -/
theorem optimalRobustMargin_minimizes_robustDecayFactor
    {beta x : ℝ}
    {selection : UniformNaturalPointGoodHeightSelection}
    {S : Finset ℂ}
    {candidates : Finset ActualSelectedHeightFiniteStripProfile}
    {chosen : ActualSelectedHeightFiniteStripProfile}
    (hx : 1 ≤ x)
    (hoptimal :
      ∀ profile ∈ candidates,
        profile.HasAnalyticTransferCertificate beta selection S →
          profile.optimalRobustMargin beta ≤ chosen.optimalRobustMargin beta) :
    ∀ profile ∈ candidates,
      profile.HasAnalyticTransferCertificate beta selection S →
        chosen.robustDecayFactor beta x ≤ profile.robustDecayFactor beta x := by
  exact optimalRobustMargin_minimizes_antitoneCost hoptimal
    (robustDecayFactor_robustMarginAntitoneCost hx)

/-- The certified robust-margin optimizer minimizes every envelope of the form
`A(x) * x ^ (-δ) + R(x)` when `A(x)` is nonnegative and `R(x)` is independent
of the profile. -/
theorem optimalRobustMargin_minimizes_weightedRobustDecayEnvelope
    {beta x weight residual : ℝ}
    {selection : UniformNaturalPointGoodHeightSelection}
    {S : Finset ℂ}
    {candidates : Finset ActualSelectedHeightFiniteStripProfile}
    {chosen : ActualSelectedHeightFiniteStripProfile}
    (hx : 1 ≤ x)
    (hweight : 0 ≤ weight)
    (hoptimal :
      ∀ profile ∈ candidates,
        profile.HasAnalyticTransferCertificate beta selection S →
          profile.optimalRobustMargin beta ≤ chosen.optimalRobustMargin beta) :
    ∀ profile ∈ candidates,
      profile.HasAnalyticTransferCertificate beta selection S →
        chosen.weightedRobustDecayEnvelope beta x weight residual ≤
          profile.weightedRobustDecayEnvelope beta x weight residual := by
  exact optimalRobustMargin_minimizes_antitoneCost hoptimal
    (weightedRobustDecayEnvelope_robustMarginAntitoneCost hx hweight)

/-- If an actual explicit-formula cost is bounded by the robust envelope for
the selected profile, then it is bounded by the corresponding envelope of
every certified competitor.  This deliberately does not assert that the
actual costs of two profiles are ordered. -/
theorem optimalRobustMargin_bounds_costBy_competitorEnvelope
    {beta x weight residual : ℝ}
    {selection : UniformNaturalPointGoodHeightSelection}
    {S : Finset ℂ}
    {candidates : Finset ActualSelectedHeightFiniteStripProfile}
    {chosen : ActualSelectedHeightFiniteStripProfile}
    {actualCost : ActualSelectedHeightFiniteStripProfile → ℝ}
    (hx : 1 ≤ x)
    (hweight : 0 ≤ weight)
    (hoptimal :
      ∀ profile ∈ candidates,
        profile.HasAnalyticTransferCertificate beta selection S →
          profile.optimalRobustMargin beta ≤ chosen.optimalRobustMargin beta)
    (hchosenMajorant :
      actualCost chosen ≤
        chosen.weightedRobustDecayEnvelope beta x weight residual) :
    ∀ profile ∈ candidates,
      profile.HasAnalyticTransferCertificate beta selection S →
        actualCost chosen ≤
          profile.weightedRobustDecayEnvelope beta x weight residual := by
  intro profile hprofile hcertificate
  exact hchosenMajorant.trans
    (optimalRobustMargin_minimizes_weightedRobustDecayEnvelope
      hx hweight hoptimal profile hprofile hcertificate)

end ActualSelectedHeightFiniteStripProfile

end PrimeNumberTheorem
