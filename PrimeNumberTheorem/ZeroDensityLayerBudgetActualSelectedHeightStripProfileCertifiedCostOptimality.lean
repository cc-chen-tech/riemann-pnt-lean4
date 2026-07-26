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

end ActualSelectedHeightFiniteStripProfile

end PrimeNumberTheorem
